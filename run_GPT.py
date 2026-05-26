import json
import pickle
from openai import AzureOpenAI
import random
import time
import sys

field_summary_system_info = """\
You are a static program analyser to analyse java byte code in jimple representations. You will be given some sliced code snippets related to value assignments to a given field.
A JSON is given to you and organized in the format: {"field": {field_name}, "execTrace": {code_snippets}}.
Your task is to summarize the data stored in {field_name} by understanding the contextual information in {code_snippets}. For fields/contents information existing in priors, use them to assist the task. The data source should be <CONSTANT> with the observed constant value (e.g., {"payment method": ["<CONSTANT> Cash"]}), <FIELD> with the observed field (e.g., {"phone number": ["<FIELD> <bio.medico.patient.data.LocalData: java.lang.String phone_number>"]}), <FUNC> with the method invocation line (e.g., {"payment url": ["<FUNC> $r1.<bio.medico.patient.data.network.model.ResponseMetaInfo$MetaData: java.lang.String getPaymentUrl()>"]}), or <N/A> if there lacks sufficient information for summarization (e.g., {"user ID": ["<N/A>"]}).
Please answer in the JSON format: {"DATA_1": [DATA_SOURCE_1, DATA_SOURCE_2, ...], "DATA_2": ...}.\
"""
field_summary_example_user_prompt = """\
{"field": "<bio.medico.patient.data.network.model.PackageModel$PaymentMethord: java.lang.String p>", 
"execTrace":
"<trace>
$r6 = "Cash"
$r5 = $r0.<bio.medico.patient.data.LocalData: java.lang.String b>
<prior>
<bio.medico.patient.data.LocalData: java.lang.String b>: {"user ID": ["<N/A>"]}
</prior>
$r4 = staticinvoke <bio.medico.patient.data.network.model.ResponseMetaInfo$MetaData: java.lang.String getPaymentUrl()>()
$r3 = $r0.<bio.medico.patient.data.LocalData: java.lang.String phone_number>
virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r6)
virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5)
virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r4)
virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r3)
$r1 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>()
$r0.<bio.medico.patient.data.network.model.PackageModel$PaymentMethord: java.lang.String p> = $r1
</trace>"}\
"""
field_summary_example_assistant_response = """\
{"payment method": ["<CONSTANT> Cash"], "payment url": ["<FUNC> $r4 = staticinvoke <bio.medico.patient.data.network.model.ResponseMetaInfo$MetaData: java.lang.String getPaymentUrl()>()"], "user ID": ["<N/A>"], "phone number": ["<FIELD> <bio.medico.patient.data.LocalData: java.lang.String phone_number>"]}\
"""


DATA_summary_system_info = """\
You are a static program analyser to analyse java byte code in jimple representations. You will be given some sliced code snippets related to a data logging/tracking/sending behavior using analytic libraries.
A JSON is given to you and organized in the format: {"execTrace": {code_snippets}}.
Your task is to summarize the data sent by understanding the contextual information in {code_snippets}. For fields/contents information existing in priors, use them to assist the task. The data source should be <CONSTANT> with the observed constant value (e.g., {"payment method": ["<CONSTANT> Cash"]}), <FIELD> with the observed field (e.g., {"phone number": ["<FIELD> <bio.medico.patient.data.LocalData: java.lang.String phone_number>"]}), <FUNC> with the method invocation line (e.g., {"payment url": ["<FUNC> $r1.<bio.medico.patient.data.network.model.ResponseMetaInfo$MetaData: java.lang.String getPaymentUrl()>"]}), or <N/A> if there lacks sufficient information for summarization (e.g., {"user ID": ["<N/A>"]}). Record the observed in-app events or user's in-app events if there are any (e.g., {"in-app event": ["app crash", "click advertisement"]}).
Please answer in the JSON format: {"DATA_1": [DATA_SOURCE_1, DATA_SOURCE_2, ...], "DATA_2": ...}.\
"""

DATA_summary_example_user_prompt = """\
{"execTrace": 
"<trace>
$r1 = $r0.<bio.medico.patient.data.network.model.PackageModel$Methord: java.lang.String p>
<prior>
<bio.medico.patient.data.network.model.PackageModel$Methord: java.lang.String p>: {"method": ["Card", "Cash", "Mobile"]}
</prior>
$r2 = staticinvoke <bio.medico.patient.data.LocalData: java.lang.String getPhoneNumber()>()
$r4 = $r7.<android.content.SharedPreferences: java.lang.String getString(java.lang.String,java.lang.String)>("ap", null)
<prior>
<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putString(java.lang.String,java.lang.String)>("ap", $r2): {"appointment type": ["offline"]}
</prior>
$r3 = $r0.<bio.medico.patient.data.LocalData: java.lang.String patientId>
$r5 = new android.os.Bundle
specialinvoke $r5.<android.os.Bundle: void <init>()>()
virtualinvoke $r5.<android.os.Bundle: void putString(java.lang.String,java.lang.String)>("android", "patient")
virtualinvoke $r5.<android.os.Bundle: void putString(java.lang.String,java.lang.String)>("additional", $r1)
virtualinvoke $r5.<android.os.Bundle: void putString(java.lang.String,java.lang.String)>("contact", $r2)
virtualinvoke $r5.<android.os.Bundle: void putString(java.lang.String,java.lang.String)>("sex", $r6)
virtualinvoke $r5.<android.os.Bundle: void putString(java.lang.String,java.lang.String)>("appointment_type", $r4)
virtualinvoke $r5.<android.os.Bundle: void putString(java.lang.String,java.lang.String)>("patient", $r3)
$r5 = <bio.medico.patient.analytics.FirebaseAnalyticsManager: com.google.firebase.analytics.FirebaseAnalytics mFirebaseAnalytics>
virtualinvoke $r5.<com.google.firebase.analytics.FirebaseAnalytics: void logEvent(java.lang.String,android.os.Bundle)>("initiate_whatsapp", $r5)
</trace>"}\
"""

DATA_summary_example_assistant_response = """\
{"payment method": ["<CONSTANT> Card", "<CONSTANT> Cash", "<CONSTANT> Mobile"], "phone number": ["<FUNC> $r2 = staticinvoke <bio.medico.patient.data.LocalData: java.lang.String getPhoneNumber()>()"], "appointment type": ["<CONSTANT> offline"], "patient ID": ["<FIELD> <bio.medico.patient.data.LocalData: java.lang.String patientId>"], "sex": ["<N/A>"], "in-app event": ["initiate whatsapp"]}\
"""

condition_summary_system_info = """\
You are a static program analyser to analyse java byte code in jimple representations. You will be given some sliced code snippets related to the validation of a boolean predicate.
A JSON is given to you and organized in the format: {"condition": {boolean_expression}, "execTrace": {code_snippets}}.
Your task is to TRY YOUR BEST to comprehensively summarize the purpose of the {boolean_expression} by understanding the contextual information in {code_snippets}. For fields/contents information existing in priors, use them to assist the task. You can answer "N/A" if there lacks sufficient information for summarization.
Please answer in the JSON format: {"purpose": {code_purpose}}.\
"""

condition_summary_example_user_prompt = """\
{"condition": "$r4 == null", 
"execTrace":
"<trace>
$r1 := @parameter0: android.content.Context
$r3 := @parameter2: java.lang.String
staticinvoke <kotlin.jvm.internal.s: void h(java.lang.Object,java.lang.String)>($r1, "context")
staticinvoke <kotlin.jvm.internal.s: void h(java.lang.Object,java.lang.String)>($r3, "tracker_name")
$r4 = virtualinvoke $r0.<com.shaadi.android.utils.tracking.GoogleAnalyticsHelper$Companion: com.google.android.gms.analytics.Tracker getTracker(android.content.Context,java.lang.String)>($r1, $r3)
</trace>"}\
"""

condition_summary_example_assistant_response = """\
{"purpose": "Verify the tracker object is defined."}\
"""

data_categorization_system_info = """\
You are a security researcher to categorize some given data recognized in a mobile app. Your are required to classify each data into one of the given three categories:
PII: Personally identifiable information, which refers to information that can be used to distinguish or trace an individual’s identity or device;
NUI: Non-identifiable user information, which contains user-related information but cannot directly link to an identity;
Others: Other information apart from the above three.
You are given a list of data. Please classify all data, and answer in the JSON format: {"PII": [PII_1, PII_2,...], "NUI": [NUI_1, NUI_2,...], "Others": [Others_1, Others_2, ...]}\
"""


data_categorization_example_user_prompt = """\
{"data": ["user name", "geolocation", "phone number", "ad ID", "email", "search result", "AnalyticsObject", "Start button"]}\
"""

data_categorization_example_assistant_response = """\
{"PII": ["user name", "phone number", "ad ID", "email"], "NUI": ["geolocation", "search result"], "Others": ["AnalyticsObject"]}\
"""

context_summary_system_info = """\
You are a program analyst to summarize the contextual knowledge from a precondition execution path leading to a logging practice with some observed in-app events logged in an app. The information is given in the format: {"path": [ITEM_1, ITEM_2, ...], "in-app events": [EVENT_1, EVENT_2, ...]}. Items in the path are in the JSON formats of:
1. {"purpose": {purpose}, "satisfy": {True/False}}: {purpose} denotes the purpose of verifying an encountered condition statement, and whether or not (True/False) this condition should be satisfied.
2. {"function_invocation": {function_signature}}: {function_signature} denotes the invocation of a given function.
Your task is to summarize and infer when such event takes place in ONE_SENTENCE starting with "When" in the JSON format: {"summary" : {SUMMARY}}.
"""

context_summary_example_user_prompt = """\
{"path": [{"function_invocation": "bio.medico.patient.ui.call.CallActivity$12: void onClick(android.view.View)"}, {"purpose": "Verify whether the callManager object is not defined.", "satisfy": False}, {"function_invocation": "bio.medico.patient.analytics.FirebaseAnalyticsManager: void logEventWithNumber(java.lang.String,java.lang.String)"}, {"purpose": "Verify whether the patient has logged in.", "satisfy": True}], "in-app events": ["EVENT_CALL_END_CLICK", "select:private"]}
"""

context_summary_example_assistant_response = """\
{"summary": "When a logged-in patient clicks to end a private call."}
"""

AZURE_END_POINTS = [  # Replace with your own end points
            {
                'key': "<AZURE_KEYS>", 
                'base': "<AZURE_BASE>" 
            }

            ]



class conditionBlock:
    def __init__(self, TAG, trace, condition, isMthdInvoke) -> None:
        self.TAG = TAG
        self.trace = trace
        self.condition = condition
        self.isMthdInvoke = isMthdInvoke

    def getTrace(self):
        return [(t.instr, t.field) for t in self.trace]

class dependentNode:
    def __init__(self, TAG):
        self.TAG = TAG
        self.dependentNode = []
        self.solved = False

    def addDependent(self, node_tag):
        if node_tag not in self.dependentNode: self.dependentNode.insert(0, node_tag)

    def isSolved(self):
        return self.solved
    
    def hasSolved(self):
        self.solved = True

    def getTag(self):
        return self.TAG
    

def parse_one_js(data, target):
    if target == 'backward_result':
        data_for_one_startPoint = data['backward_result']
        
        startPoint = data_for_one_startPoint['startPoint']
        startPoint_tag = startPoint['method'] + "+" + str(startPoint['block']) + "+" + startPoint['stmt']
    
        allConditionChain[startPoint_tag] = []
        allDataTrace[startPoint_tag] = []

        conditionChain_for_one_startPoint = data_for_one_startPoint['conditionChains']
        dataTrace_for_one_startPoint = data_for_one_startPoint['DataTraces']

        tmp_zip = zip(conditionChain_for_one_startPoint, dataTrace_for_one_startPoint)

        data_node = dependentNode(startPoint_tag)
        allNodes[data_node.TAG] = data_node
        
        for __ in tmp_zip:
            cc = __[0]

            condition_chain = []
            for cb in cc:
                exec_trace = cb['execTrace']
                trace = []
                if cb['condition'] != 'null':
        
                    tag = exec_trace[-1]['method'] + "+" + str(exec_trace[-1]['block'])
                    condition_chain.append((tag, cb['satisfy']))
                    
                    if tag in allConditionBlocks.keys():
                        continue
                    
                    condition_node = dependentNode(tag)
                    allNodes[condition_node.TAG] = condition_node

                    condition = cb['condition']
                    
                    for _ in exec_trace[:-1]:
                        
                        field = None if 'field' not in _.keys() else _['field']
                        field = field if 'ICC' not in _.keys() else _['ICC']
                        # dt.append((item['stmt'], field))
                        if field != None:
                            field = field.replace('ICC_SP:', '').replace('ICC_INTENT:', '')
                            condition_node.addDependent(field)
                        item = (_['stmt'], field)
                        trace.append(item)

                    new_cb = conditionBlock(tag, trace, condition, False)
                    
                else:
                    tag = "[INVOKE]" + exec_trace[0]['method']
                    condition_chain.append((tag, cb['satisfy']))

                    if tag in allConditionBlocks.keys():
                        continue

                    item = (exec_trace[0]['method'], None)
                    trace.append(item)
                    new_cb = conditionBlock(tag, trace, None, True)


                allConditionBlocks[tag] = new_cb

            cur_mthd = __[1][0]['method']
            tag = "[INVOKE]" + cur_mthd
            condition_chain.append((tag, True))
            trace = []
            if tag not in allConditionBlocks.keys():
                item = (cur_mthd, None)
                trace.append(item)
                new_cb = conditionBlock(tag, trace, None, True)
                allConditionBlocks[tag] = new_cb
                # print("added: " + tag)

            allConditionChain[startPoint_tag].append(condition_chain)

        for data_trace in dataTrace_for_one_startPoint:
            dt = []
            for item in data_trace:
                field = None if 'field' not in item.keys() else item['field']
                field = field if 'ICC' not in item.keys() else item['ICC']
                instr = item['stmt']
                if field != None: 
                    field = field.replace('ICC_SP:', '').replace('ICC_INTENT:', '')
                    data_node.addDependent(field)
                    
                    if not (field.startswith('<') and field.endswith('>')):                  
                        param = instr[instr.rfind('(') + 1 : instr.rfind(',')]
                        instr = instr.replace(param, '"' + field + '"')

                dt.append((instr, field, item['block'], item['method']))

            allDataTrace[startPoint_tag].append(dt)
            

    if target == 'field_results':
        field_data = data['field_results']
        if 'Field' in field_data:
            field_name = field_data['Field']

        allFieldAndICCTraces[field_name] = []

        if 'Depend' not in field_data: return

        field_node = dependentNode(field_name)
        allNodes[field_node.TAG] = field_node

        for depends in field_data['Depend']:
            if 'ExecTrace' not in depends: continue
            for item in depends['ExecTrace']:
                trace = []
                for instr in item:
                    field = None if 'field' not in instr.keys() else instr['field']
                    field = field if 'ICC' not in instr.keys() else instr['ICC']
                    instrr = instr['stmt']
                    if field != None:
                        field = field.replace('ICC_SP:', '').replace('ICC_INTENT:', '')
                        field_node.addDependent(field)
                        
                        if not (field.startswith('<') and field.endswith('>')):                     
                            param = instrr[instrr.rfind('(') + 1 : instrr.rfind(',')]
                            instrr = instrr.replace(param, '"' + field + '"')
                            

                    trace.append((instrr, field, instr['block'], instr['method']))
                    # print(trace[-1])
                    
                allFieldAndICCTraces[field_name].append(trace)



def remove_duplicate_traces():  # remove duplicated data traces

    print("Removing duplicated traces ...")

    data_trace_count_before = 0
    data_trace_count_after = 0
    field_trace_count_before = 0
    field_trace_count_after = 0


    all_data_tags = [_ for _ in allDataTrace.keys()]

    for dataPoint_tag in all_data_tags:
        traces_for_one_dataPoint = allDataTrace.get(dataPoint_tag, [])
        condition_chain_for_one_dataPoint = allConditionChain.get(dataPoint_tag, [])
        if len(traces_for_one_dataPoint) == 0:
            allDataTrace.pop(dataPoint_tag)
            allConditionChain.pop(dataPoint_tag)
            continue
        
        data_trace_count_before += len(traces_for_one_dataPoint)

        idx = 0
        while idx < len(traces_for_one_dataPoint):
            l = len(traces_for_one_dataPoint)
            target_trace = traces_for_one_dataPoint[idx]

            for idx_cp in range(l - 1, idx, -1):
                if is_same_trace(target_trace, traces_for_one_dataPoint[idx_cp]):
                    traces_for_one_dataPoint.pop(idx_cp)
                    condition_chain_for_one_dataPoint.pop(idx_cp)
            idx += 1
        
        data_trace_count_after += len(traces_for_one_dataPoint)

    all_field_tags = [_ for _ in allFieldAndICCTraces.keys()]

    for field_tag in all_field_tags:
        traces_for_one_field = allFieldAndICCTraces.get(field_tag, [])
        if len(traces_for_one_field) == 0:
            allFieldAndICCTraces.pop(field_tag)
            continue
        
        field_trace_count_before += len(traces_for_one_field)
        idx = 0
        while idx < len(traces_for_one_field):
            l = len(traces_for_one_field)
            target_trace = traces_for_one_field[idx]
            for idx_cp in range(l - 1, idx, -1):
                if is_same_trace(target_trace, traces_for_one_field[idx_cp]):
                    traces_for_one_field.pop(idx_cp)

            idx += 1

        field_trace_count_after += len(traces_for_one_field)


def is_same_trace(trace_1, trace_2):
    if len(trace_1) != len(trace_2): return False
    for item in zip(trace_1, trace_2):
        if item[0] != item[1]:
            return False
        
    return True

def prompt_for_field(field):
    if field in fieldResults.keys() or field not in allFieldAndICCTraces.keys():
        return
    
    traces = allFieldAndICCTraces[field]
    prompt = {}
    prompt['field'] = field

    same_count = 0
    trace_count = 0
    result = '{}'
    for trace in traces:
        
        trace_prompt = construct_trace_prompt(trace)
        prompt['execTrace'] = trace_prompt
        promptstring = json.dumps(prompt)

        messages = construct_messages('field')
        messages.append({"role": "user", "content": promptstring})

        cur_result, n_token = call_chatGPT(messages)
        result, isUpdated = field_merge_and_check(result, cur_result)
        if not isUpdated:
            same_count += 1
        else:
            same_count = 0

        if same_count == 3 or trace_count >= MAX_TRACES_PER_FIELD:
            break
        
        trace_count += 1

    fieldResults[field] = json.loads(result)

def prompt_for_final_data(dataPoint):
    if dataPoint in dataResults.keys() or dataPoint not in allDataTrace.keys(): return
    
    traces = allDataTrace[dataPoint]
    prompt = {}

    same_count = 0
    trace_count = 0
    result = '{}'

    for trace in traces:
        
        trace_prompt = construct_trace_prompt(trace)
        prompt['execTrace'] = trace_prompt
        promptstring = json.dumps(prompt)

        messages = construct_messages('data')
        messages.append({"role": "user", "content": promptstring})
        
        cur_result, n_token = call_chatGPT(messages)

        result, isUpdated = field_merge_and_check(result, cur_result)
        if not isUpdated:
            same_count += 1
        else:
            same_count = 0

        
        cur_result = json.loads(cur_result)
        
        print("============================")
        print(cur_result)
        filtered_iae = []
        new_result = {}
        for data_type in cur_result:
            data_content = cur_result[data_type]
            constant_list = []
            for data in data_content:
                if '<CONSTANT>' in data and data.lower() != 'null':
                    constant_list.append(data.replace('<CONSTANT> ', ''))
            print(constant_list)
            if len(constant_list) == 1:
                tmp = data_type + ':' + constant_list[0]
                filtered_iae.append(tmp)
            else:
                new_result[data_type] = data_content

        print(filtered_iae)

        dataResults.setdefault(dataPoint, []).append(cur_result)

        data_categorization_result = prompt_for_data_categorization(new_result)


        
        iae = cur_result['in-app event'] if 'in-app event' in cur_result else []
        iae.extend(filtered_iae)
        data_categorization_result['IAE'].extend(iae)
        print(data_categorization_result)

        dataCategorizationResults.setdefault(dataPoint, []).append(data_categorization_result)

        if 'PII' in data_categorization_result.keys() and len(data_categorization_result['PII']) > 0:
            privacyDataPoint.setdefault(dataPoint, []).append(trace_count)

        if same_count == 3 or trace_count >= MAX_TRACES_PER_DATA:
            break
        
        trace_count += 1
        # print(messages)


def prompt_for_data(dataPoint):
    idx = 0
    solveSteps = dataSolveSteps[dataPoint]
    while idx < len(solveSteps):
        target = solveSteps[idx]
        if idx == len(solveSteps) - 1:
            prompt_for_final_data(target)
            return

        if target.startswith('<') and target.endswith('>'):
            prompt_for_field(target)

        idx += 1




def prompt_for_data_categorization(data):
    data_list = [_ for _ in data if _ != "in-app event"]
    prompt = {}
    prompt['data'] = data_list
    promptstring = json.dumps(prompt)

    messages = construct_messages('data_categorization')
    messages.append({"role": "user", "content": promptstring})
    cur_result, n_token = call_chatGPT(messages)

    return json.loads(cur_result)

def prompt_for_blocks_in_chain(dataPoint):
    conditionChains_for_dataPoint = allConditionChain[dataPoint]
    for cc_idx in privacyDataPoint[dataPoint]:
        conditionChain = conditionChains_for_dataPoint[cc_idx]
        for cb in conditionChain:
            prompt_for_condition(cb[0])

    
    
def prompt_for_final_condition(condition_tag):
    if condition_tag in conditionResults.keys() or condition_tag not in allConditionBlocks.keys():
        return
    trace = allConditionBlocks[condition_tag].trace
    prompt = {}
    trace_prompt = construct_trace_prompt(trace)
    prompt['execTrace'] = trace_prompt
    prompt['condition'] = allConditionBlocks[condition_tag].condition
    promptstring = json.dumps(prompt)
    messages = construct_messages('condition')
    messages.append({"role": "user", "content": promptstring})
    cur_result, n_token = call_chatGPT(messages)

    conditionResults[condition_tag] = json.loads(cur_result)


def prompt_for_condition(condition_tag):
    if condition_tag.startswith('[INVOKE]'): return

    idx = 0
    solveSteps = conditionSolveSteps[condition_tag]
    while idx < len(solveSteps):
        target = solveSteps[idx]
        if idx == len(solveSteps) - 1:
            prompt_for_final_condition(target)
            return

        if target.startswith('<') and target.endswith('>'): # field
            prompt_for_field(target)

        idx += 1


def prompt_for_context_summary(dataPoint):
    conditionChains_for_dataPoint = allConditionChain[dataPoint]

    for cc_idx in privacyDataPoint[dataPoint]:
        conditionChain = conditionChains_for_dataPoint[cc_idx]

    # cc_idx = 0
    # for conditionChain in conditionChains_for_dataPoint:
        if cc_idx >= len(dataResults[dataPoint]): return

        prompt_path = []
        prompt = {}
        for cb_tuple in conditionChain:
            cb = cb_tuple[0]
            # print(cb_tuple)
            d = {}
            if cb.startswith('[INVOKE]'):
                d['function_invocation'] = cb.replace('[INVOKE]', '')
            elif cb in conditionResults.keys() and 'purpose' in conditionResults[cb]:
                purpose = conditionResults[cb]['purpose']
                if "N/A" not in purpose:
                    d['purpose'] = purpose
                    d['satisfy'] = cb_tuple[1]

            if len(d) > 0:
                prompt_path.append(d)

        prompt_iae = [] if 'IAE' not in dataCategorizationResults[dataPoint][cc_idx].keys() else dataCategorizationResults[dataPoint][cc_idx]['IAE']
        prompt['path'] = prompt_path
        prompt['in-app events'] = prompt_iae
        promptstring = json.dumps(prompt)
        messages = construct_messages('context')
        messages.append({"role": "user", "content": promptstring})

        cur_result, n_token = call_chatGPT(messages)
        
        contextSummaryResults.setdefault(dataPoint, {}).setdefault(cc_idx, json.loads(cur_result))
        cc_idx += 1


def call_chatGPT(messages, temperature=0.0):
    model = "gpt-4o"

    max_attempts = 5
    attempts = 0

    while attempts < max_attempts:
        try:

            endpoint = AZURE_END_POINTS

            e = random.choice(endpoint)

            client = AzureOpenAI(
                azure_endpoint = e['base'],
                api_key = e['key'],
                api_version = "2024-10-21"
            )


            chat_completion = client.chat.completions.create(
                model=model,
                temperature=temperature,
                messages=messages,
                response_format={ "type": "json_object" },
                # request_timeout=30,
            )



            reply = chat_completion.choices[0].message.content.strip()
            
            # print(reply)

            return reply, chat_completion.usage.total_tokens
        except Exception as e:
            print(f"[OpenAI API Error]: {e}, Hash Value: {hash(str(messages))}")
            # if isinstance(e, openai.error.RateLimitError):
            if 'RateLimitError' in str(e):
                if 'Rate limit reached' in str(e):
                    time_sleep = random.randint(5, 10) * (attempts + 1)
                    time.sleep(time_sleep)
                    print(f"[OpenAI API RateLimitError]: Wait for {time_sleep}s!")
                else:
                    print(f'[OpenAI API RateLimitError]: {e}')
                    with open("notProcessApp.txt", 'a+') as f:
                        f.write(app_name + '\n')
                        sys.exit()            
            attempts += 1
            if attempts < max_attempts:
                time.sleep(2 ** attempts)
            else:
                print("[OpenAI API Error]: Max attempts reached. Skipped.")
                break
    return "", 0




def priors_embedding(prior_name):
    if prior_name == None: return ''    
    if prior_name.startswith('<') and prior_name.endswith('>'):
        result = fieldResults.get(prior_name, None)
    
    if result == None: return ''

    prompt = '\n<prior>\n' + json.dumps(result) + '\n</prior>'

    return prompt

def construct_trace_prompt(trace):
    prompt = '<trace>'
    for instr in trace:
        prompt += '\n' + instr[0] + priors_embedding(instr[1])
        
    prompt += '\n</trace>\n'
    return prompt.strip()

def construct_messages(fn):
    # construct message
    if fn == 'field':
        messages = [{"role": "system", "content": field_summary_system_info}]
        messages.append({"role": "user", "content": field_summary_example_user_prompt})
        messages.append({"role": "assistant", "content": field_summary_example_assistant_response})
    elif fn == 'condition':
        messages = [{"role": "system", "content": condition_summary_system_info}]
        messages.append({"role": "user", "content": condition_summary_example_user_prompt})
        messages.append({"role": "assistant", "content": condition_summary_example_assistant_response})
    elif fn == 'data_categorization':
        messages = [{"role": "system", "content": data_categorization_system_info}]
        messages.append({"role": "user", "content": data_categorization_example_user_prompt})
        messages.append({"role": "assistant", "content": data_categorization_example_assistant_response})
    elif fn == 'context':
        messages = [{"role": "system", "content": context_summary_system_info}]
        messages.append({"role": "user", "content": context_summary_example_user_prompt})
        messages.append({"role": "assistant", "content": context_summary_example_assistant_response})
    else: # data
        messages = [{"role": "system", "content": DATA_summary_system_info}]
        messages.append({"role": "user", "content": DATA_summary_example_user_prompt})
        messages.append({"role": "assistant", "content": DATA_summary_example_assistant_response})

    return messages

def field_merge_and_check(text_a, text_b):
    info_stored_a = json.loads(text_a)
    info_stored_b = json.loads(text_b)
    original_data_a = json.loads(text_a) 
    for key, values in info_stored_b.items():
        if key in info_stored_a:
            original_values = set(info_stored_a[key])
            new_values = set(values)
            info_stored_a[key] = list(original_values.union(new_values))
        else:
            info_stored_a[key] = values
    if original_data_a == info_stored_a:
        return json.dumps(info_stored_a), True
    else:
        return json.dumps(info_stored_a), False
    
def save_all_results():
    with open('gpt_results/' + app_name + '_GPT_results.pickle', 'wb') as file:
        content = (allConditionBlocks,
                    allConditionChain,
                    allDataTrace,
                    allFieldAndICCTraces,
                    allNodes,
                    dataSolveSteps,
                    conditionSolveSteps,
                    dataResults,
                    dataCategorizationResults,
                    fieldResults,
                    conditionResults,
                    privacyDataPoint,
                    contextSummaryResults)
        pickle.dump(content, file)  


MAX_TRACES_PER_FIELD = 5
MAX_TRACES_PER_DATA = 10
MAX_STEPS_PER_DATA = 30
MAX_STEPS_PER_CONDITION = 5


allConditionBlocks = {}
allConditionChain = {}
allDataTrace = {}
allFieldAndICCTraces = {}
allNodes = {}

dataSolveSteps = {}
conditionSolveSteps = {}

dataResults = {}
dataCategorizationResults = {}
fieldResults = {}
conditionResults = {}

privacyDataPoint = {}
contextSummaryResults = {}


global app_name

if __name__ == "__main__":
    
    # app_name = sys.argv[1]
    app_name = 'APP_result.json'
    file_path = app_name
    app_name = app_name.replace('_result.json', '')

    json_dir = './'

    print("solving: " + app_name)
    
    with open(json_dir + file_path, 'r') as file:

        for line in file:
            # print(line)
            if len(line) < 10: continue
            data = json.loads(line)
            if len(data) == 0: continue
            if 'backward_result' in data:
                parse_one_js(data, 'backward_result')
            elif 'field_results' in data:
                parse_one_js(data, 'field_results')
            
            


    remove_duplicate_traces()


    for startPoint_tag in allDataTrace:
        solveStep = []
        solveStep.append(startPoint_tag)
        index = 0
        while index < len(solveStep):
            toAddDependents = allNodes[solveStep[index]].dependentNode if solveStep[index] in allNodes else []
            solveStep.extend(list(set(toAddDependents) - set(solveStep)))
            index += 1
        solveStep = solveStep[:MAX_STEPS_PER_DATA] if len(solveStep) > MAX_STEPS_PER_DATA else solveStep
        dataSolveSteps[startPoint_tag] = solveStep[::-1]
        # print(len(solveStep))

    for condition_tag in allConditionBlocks:
        solveStep = []
        solveStep.append(condition_tag)
        index = 0
        while index < len(solveStep):
            toAddDependents = allNodes[solveStep[index]].dependentNode if solveStep[index] in allNodes else []
            solveStep.extend(list(set(toAddDependents) - set(solveStep)))
            index += 1
        solveStep = solveStep[:MAX_STEPS_PER_CONDITION] if len(solveStep) > MAX_STEPS_PER_CONDITION else solveStep
        conditionSolveSteps[condition_tag] = solveStep[::-1]
        # print(len(solveStep))

    finished_count = 0
    for dataPoint in allDataTrace:
        prompt_for_data(dataPoint)
        if len(privacyDataPoint.get(dataPoint, [])) > 0:
            prompt_for_blocks_in_chain(dataPoint)
            prompt_for_context_summary(dataPoint)
        finished_count += 1
        save_all_results()
        print(app_name, finished_count, '/', len(allDataTrace))
