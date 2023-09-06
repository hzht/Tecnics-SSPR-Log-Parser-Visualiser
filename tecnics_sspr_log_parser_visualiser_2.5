# HZH
# Version: 2.5
# Date 2023-02-14
# Tecnics SSPR - Log parser & Visualiser 

"""
# Every success / failure is tied to an ACTION i.e. reset, unlock.
# No reason collected for success. 
# Reason collected for every failure

Logic: 
# Every new block or instance is identified by a new unique SessionID
# Once a new block starts, function is called to finalise the count and ensure an increment caters for all the requirements 
of the collection e.g. categorised as one of (reset, unlock), either success or failure and if failure, a reason. 
# If no ACTION AND OR ACTOR is identified i.e. blank at the start of a new block, data is collected but not used in summarisations. 
This is for: /owa/ anomaly with no ACTION or ACTOR. 

Requirements:
# Need to cater for special numpties who clickety click click on everything according to their nonsensical whims i.e. after resetting
successfully, click unlock a few times and then click change password cause why not? How to capture this? Answer:
    * The condition for "same instance" should be:
        * identical SessionID matched to an Action type. If Action changes, it's a new instance regardless of identical SessionID.

Observations: 
# people are trying different options after failing, typically failing with NO_FACTOR_SET or USER_DOES_NOT_EXIST
for both reset or unlock.

Changes in version 2.4
* Removal of "Change" category for graphing and collection as this has been disabled for SSPR. DONE
* Addition of server3 & server4 directories so that logs no longer need to be renamed in folders1 & 2. DONE
* Scaling for weekly data. DONE
* Automate to run on schedule weekly first, then daily emails to be sent to the 'no factor' users
* Mechanism to pull zip files on schedule - waiting on access - 23 Feb 2023
* Log tailing live logs on 4 servers. 
* Auto emailing of people trying to use SSPR but failing due to "no_factor_set". 
"""

from datetime import datetime, timedelta, time
import zipfile
import os
import json
import random
import string
import shutil
import plotly.graph_objs as go
import plotly.subplots as sp
import copy
import time as snoozer

# constants
server1 = r".\server1"
server2 = r".\server2"
server3 = r".\server3"
server4 = r".\server4"
logs_dropbox = r".\logs_dropbox" 
logs_processed = r".\logs_processed" # processed logs (zips) are moved here. 
output_dir = r".\output" # holds json files containing summarisations 
report_dir = r".\report" # final graph
userlist = r".\userlist.txt" # list of unique users who have used SSPR
user_growth_dir = r".\user_growth" # yyyy-mm-dd.txt # holds number of unique users in userlist
no_factor_set_dir = r".\no_factor_set"
no_factor_set_userlist = r".\no_factor_set_userlist_cumulative.txt"

success_messages = { # messages / outcomes
    "Password Recovery Operation is successful": "Password Recovery Operation is successful", 
    "Unlock operation is performed": "Unlock operation is performed", 
    '"status":"SUCCESS"': '"status":"SUCCESS"'
}

failure_messages = {
    '"status":"NO_FACTOR_SET"': "NO_FACTOR_SET", 
    '"status":"TIMEOUT"': "TIMEOUT", 
    '"status":"USER_DOES_NOT_EXIST"': "USER_DOES_NOT_EXIST", 
    "Malicious request or intentional request": "MALICIOUS", 
    "was not found or does not implement IController": "CONTROLLER_FOR_PATH_NOT_FOUND", 
    "Your code doesn't match our records": "CODE_DOES_NOT_MATCH", 
    "Each code can only be used once": "CODE_REUSED", 
    "Password requirements: at least 10 characters": "PASSWORD_COMPLEXITY_HISTORY_NOT_MET", 
    '"errorCode":"E0000022"': "ENDPOINT_HTTP_SUPPORT_ISSUE", 
    "Warning : Code Input is missing": "CODE_INPUT_MISSING"
    }

def parse_log(extracted_log_file, zipped_log_mod_date):
    """
    Returns: [log_results, no_factor_set_actors_unique_to_log_only]
    """
    log_results = {
        "LOG_DATE": str(zipped_log_mod_date), # one date per log file
        "SUMMARY": {
            "RESET": { # forgot
                "instance": {"count": 0}, # just for easier summarisation (success + failure counts)
                "success": {"count": 0}, 
                "failure": {
                    "count": 0,
                    "reason": {
                        "NO_FACTOR_SET": 0, # "status":"NO_FACTOR_SET", "factorType":"sms","provider":"OKTA"
                        "USER_DOES_NOT_EXIST": 0, # "status":"USER_DOES_NOT_EXIST"
                        "TIMEOUT": 0, # "status":"TIMEOUT"
                        "MALICIOUS": 0, # potential malicious attempt: "Malicious request or intentional request tampering encontered"
                        "CONTROLLER_FOR_PATH_NOT_FOUND": 0,
                        "CODE_DOES_NOT_MATCH": 0, 
                        "CODE_REUSED": 0, 
                        "PASSWORD_COMPLEXITY_HISTORY_NOT_MET": 0,
                        "ENDPOINT_HTTP_SUPPORT_ISSUE": 0, #E000002 - likely will never be incremented as actor & action is ""
                        "CODE_INPUT_MISSING": 0
                    }
                }
            },
            "UNLOCK": {
                "instance": {"count": 0}, 
                "success": {"count": 0}, 
                "failure": {
                    "count": 0, 
                    "reason": {
                        "NO_FACTOR_SET": 0, 
                        "USER_DOES_NOT_EXIST": 0, 
                        "TIMEOUT": 0, 
                        "MALICIOUS": 0,
                        "CONTROLLER_FOR_PATH_NOT_FOUND": 0,
                        "CODE_DOES_NOT_MATCH": 0, 
                        "CODE_REUSED": 0, 
                        "PASSWORD_COMPLEXITY_HISTORY_NOT_MET": 0,
                        "ENDPOINT_HTTP_SUPPORT_ISSUE": 0, 
                        "CODE_INPUT_MISSING": 0,
                    }
                }
            }, 
            "target_sspr": 0,
            "target_okta": 0,
            "no_actor_action_or_outcome": 0, # collect but don't include or use as part of summarisation calculations e.g. no controller err
            "unique_actors": set()
            },
        # to be used to process a unique instance (either individual, or successive blocks of sessions) 
        # prior to incrementing data to SUMMARY BLOCK
        "INSTANCE": { # single instance of user action i.e. RESET or UNLOCK.
            "SessionID": "",
            "Actor": "", 
            "Action": "", 
            "Target": "", 
            "Outcome": "", # success / failure
            "MessageList": [], 
            }
    }

    no_factor_set_actors = set() # deliberately separate from log results - ALL no factors to date
    no_factor_set_actors_unique_to_log_only = set() # - UNIQUE TO LOG only

    def load_previous_unique_users(): 
        """Caters for both userlist.txt & no_factor_set_userlist.txt
        """
        with open(userlist, "r") as f: 
            try: 
                log_results["SUMMARY"]["unique_actors"] = set(f.read().splitlines())
            except Exception as e:
                print("eee:", e)
        with open(no_factor_set_userlist, "r") as f: 
            try: 
                for i in f: 
                    no_factor_set_actors.add(i.strip())
            except Exception as e: 
                print("eef:", e)
                
    def write_unique_users_to_file():
        """
        Also write / append yyyy-mm-dd.txt to user_growth_dir total number of unique users. 
        Over time it should be an upward trend. 
        Also writes no_factor_set_actors to the cumulative txt file
        """
        with open(userlist, "w") as f: 
            try: 
                f.write("\n".join(log_results["SUMMARY"]["unique_actors"]))
            except Exception as e: 
                print("fff:", e)

        with open(os.path.join(user_growth_dir, log_results["LOG_DATE"] + ".txt"), "w") as f:
            try: 
                f.write(str(len(log_results["SUMMARY"]["unique_actors"])))
            except Exception as e: 
                print("hhh:", e)

        with open(no_factor_set_userlist, "w") as f: 
            try: 
                f.write("\n".join(no_factor_set_actors))
            except Exception as e: 
                print("ffg:", e)

    def increment_counts(): 
        """
        End of a series of blocks associated with one unique SessionID. 
        Resulting in the increment of counts 
        """
        def increment_outcome(outcome, action): 
            try: 
                # print("\nDEBUG: increment_outcome - outcome:{}, action:{}".format(outcome, action))
                # print("DEBUG: entire log count:\n {}".format(log_results["SUMMARY"]))
                if outcome in success_messages:
                    log_results["SUMMARY"][action]["success"]["count"] += 1
                elif outcome in failure_messages: 
                    log_results["SUMMARY"][action]["failure"]["count"] += 1
                    log_results["SUMMARY"][action]["failure"]["reason"][failure_messages[outcome]] += 1
                    if outcome == '"status":"NO_FACTOR_SET"': # siphon no factor users to set 
                        no_factor_set_actors.add(log_results["INSTANCE"]["Actor"].lower())
                        no_factor_set_actors_unique_to_log_only.add(log_results["INSTANCE"]["Actor"].lower())
                else: 
                    print("CRITICAL ERROR: You shouldnt see this! INSTANCE:", log_results["INSTANCE"])
            except Exception as e: 
                print("zzz:", e)
        
        try: # ensure validity
            if log_results["INSTANCE"]["Actor"] == "": 
                log_results["INSTANCE"]["Actor"] = None 

            session_id = log_results["INSTANCE"]["SessionID"]
            actor = log_results["INSTANCE"]["Actor"]
            action = log_results["INSTANCE"]["Action"]
            target = log_results["INSTANCE"]["Target"]
            outcome = log_results["INSTANCE"]["Outcome"]

            # print(
            #     "Pre-increment - session_id: {}, actor: {}, action: {}, target: {}, outcome: {}".format(
            #     session_id, actor, action, target, outcome)
            #     )

            if None in [session_id, actor, action, target, outcome]: 
                log_results["SUMMARY"]["no_actor_action_or_outcome"] += 1
                # print("##### no_actor_action_or_outcome:", log_results["SUMMARY"]["no_actor_action_or_outcome"])
                return
        except Exception as e: 
            print("vvv:", e)

        try: # reaching hear guarantees good data (count)
            if target == "SSPR": 
                log_results["SUMMARY"]["target_sspr"] += 1 
            elif target == "OKTA": 
                log_results["SUMMARY"]["target_okta"] += 1 

            log_results["SUMMARY"][action]["instance"]["count"] += 1
            
            increment_outcome(outcome, action) # finally

        except Exception as e: 
            print("ggg:", e)

    def obtain_last_non_blank_outcome(message_list): 
        """
        """
        for i in range(len(message_list)-1, -1, -1): # work backwards
            try: 
                if message_list[i] != "\n": 
                    return message_list[i] # last non \n
            except Exception as e: 
                print("aaa:", e)
        return None # nothing! Anomaly, caters for "\n" # what to do here? 
    
    def process_message_type(line, message_list): 
        """Produces message_list as ["NO_FACTOR_SET" etc... i.e. already mapped to count names]
        """
        # found = False
        for key in success_messages: # try success
            try: 
                if key in line: 
                    message_list.append(key)
                    # found = True
                    break
            except Exception as e: 
                print("bbb:", e)
        # if not found:
        for key in failure_messages: 
            try: 
                if key in line: 
                    message_list.append(key) 
                    break
            except Exception as e: 
                print("www:", e)
    
    def reset_collection(): 
        """Resets the appropriate log_result["INSTANCE"] values in preparation
        for a new INSTANCE.
        """
        log_results["INSTANCE"]["MessageList"].clear()
        log_results["INSTANCE"]["Outcome"] = ""
        log_results["INSTANCE"]["Action"] = ""

    load_previous_unique_users() # load the users! 

    # MAGICKS
    with open(extracted_log_file, "r") as rolling_log:
        next(rolling_log) # skip the first line which is always empty
        for line in rolling_log:
            try: 
                if "Actor :" in line: # extract user
                    actor = line[8:].strip()
                    if actor != "": 
                        log_results["SUMMARY"]["unique_actors"].add(actor.lower())
                elif "SessionId :" in line: 
                    SessionID = line[12:].strip() 
                    if log_results["INSTANCE"]["SessionID"] == "": # start of log processing! 
                        log_results["INSTANCE"]["SessionID"] = SessionID
                    elif log_results["INSTANCE"]["SessionID"] == SessionID: # new block of same SessionID i.e. same INSTANCE
                        pass # continue. Action entry will determine whether same INSTANCE
                    elif log_results["INSTANCE"]["SessionID"] != SessionID: # new block of different SessionID, finalise processing for SessionID
                        # print("DEBUG: Previous instance data: {}\n".format(log_results["INSTANCE"]))
                        last_message = obtain_last_non_blank_outcome(log_results["INSTANCE"]["MessageList"]) # determine the outcome
                        log_results["INSTANCE"]["Outcome"] = last_message # note could be None, handled in increment_count()
                        increment_counts() 
                        # print("\nDEBUG: New instance ********************************\n")
                        reset_collection() 
                        log_results["INSTANCE"]["SessionID"] = SessionID
                    log_results["INSTANCE"]["Actor"] = actor # solves problem of Actor coming before the SessionID
                elif "Action :" in line: 
                    action = line[9:].strip()
                    if action == "" or action == "CHANGE": # ignores old logs with CHANGE.
                        action = None
                    if log_results["INSTANCE"]["Action"] == "": # new INSTANCE
                        log_results["INSTANCE"]["Action"] = action
                    elif log_results["INSTANCE"]["Action"] == action: # same action i.e. same INSTANCE
                        pass # continue to next line
                    elif log_results["INSTANCE"]["Action"] != action: # likely same SessionID but different Action i.e. new INSTANCE
                        last_message = obtain_last_non_blank_outcome(log_results["INSTANCE"]["MessageList"]) # process previous INSTANCE with a particular Action
                        log_results["INSTANCE"]["Outcome"] = last_message
                        increment_counts() 
                        reset_collection()
                elif "Target :" in line: 
                    log_results["INSTANCE"]["Target"] = line[9:].strip()
                elif "Message :" in line: 
                    process_message_type(line[10:].strip(), log_results["INSTANCE"]["MessageList"])
            except UnboundLocalError as e: 
                # missing_actor_action += 1
                print("You shouldn't see this:", e)
            except Exception as e2: 
                print("ccc:", e)
                print('cc2', log_results["INSTANCE"])
        
        try: # last block in log
            last_message = obtain_last_non_blank_outcome(log_results["INSTANCE"]["MessageList"]) # process previous INSTANCE with a particular Action
            log_results["INSTANCE"]["Outcome"] = last_message
            increment_counts() 
        except Exception as e: 
            print("abc:", e)
    
    write_unique_users_to_file() # write new unique users back to file

    return [log_results, no_factor_set_actors_unique_to_log_only] # to write to file

def commit_no_factor_actors_to_file(no_factor_set_actors_unique_to_log_only, destination, log_date): 
    """
    Commit set of no_factor_set_actors_unique_to_log_only to file -> into ./no_factor_set_dir e.g. 2023-02-01.txt
    similar to commit_log_results_to_file, combines identical dates.
    Set to commit is: no_factor_set_actors_unique_to_log_only
    """
    def commit(combined_users, destination, log_date): 
        """
        TXT
        """
        try: 
            with open(os.path.join(destination, log_date + ".txt"), "w") as f: 
                for u in combined_users: 
                    f.write(str(u) + "\n")
        except Exception as e: 
            print("zdr:", e)

    existing_data = set()
    if os.path.exists(os.path.join(destination, log_date + ".txt")): # check if TXT already exists, if so load into set
        try: 
            with open(os.path.join(destination, log_date + ".txt")) as f:
                for line in f: 
                    existing_data.add(line.strip())
        except Exception as e: 
            print("nmw:", e)
    
    try: # populate userlist
        temp_set = set()
        for u in no_factor_set_actors_unique_to_log_only: 
            temp_set.add(u)
    except Exception as e: 
        print("mew:", e)

    try: # combine two (one could be empty)
        combined_users = existing_data | temp_set
        commit(combined_users, destination, log_date)
    except Exception as e: 
        print("yeq:", e)

def commit_log_results_to_file(log_results, destination, log_date): 
    """ 
    Commit log_result to file -> into ./output e.g. 2023-02-01.txt. 
    If two identical dates exist, ensuring to sum results i.e. read first into memory and then 2nd
    summing required values before commiting to the same file again.
    Return log_results for consuming with plots
    """
    del log_results["INSTANCE"] # not needed
    
    def commit(log_results, destination, log_date): 
        """
        JSON
        """
        try: 
            # print("\nDEBUG: COMMIT TO LOG FILE: {}\n\n\n".format(log_results))
            with open(os.path.join(destination, log_date + ".json"), "w") as f: 
                json.dump(log_results, f)
        except Exception as e: 
            print("nnn:", e)

    if os.path.exists(os.path.join(destination, log_date + ".json")): 
        existing_data = None
        try: 
            with open(os.path.join(destination, log_date + ".json")) as f: 
                data = f.read()
                if data: 
                    existing_data = json.loads(data)
        except Exception as e: 
            print("mmm:", e)
        
        try: # modify exist_data with data from log_results
            log_results["SUMMARY"]["RESET"]["instance"]["count"] += int(existing_data["SUMMARY"]["RESET"]["instance"]["count"])
            log_results["SUMMARY"]["RESET"]["success"]["count"] += int(existing_data["SUMMARY"]["RESET"]["success"]["count"])
            log_results["SUMMARY"]["RESET"]["failure"]["count"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["count"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["NO_FACTOR_SET"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["NO_FACTOR_SET"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["USER_DOES_NOT_EXIST"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["USER_DOES_NOT_EXIST"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["TIMEOUT"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["TIMEOUT"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["MALICIOUS"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["MALICIOUS"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_REUSED"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_REUSED"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"])
            log_results["SUMMARY"]["RESET"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"] += int(existing_data["SUMMARY"]["RESET"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"])
            
        except Exception as e: 
            print('QQT:', e)

        try: 
            log_results["SUMMARY"]["UNLOCK"]["instance"]["count"] += int(existing_data["SUMMARY"]["UNLOCK"]["instance"]["count"])
            log_results["SUMMARY"]["UNLOCK"]["success"]["count"] += int(existing_data["SUMMARY"]["UNLOCK"]["success"]["count"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["count"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["count"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["NO_FACTOR_SET"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["NO_FACTOR_SET"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["USER_DOES_NOT_EXIST"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["USER_DOES_NOT_EXIST"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["TIMEOUT"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["TIMEOUT"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["MALICIOUS"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["MALICIOUS"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"])
            log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"] += int(existing_data["SUMMARY"]["UNLOCK"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"])
        except Exception as e: 
            print('ef2ef2ef2ef', log_results["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"])
            print('cafe', existing_data["SUMMARY"]["UNLOCK"]["failure"]["CODE_REUSED"])
            print('iiwq', e)

        try:
            log_results["SUMMARY"]["target_sspr"] += int(existing_data["SUMMARY"]["target_sspr"])
            log_results["SUMMARY"]["target_okta"] += int(existing_data["SUMMARY"]["target_okta"])
            log_results["SUMMARY"]["no_actor_action_or_outcome"] += int(existing_data["SUMMARY"]["no_actor_action_or_outcome"])
        except Exception as e: 
            print("ooo:", e)
            print("ooo.2", log_results, destination, log_date)
        
        try: 
            # union set then convert to list to list for commit to JSON file lest exception!
            log_results["SUMMARY"]["unique_actors"] = list(log_results["SUMMARY"]["unique_actors"] | set(existing_data["SUMMARY"]["unique_actors"])) 
        except Exception as e: 
            print('aha!', e)
    else: 
        # print('\nDEBUG: log_results_unique_actors', log_results["SUMMARY"]["unique_actors"])
        log_results["SUMMARY"]["unique_actors"] = list(log_results["SUMMARY"]["unique_actors"]) # convert the one set to list before commiting to file (json)

    try: # commit to file - either overwrite or write first time
        commit(log_results, destination, log_date)
    except Exception as e: 
        print("ppp:", e)    

def obtain_weekly_data(collection): 
    """Where collection is e.g. {"2000-03-04": 5, "2000-03-05": 4, n}
    To be used in conjunction with dictify_user_growth function to obtain weekly data.
    ISO week: starting from Monday and ending Sunday
    """
    result = {}
    
    for date_str, value in collection.items(): 
        date = datetime.strptime(date_str, "%Y-%m-%d").date()
        yr, week, day = date.isocalendar()
        week_start = date - timedelta(days=day)
        week_end = week_start + timedelta(days=7)
        #result[week_end.strftime("%Y-%m-%d")] = result.get(week_end.strftime("%Y-%m-%d"), 0) + int(value)
        result[week_end.strftime("%Y-%m-%d")] = value

    return result

def dictify_user_growth(source): 
    """ go through user_growth directory. Read each filename extract the date. 
    Store the info in collection in ascending order along with its value inside the txt file. 
    return the collection to be plotted.
    """
    daily_dict = {}
    txt_list = os.listdir(source)
    txt_list_times = [(f, os.path.getmtime(os.path.join(source, f))) for f in txt_list] # tuples of file and mod time
    txt_list_times.sort(key=lambda x: x[1]) # sort tuples by mod time in ascending order
    
    for txt_file in [f[0] for f in txt_list_times]:
        try: 
            with open(os.path.join(source, txt_file), "r") as file: 
                daily_dict[txt_file[:-4]] = file.read()                    
        except Exception as e: 
            print("kkk:", e)
    
    #print('daily', daily_dict)
    weekly_dict = obtain_weekly_data(daily_dict)

    return [daily_dict, weekly_dict]

def plot_graphs(mode=None, unique_user_growth=None, list_of_log_results=None):
    """
    Summary: 
    Parameters: 
    unique_user_growth: {'2023-02-01': '63', n}
    """
    try: # prep
        y_unique_user_growth = [int(i) for i in list(unique_user_growth.values())]

        # the one date to rule them all - hack to decrement days by 1 so as to use date in rolling.log and not when it is zipped i.e. the next day
        x_axis_log_dates = [
            (datetime.strptime(date, "%Y-%m-%d") - timedelta(days=1)).strftime("%Y-%m-%d") for date in [d["LOG_DATE"] for d in list_of_log_results] # decrement by one day
        ]
        
        # ALL RESETS
        y_reset_count = [int(d["SUMMARY"]["RESET"]["instance"]["count"]) for d in list_of_log_results] # d for dictionary
        y_reset_success_count = [int(d["SUMMARY"]["RESET"]["success"]["count"]) for d in list_of_log_results]
        y_reset_failure_count = [int(d["SUMMARY"]["RESET"]["failure"]["count"]) for d in list_of_log_results]
        y_reset_reason_no_factor = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["NO_FACTOR_SET"]) for d in list_of_log_results]
        y_reset_reason_no_user_exist = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["USER_DOES_NOT_EXIST"]) for d in list_of_log_results]
        y_reset_reason_timeout = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["TIMEOUT"]) for d in list_of_log_results]
        y_reset_reason_malicious = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["MALICIOUS"]) for d in list_of_log_results]
        y_reset_reason_no_controller_err = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"]) for d in list_of_log_results]
        y_reset_reason_no_code_match = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"]) for d in list_of_log_results]
        y_reset_reason_code_reused = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_REUSED"]) for d in list_of_log_results]
        y_reset_reason_complexity_not_met = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"]) for d in list_of_log_results]
        y_reset_reason_http_endpoint_issue = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"]) for d in list_of_log_results]
        y_reset_reason_missing_code = [int(d["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_INPUT_MISSING"]) for d in list_of_log_results]

        # ALL UNLOCKS
        y_unlock_count = [int(d["SUMMARY"]["UNLOCK"]["instance"]["count"]) for d in list_of_log_results]
        y_unlock_success_count = [int(d["SUMMARY"]["UNLOCK"]["success"]["count"]) for d in list_of_log_results]
        y_unlock_failure_count = [int(d["SUMMARY"]["UNLOCK"]["failure"]["count"]) for d in list_of_log_results]
        y_unlock_reason_no_factor = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["NO_FACTOR_SET"]) for d in list_of_log_results]
        y_unlock_reason_no_user_exist = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["USER_DOES_NOT_EXIST"]) for d in list_of_log_results]
        y_unlock_reason_timeout = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["TIMEOUT"]) for d in list_of_log_results]
        y_unlock_reason_malicious = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["MALICIOUS"]) for d in list_of_log_results]
        y_unlock_reason_no_controller_err = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"]) for d in list_of_log_results]
        y_unlock_reason_no_code_match = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"]) for d in list_of_log_results]
        y_unlock_reason_code_reused = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"]) for d in list_of_log_results]
        y_unlock_reason_complexity_not_met = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"]) for d in list_of_log_results]
        y_unlock_reason_http_endpoint_issue = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"]) for d in list_of_log_results]
        y_unlock_reason_missing_code = [int(d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_INPUT_MISSING"]) for d in list_of_log_results]

        y_no_actor_action_outcome_count = [int(d["SUMMARY"]["no_actor_action_or_outcome"]) for d in list_of_log_results]

        # COMBINED counts - attempts & success & failures 
        y_total_attempts = [y_reset_count[i] + y_unlock_count[i] for i in range(len(x_axis_log_dates))]
        y_total_successes = [y_reset_success_count[i] + y_unlock_success_count[i] for i in range(len(x_axis_log_dates))]
        y_total_failures = [y_reset_failure_count[i] + y_unlock_failure_count[i] for i in range(len(x_axis_log_dates))]

        # COMBINED categorised failures
        y_total_no_factor = [y_reset_reason_no_factor[i] + y_unlock_reason_no_factor[i] for i in range(len(x_axis_log_dates))]
        y_total_no_user_exists = [y_reset_reason_no_user_exist[i] + y_unlock_reason_no_user_exist[i] for i in range(len(x_axis_log_dates))]
        y_total_timeout = [y_reset_reason_timeout[i] + y_unlock_reason_timeout[i] for i in range(len(x_axis_log_dates))]
        y_total_malicious = [y_reset_reason_malicious[i] + y_unlock_reason_malicious[i] for i in range(len(x_axis_log_dates))]
        y_no_controller_err = [y_reset_reason_no_controller_err[i] + y_unlock_reason_no_controller_err[i] for i in range(len(x_axis_log_dates))]
        y_http_endpoint_err = [y_reset_reason_http_endpoint_issue[i] + y_unlock_reason_http_endpoint_issue[i] for i in range(len(x_axis_log_dates))]
        y_total_no_code_match = [y_reset_reason_no_code_match[i] + y_unlock_reason_no_code_match[i] for i in range(len(x_axis_log_dates))]
        y_total_code_reused = [y_reset_reason_code_reused[i] + y_unlock_reason_code_reused[i] for i in range(len(x_axis_log_dates))]
        y_total_complexity_not_met = [y_reset_reason_complexity_not_met[i] + y_unlock_reason_complexity_not_met[i] for i in range(len(x_axis_log_dates))]
        y_total_missing_code = [y_reset_reason_missing_code[i] + y_unlock_reason_missing_code[i] for i in range(len(x_axis_log_dates))]
        
        # MAX
        max_y_unique_user_growth = max(y_unique_user_growth)
        max_y_list_of_log_results = max(
            [
                max(y_reset_count),
                max(y_reset_success_count),
                max(y_reset_failure_count),
                max(y_unlock_count), 
                max(y_unlock_success_count), 
                max(y_unlock_failure_count), 
                max(y_no_actor_action_outcome_count)
            ]
        )
    except Exception as e: 
        print("qqq:", e)

    try: 
        # fig1 - LINE GRAPHS
        # daily user growth
        trace_unique_user_growth = go.Scatter(
            x=x_axis_log_dates, y=y_unique_user_growth, mode="lines+markers", name="Cumulative unique users", marker=dict(size=4), legendgroup="1"
            )
        # INSTANCE counts (reset, unlock)
        trace_forgot_pw = go.Scatter(
            x=x_axis_log_dates, y=y_reset_count, mode="lines+markers", name="Forgot password", marker=dict(size=4), legendgroup="2"
            )
        trace_unlock_pw = go.Scatter(
            x=x_axis_log_dates, y=y_unlock_count, mode="lines+markers", name="Unlock account", marker=dict(size=4), legendgroup="2"
            )
        # SUCCESS counts
        trace_reset_success = go.Scatter(
            x=x_axis_log_dates, y=y_reset_success_count, mode="lines+markers", name="Forgot success", marker=dict(size=4), legendgroup="3"
            )
        trace_unlock_success = go.Scatter(
            x=x_axis_log_dates, y=y_unlock_success_count, mode="lines+markers", name="Unlock success", marker=dict(size=4), legendgroup="3"
            )
        # FAILURES counts
        trace_reset_failure = go.Scatter(
            x=x_axis_log_dates, y=y_reset_failure_count, mode="lines+markers", name="Forgot failure", marker=dict(size=4), legendgroup="4"
            )
        trace_unlock_failure = go.Scatter(
            x=x_axis_log_dates, y=y_unlock_failure_count, mode="lines+markers", name="Unlock failure", marker=dict(size=4), legendgroup="4"
            )
        # COMBINED FAILURES CATEGORISED
        trace_no_factor = go.Scatter(
            x=x_axis_log_dates, y=y_total_no_factor, mode="lines+markers", name="No factor set", marker=dict(size=4), legendgroup="5"
            )
        trace_no_user = go.Scatter(
            x=x_axis_log_dates, y=y_total_no_user_exists, mode="lines+markers", name="No user exists", marker=dict(size=4), legendgroup="5"
            )
        trace_timeout = go.Scatter(
            x=x_axis_log_dates, y=y_total_timeout, mode="lines+markers", name="Timeout", marker=dict(size=4), legendgroup="5"
            )
        trace_no_code_match = go.Scatter(
            x=x_axis_log_dates, y=y_total_no_code_match, mode="lines+markers", name="No code match", marker=dict(size=4), legendgroup="5"
            )
        trace_code_reused = go.Scatter(
            x=x_axis_log_dates, y=y_total_code_reused, mode="lines+markers", name="Code reused", marker=dict(size=4), legendgroup="5"
            )
        trace_complexity_not_met = go.Scatter(
            x=x_axis_log_dates, y=y_total_complexity_not_met, mode="lines+markers", name="PW complexity not met", marker=dict(size=4), legendgroup="5"
            )
        trace_missing_code = go.Scatter(
            x=x_axis_log_dates, y=y_total_missing_code, mode="lines+markers", name="Missing code", marker=dict(size=4), legendgroup="5"
            )
        trace_malicious = go.Scatter(
            x=x_axis_log_dates, y=y_total_malicious, mode="lines+markers", name="Malicious activity", marker=dict(size=4), legendgroup="5"
            )
        trace_no_controller = go.Scatter(
            x=x_axis_log_dates, y=y_no_controller_err, mode="lines+markers", name="No controller", marker=dict(size=4), legendgroup="5"
            )
        trace_http_endpoint_err = go.Scatter(
            x=x_axis_log_dates, y=y_http_endpoint_err, mode="lines+markers", name="HTTP endpoint err", marker=dict(size=4), legendgroup="5"
            )            

        # fig2 - BAR & PIE 
        if mode == "daily":
            trace_sspr_type_bar = go.Bar(name="Attempts", x=["Reset", "Unlock"], y=[sum(y_reset_count), sum(y_unlock_count)], legendgroup="1")
            
            trace_sspr_success_comparison_group = go.Histogram(
                histfunc="sum", 
                y=[sum(y_reset_success_count), sum(y_unlock_success_count)], 
                x=["Reset", "Unlock"], 
                name="Success",
                marker=dict(color="teal"),
                legendgroup="2"
                )
            
            trace_sspr_fail_comparison_group = go.Histogram(
                histfunc="sum", 
                y=[sum(y_reset_failure_count), sum(y_unlock_failure_count)], 
                x=["Reset", "Unlock"], 
                name="Failure",
                marker=dict(color="darkorange"),
                legendgroup="2"
                )

            trace_sspr_failures_categorised_pie = go.Pie(
                labels=[
                    "No Factor Set", "No User Exists", "Timeout", "No Code Match", "Code Reused", "Password Complexity Not Met", 
                    "Code Input Missing", "Potential Malicious Activity", "No Controller Err", "HTTP Endpoint Anomaly"
                    ], 
                    values=[
                        sum(y_total_no_factor), 
                        sum(y_total_no_user_exists), 
                        sum(y_total_timeout), 
                        sum(y_total_no_code_match), 
                        sum(y_total_code_reused), 
                        sum(y_total_complexity_not_met), 
                        sum(y_total_missing_code),
                        sum(y_total_malicious),
                        sum(y_no_controller_err),
                        sum(y_http_endpoint_err)
                    ], 
                    # showlegend=False
                    legendgroup="3"
            )

        # fig3 - TABULAR 
        # reverse order date and values - copies
        x_axis_log_dates_reversed = x_axis_log_dates[::-1] # shallow copy
        y_total_attempts_reversed = y_total_attempts[::-1]
        # Note: too many variables created in ascending order, best to reverse once after all calculations - hence:
        y_total_successes_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_total_successes, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["success"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["success"]["count"]),
                        int(log["SUMMARY"]["RESET"]["instance"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["instance"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_total_failures_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_total_failures, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"]),
                        int(log["SUMMARY"]["RESET"]["instance"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["instance"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_reset_count_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_reset_count, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["instance"]["count"]),
                        int(log["SUMMARY"]["RESET"]["instance"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["instance"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_unlock_count_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_unlock_count, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["UNLOCK"]["instance"]["count"]),
                        int(log["SUMMARY"]["RESET"]["instance"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["instance"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_total_successes_reversed = y_total_successes[::-1]
        y_reset_success_count_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_reset_success_count, [round( # value | %
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["success"]["count"]),
                        int(log["SUMMARY"]["RESET"]["success"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["success"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_unlock_success_count_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_unlock_success_count, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["UNLOCK"]["success"]["count"]),
                        int(log["SUMMARY"]["RESET"]["success"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["success"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_total_failures_reversed = y_total_failures[::-1]
        y_reset_failure_count_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_reset_failure_count, [round( # value | %
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
        y_unlock_failure_count_percent_reversed = ["{}   |   {} %".format(v, p) for v, p in zip(y_unlock_failure_count, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["UNLOCK"]["failure"]["count"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]

        if mode == "daily": 
            table_date_title = "Date"
        elif mode == "weekly": 
            table_date_title = "Week - Ending Date"

        trace_success_failure_summary_table = go.Table(
            header=dict(values=[
                table_date_title, "Total Attempts", "Total Success / %", "Total Failure / %"
                ],
            line_color="darkslategray", 
            align="center", 
            font=dict(color="black", size=11)
            ),
            cells=dict(values=[
                x_axis_log_dates_reversed, # dates - newest first
                y_total_attempts_reversed, 
                y_total_successes_percent_reversed,
                y_total_failures_percent_reversed,
            ],
            line_color="darkslategray", 
            align=["center", "center", "center", "center"], 
            font=dict(color="darkslategray", size=13)
            ), # header -> value
            columnwidth=[1,1,1,1]
        )

        trace_sspr_type_summary_table = go.Table(
            header=dict(values=[
                table_date_title, "Total Attempts", "Resets / %", "Unlocks / %"
                ],
            line_color="darkslategray", 
            align="center", 
            font=dict(color="black", size=11)
            ),
            cells=dict(values=[
                x_axis_log_dates_reversed, # dates - newest first
                y_total_attempts_reversed,
                y_reset_count_percent_reversed,
                y_unlock_count_percent_reversed,
            ],
            line_color="darkslategray", 
            align=["center", "center", "center", "center"], 
            font=dict(color="darkslategray", size=13)
            ), # header -> value
            columnwidth=[1,1,1,1]
        )

        trace_sspr_successes_table = go.Table(
            header=dict(values=[
                table_date_title, "Total Successes", "Resets / %", "Unlocks / %"
                ],
            line_color="darkslategray", 
            align="center", 
            font=dict(color="black", size=11)
            ),
            cells=dict(values=[
                x_axis_log_dates_reversed, # dates - newest first
                y_total_successes_reversed,
                y_reset_success_count_percent_reversed,
                y_unlock_success_count_percent_reversed,
            ],
            line_color="darkslategray", 
            align=["center", "center", "center", "center"], 
            font=dict(color="darkslategray", size=13)
            ), # header -> value
            columnwidth=[1,1,1,1]
        )

        trace_sspr_failures_table = go.Table( 
            header=dict(values=[
                table_date_title, "Total Failures", "Resets / %", "Unlocks / %"
                ],
            line_color="darkslategray", 
            align="center", 
            font=dict(color="black", size=11)
            ),
            cells=dict(values=[
                x_axis_log_dates_reversed, # dates - newest first
                y_total_failures_reversed,
                y_reset_failure_count_percent_reversed,
                y_unlock_failure_count_percent_reversed,
            ],
            line_color="darkslategray", 
            align=["center", "center", "center", "center"], 
            font=dict(color="darkslategray", size=13)
            ), # header -> value
            columnwidth=[1,1,1,1]
        )

        trace_failures_categorised_summary_table = go.Table(
            header=dict(values=[
                table_date_title, "Total Failures", "No Factor Set / %", "No User Exists / %", "Timeout / %", "No Code Match / %", "Code Reused / %", 
                "Password Complexity Not Met / %", "Code Input Missing / %", "Potential Malicious Activity / %", "No Controller Err / %", "HTTP Endpoint Anomaly / %"
                ],
            line_color="darkslategray", 
            align="center", 
            font=dict(color="black", size=11)
            ),
            cells=dict(values=[
                x_axis_log_dates_reversed, # dates - newest first
                y_total_failures_reversed,
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_no_factor, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["NO_FACTOR_SET"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["NO_FACTOR_SET"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_no_user_exists, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["USER_DOES_NOT_EXIST"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["USER_DOES_NOT_EXIST"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_timeout, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["TIMEOUT"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["TIMEOUT"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_no_code_match, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_code_reused, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_REUSED"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_complexity_not_met, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1], 
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_missing_code, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_INPUT_MISSING"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_INPUT_MISSING"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],                   
                ["{}   |   {} %".format(v, p) for v, p in zip(y_total_malicious, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["MALICIOUS"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["MALICIOUS"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],                      
                ["{}   |   {} %".format(v, p) for v, p in zip(y_no_controller_err, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1],
                ["{}   |   {} %".format(v, p) for v, p in zip(y_http_endpoint_err, [round(
                    divide_by_zero(
                        int(log["SUMMARY"]["RESET"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"]),
                        int(log["SUMMARY"]["RESET"]["failure"]["count"]) + int(log["SUMMARY"]["UNLOCK"]["failure"]["count"])
                        ) * 100, 1
                    ) for log in list_of_log_results])
                ][::-1]
            ],
            line_color="darkslategray", 
            align=["center", "center", "center", "center", "center", "center",
                   "center", "center", "center", "center", "center", "center"], 
            font=dict(color="darkslategray", size=13)
            ), # header -> value
            columnwidth=[1,1,1,1,1,1,1,1,1,1,1,1]
        )
    except Exception as e: 
        print("rrr:", e)

    try: # DRAW SUBPLOTS
        if mode == "daily": 
            fig1_title = "SSPR Usage - Daily Stats"
            fig3_title = "SSPR - Daily Stats"
        elif mode == "weekly": 
            fig1_title = "SSPR Usage - Weekly Stats"
            fig3_title = "SSPR - Weekly Stats"

        # Line graphs
        fig1 = sp.make_subplots(rows=5, cols=1, subplot_titles=(
            "User Growth: cumulative number of unique users who have used SSPR", 
            "SSPR Categories Used",
            "SSPR Successful Attempts",
            "SSPR Failed Attempts",
            "Failure Categories (combined for reset & unlock)"
            ),
            specs=[[{"type": "xy"}], [{"type": "xy"}], [{"type": "xy"}], [{"type": "xy"}], [{"type": "xy"}]]
        )

        fig1.add_trace(trace_unique_user_growth, row=1, col=1)
        fig1.update_xaxes(row=1, col=1) 
        fig1.update_yaxes(title_text="Count", range=[0, max_y_unique_user_growth+100], row=1, col=1) 

        fig1.add_trace(trace_forgot_pw, row=2, col=1)
        fig1.add_trace(trace_unlock_pw, row=2, col=1)
        fig1.update_xaxes(row=2, col=1)
        fig1.update_yaxes(title_text="Count", range=[0, max_y_list_of_log_results+100], row=2, col=1) 

        fig1.add_trace(trace_reset_success, row=3, col=1)
        fig1.add_trace(trace_unlock_success, row=3, col=1)
        fig1.update_xaxes(row=3, col=1)
        fig1.update_yaxes(title_text="Count", range=[0, max_y_list_of_log_results+100], row=3, col=1) 

        fig1.add_trace(trace_reset_failure, row=4, col=1)
        fig1.add_trace(trace_unlock_failure, row=4, col=1)
        fig1.update_xaxes(row=4, col=1)
        fig1.update_yaxes(title_text="Count", range=[0, max_y_list_of_log_results+100], row=4, col=1) 

        fig1.add_trace(trace_no_factor, row=5, col=1)
        fig1.add_trace(trace_no_user, row=5, col=1)
        fig1.add_trace(trace_timeout, row=5, col=1)
        fig1.add_trace(trace_no_code_match, row=5, col=1)
        fig1.add_trace(trace_code_reused, row=5, col=1)
        fig1.add_trace(trace_complexity_not_met, row=5, col=1)
        fig1.add_trace(trace_missing_code, row=5, col=1)
        fig1.add_trace(trace_malicious, row=5, col=1)
        fig1.add_trace(trace_no_controller, row=5, col=1)
        fig1.add_trace(trace_http_endpoint_err, row=5, col=1)
        fig1.update_xaxes(row=5, col=1)
        fig1.update_yaxes(title_text="Count", range=[0, max_y_list_of_log_results+100], row=5, col=1) 

        fig1.update_layout(
            title=fig1_title,
            height=1200,
            legend_tracegroupgap=190
        )

        # Bar & pie graph
        if mode == "daily":
            fig2 = sp.make_subplots(rows=3, cols=1, shared_yaxes=True, subplot_titles=(
                "SSPR Usage",
                "SSPR Success & Failure",
                r"SSPR Failures Categorised (% in relation to failure total)",
                ), 
                specs=[
                    [{"type": "bar"}], [{"type": "bar"}], 
                    [{"type": "pie"}]
                ]
            )

            fig2.add_trace(trace_sspr_type_bar, row=1, col=1)
            fig2.add_trace(trace_sspr_success_comparison_group, row=2, col=1)
            fig2.add_trace(trace_sspr_fail_comparison_group, row=2, col=1)
            fig2.add_trace(trace_sspr_failures_categorised_pie, row=3, col=1)
            
            fig2.update_layout(
                title="SSPR - Running Totals",
                height=1200,
                legend_tracegroupgap=330
            )

        # Tabular report
        fig3 = sp.make_subplots(rows=4, cols=2, subplot_titles=(
            "Success / Failure",
            "SSPR Usage",
            r"SSPR Successes (% in relation to success total)",
            r"SSPR Failures (% in relation to failure total)",
            r"SSPR Failures Categorised (% in relation to failure total)",
            ), 
            specs=[
                [{"type": "table"}, {"type": "table"}],
                [{"type": "table", "colspan": 2}, None], 
                [{"type": "table", "colspan": 2}, None], 
                [{"type": "table", "colspan": 2}, None]
            ]
        )

        fig3.add_trace(trace_success_failure_summary_table, row=1, col=1)
        fig3.add_trace(trace_sspr_type_summary_table, row=1, col=2)
        fig3.add_trace(trace_sspr_successes_table, row=2, col=1)
        fig3.add_trace(trace_sspr_failures_table, row=3, col=1)
        fig3.add_trace(trace_failures_categorised_summary_table, row=4, col=1)
        
        fig3.update_layout(
            title=fig3_title,
            height=1200
        )

        if mode == "daily": 
            fig1.write_html(r".\report\SSPR_report - daily_graphs_1.html")
            fig2.write_html(r".\report\SSPR_report - running_totals.html")
            fig3.write_html(r".\report\SSPR_report - daily_tables.html")
        elif mode == "weekly": 
            fig1.write_html(r".\report\SSPR_report - weekly_graphs_1.html")
            fig3.write_html(r".\report\SSPR_report - weekly_tables.html")

    except Exception as e: 
        print("sss:", e)

def divide_by_zero(x, y): 
    """Caters for division by zero, returns 0 rather than exception.
    """
    try: 
        return x / y
    except Exception as e: 
        return 0
        
def get_log_modified_date(logs_source, zipped_log): 
    """
    """
    t = os.path.getmtime(os.path.join(logs_source, zipped_log))
    dt = datetime.fromtimestamp(t)
    return dt.strftime("%Y-%m-%d")

def copy_all_logs_to_single_folder(source, destination): 
    """
    """
    for f in os.listdir(source): 
        try: 
            if os.path.isfile(os.path.join(destination, f)): 
                new_fname = f[:-4] + "_" + "".join(random.choices(string.ascii_uppercase + string.digits, k=8)) + ".zip"
                shutil.copy2(os.path.join(source, f), os.path.join(destination, new_fname))
            else: 
                shutil.copy2(os.path.join(source, f), destination)
        except Exception as e: 
            print("iii:", e)

def delete_all_logs_in_source(source): 
    try: # delete the files from the source folder (server1 to 4) 
        for f in os.listdir(source):
            os.remove(os.path.join(source, f))
    except Exception as e: 
        print("jjj:", e)

def reload_json(output_dir, d):
    """
    Necessary, to reload summed logs on one date. Prior to appending to list_of_log_results
    """
    try: 
        with open(os.path.join(output_dir, d + ".json")) as f: 
            data = f.read()
            if data: 
                results_on_json_file = json.loads(data)
    except Exception as e: 
        print("ttt:", e)
    return results_on_json_file

def summarise_by_week(daily_log_results): 
    """Takes daily log results e.g. [{'LOG_DATE': '2023-02-27', 'SUMMARY': {'RESET': {'instance': {'count': 2},n...]
    Returns similar list of dictionaries structure but cumulative count for each ISO week of the year.
    """
    def calculate_dates(d): 
        log_date = datetime.strptime(d["LOG_DATE"], "%Y-%m-%d").date()
        year, week_num, day_num = log_date.isocalendar()
        week_start = log_date - timedelta(days=day_num)
        week_end = week_start + timedelta(days=7)
        return (year, week_end, week_num, day_num)

    result = []
    weekly_data = {}
    week_end_prev = calculate_dates(daily_log_results[0])[1] # track whether week has changed

    for d in daily_log_results: # a copy
        year, week_end, week_num, day_num = calculate_dates(d)

        r_instance_count = d["SUMMARY"]["RESET"]["instance"]["count"]
        r_success_count = d["SUMMARY"]["RESET"]["success"]["count"]
        r_failure_count = d["SUMMARY"]["RESET"]["failure"]["count"]
        r_failure_reason_nfs = d["SUMMARY"]["RESET"]["failure"]["reason"]["NO_FACTOR_SET"]
        r_failure_reason_usne = d["SUMMARY"]["RESET"]["failure"]["reason"]["USER_DOES_NOT_EXIST"]
        r_failure_reason_to = d["SUMMARY"]["RESET"]["failure"]["reason"]["TIMEOUT"]
        r_failure_reason_m = d["SUMMARY"]["RESET"]["failure"]["reason"]["MALICIOUS"]
        r_failure_reason_cfpnf = d["SUMMARY"]["RESET"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"]
        r_failure_reason_cdnm = d["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"]
        r_failure_reason_cr = d["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_REUSED"]
        r_failure_reason_pchnm = d["SUMMARY"]["RESET"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"]
        r_failure_reason_ehsi = d["SUMMARY"]["RESET"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"]
        r_failure_reason_cim = d["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_INPUT_MISSING"]

        u_instance_count = d["SUMMARY"]["UNLOCK"]["instance"]["count"]
        u_success_count = d["SUMMARY"]["UNLOCK"]["success"]["count"]
        u_failure_count = d["SUMMARY"]["UNLOCK"]["failure"]["count"]
        u_failure_reason_nfs = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["NO_FACTOR_SET"]
        u_failure_reason_usne = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["USER_DOES_NOT_EXIST"]
        u_failure_reason_to = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["TIMEOUT"]
        u_failure_reason_m = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["MALICIOUS"]
        u_failure_reason_cfpnf = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"]
        u_failure_reason_cdnm = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"]
        u_failure_reason_cr = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"]
        u_failure_reason_pchnm = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"]
        u_failure_reason_ehsi = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"]
        u_failure_reason_cim = d["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_INPUT_MISSING"]
        
        key = str(year) + "-" + str(week_num)
        
        if key not in weekly_data: # first log for week
            weekly_data[key] = d # first day
            weekly_data[key]["LOG_DATE"] = week_end.strftime("%Y-%m-%d") # key similar to that of daily
        else: # increment
            weekly_data[key]["SUMMARY"]["RESET"]["instance"]["count"] += r_instance_count
            weekly_data[key]["SUMMARY"]["RESET"]["success"]["count"] += r_success_count
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["count"] += r_failure_count
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["NO_FACTOR_SET"] += r_failure_reason_nfs
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["USER_DOES_NOT_EXIST"] += r_failure_reason_usne 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["TIMEOUT"] += r_failure_reason_to 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["MALICIOUS"] += r_failure_reason_m
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"] += r_failure_reason_cfpnf 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"] += r_failure_reason_cdnm 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_REUSED"] += r_failure_reason_cr 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"] += r_failure_reason_pchnm 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"] += r_failure_reason_ehsi 
            weekly_data[key]["SUMMARY"]["RESET"]["failure"]["reason"]["CODE_INPUT_MISSING"] += r_failure_reason_cim

            weekly_data[key]["SUMMARY"]["UNLOCK"]["instance"]["count"] += u_instance_count
            weekly_data[key]["SUMMARY"]["UNLOCK"]["success"]["count"] += u_success_count
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["count"] += u_failure_count
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["NO_FACTOR_SET"] += u_failure_reason_nfs
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["USER_DOES_NOT_EXIST"] += u_failure_reason_usne 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["TIMEOUT"] += u_failure_reason_to 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["MALICIOUS"] += u_failure_reason_m
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CONTROLLER_FOR_PATH_NOT_FOUND"] += u_failure_reason_cfpnf 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_DOES_NOT_MATCH"] += u_failure_reason_cdnm 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_REUSED"] += u_failure_reason_cr 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["PASSWORD_COMPLEXITY_HISTORY_NOT_MET"] += u_failure_reason_pchnm 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["ENDPOINT_HTTP_SUPPORT_ISSUE"] += u_failure_reason_ehsi 
            weekly_data[key]["SUMMARY"]["UNLOCK"]["failure"]["reason"]["CODE_INPUT_MISSING"] += u_failure_reason_cim

        if week_end != week_end_prev: # new week
            result.append(weekly_data[key])
            week_end_prev = week_end
            
    return result

def check_existence_file_folder(file_or_folder): 
    if os.path.exists(file_or_folder): 
        print("Created:", file_or_folder)
    else: 
        pass 
    
def purge_previous_run_data(): 
    for i in [r".\rolling.log", userlist, no_factor_set_userlist]: 
        try: 
            os.remove(i)
            print("Removed File:", i)
        except Exception as e: 
            print("RemFile:", e)

    for j in [user_growth_dir, no_factor_set_dir, output_dir, logs_dropbox, report_dir, logs_processed]:
        try: 
            shutil.rmtree(j)
            print("Removed Directory:", j)
        except Exception as e: 
            print("RemDir:", e)

    for i in [
        r".\rolling.log", userlist, no_factor_set_userlist, user_growth_dir, no_factor_set_dir, 
        output_dir, logs_dropbox, report_dir, logs_processed
        ]: 
        check_existence_file_folder(i)

    try: 
        print("\nRecreating directories and files:\n")

        os.makedirs(user_growth_dir)
        os.makedirs(no_factor_set_dir)
        os.makedirs(output_dir)
        os.makedirs(logs_dropbox)
        os.makedirs(report_dir)
        os.makedirs(logs_processed)
        with open(userlist, "w"): pass 
        with open(no_factor_set_userlist, "w"): pass 

        for j in [
            userlist, no_factor_set_userlist, user_growth_dir, no_factor_set_dir, 
            output_dir, logs_dropbox, report_dir, logs_processed
            ]: 
            check_existence_file_folder(j)
    except Exception as e: 
        print("Recreations failed:", e)

def count_files_in_dir(d): 
    f_list = os.listdir(d)
    f_list = [f for f in f_list if os.path.isfile(os.path.join(d, f))]
    return len(f_list)

def initiate_process(logs_source, processed_logs_destination): 
    """
    Parameter: list_of_log_results - passed in empty list, to be used in plotting
    """
    zipped_logs_list = os.listdir(logs_source) 
    zipped_logs_times = [(f, os.path.getmtime(os.path.join(logs_source, f))) for f in zipped_logs_list] # tuples of file and mod time
    zipped_logs_times.sort(key=lambda x: x[1]) # sort tuples by mod time in ascending order
    list_of_dates = set() # all dates of logs (no duplicates)
    for zipped_log in [f[0] for f in zipped_logs_times]:
        try: 
            if zipped_log.endswith(".zip"):
                d = get_log_modified_date(logs_source, zipped_log)
                with zipfile.ZipFile(os.path.join(logs_source, zipped_log), "r") as zip_file:
                    extracted_log_file = zip_file.extract("rolling.log") 
                    # print("DEBUG: Starting ++++++++++: {}\n".format(zip_file))
                    log_results = parse_log(extracted_log_file, d) # one - for each zip file i.e. rolling.log for each day
                    commit_log_results_to_file(log_results[0], output_dir, d) # two
                    commit_no_factor_actors_to_file(log_results[1], no_factor_set_dir, d) # three
                    list_of_dates.add(d) #list_of_log_results.append(reload_json(output_dir, d)) # four
                    # print("DEBUG: Finishing ++++++++++: {}\n".format(zip_file))
                shutil.move(
                    os.path.join(logs_source, zipped_log), 
                    os.path.join(processed_logs_destination, zipped_log)
                    ) # move to processed_log_dir
        except Exception as e:
            print("ddd:", e)
    return list_of_dates

def active_time_range(start, end): # time range during which hostlist.txt is processed
    now = datetime.now().time()
    if now > time(start[0], start[1]) and now < time(end[0], end[1]): # now > 11:30AM AND < 2:00PM
        return True
    else:
        return False
    
# def previous_reset_time(prev, now):
#     if last_run == None: # first run
#         return True 
#     else: 
#         difference = datetime.now() - prev
#         if difference.total_seconds() >= 86400:
#             return True
#         else:
#             return False
        
def created_within_last_hour(file): 
    file_mod_time = os.path.getmtime(file) 
    current_time = snoozer.time()
    if current_time - file_mod_time <= 3600: # created / modified within last hour i.e. new! 
        return True
    else: 
        return False 

def single_run(): 
    purge_previous_run_data() # Purge all previous runs

    print("\nServer 1, number of logs:", count_files_in_dir(server1))
    print("Server 2, number of logs:", count_files_in_dir(server2))
    print("Server 3, number of logs:", count_files_in_dir(server3))
    print("Server 4, number of logs:", count_files_in_dir(server4))

    copy_all_logs_to_single_folder(source=server1, destination=logs_dropbox)
    copy_all_logs_to_single_folder(source=server2, destination=logs_dropbox)
    copy_all_logs_to_single_folder(source=server3, destination=logs_dropbox)
    copy_all_logs_to_single_folder(source=server4, destination=logs_dropbox)

    # process each log file and commits results to .\output\ & .\no_factor_set
    list_of_dates = initiate_process(
        logs_source=logs_dropbox, 
        processed_logs_destination=logs_processed
        )

    try: # obtain a list (list_of_log_results) of all the results (dict) from the index 0 return value of parse_log function.
        sorted_list_of_dates = sorted(list_of_dates, key=lambda x: x) # this works as it is already in YYYY-mm-dd format
        daily_log_results = list() # will contain all log_results
        for d in sorted_list_of_dates: # unique dates
            daily_log_results.append(reload_json(output_dir, d))
    except Exception as e: 
        print("uuu:", e)

    try: # weekly 
        weekly_log_results = summarise_by_week(copy.deepcopy(daily_log_results)) 
    except Exception as e: 
        print("uuu2:", e)

    delete_all_logs_in_source(source=server1)
    delete_all_logs_in_source(source=server2)
    delete_all_logs_in_source(source=server3)
    delete_all_logs_in_source(source=server4)

    # processed stat
    print("\nNumber of logs processed:", count_files_in_dir(logs_processed))

    # read daily user growth into dictionary
    daily_growth, weekly_growth = dictify_user_growth(source=user_growth_dir) # {'2023-02-01': '63', n} 

    # plot...!
    plot_graphs(mode="daily", unique_user_growth=daily_growth, list_of_log_results=daily_log_results) # daily
    plot_graphs(mode="weekly", unique_user_growth=weekly_growth, list_of_log_results=weekly_log_results) # weekly

# MAINLINE
msg = """
Run mode: 
1) Single run - i.e. manually copied logs for processing one off in order to generate reports and user lists. 

2) Scheduled - i.e. automated to run every morning at 9:00am. Automates single run process to produce reports and 
user lists. When selected, script will snooze indefinitely until when scheduled to run (9:00am).

Requires UNC path access to 4 server's log locations. Option will map to these log locations and automatically 
copy the logs etc. 

3) Tail live log - i.e. actively tail live (not archived) logs on 4 servers to obtain real-time list of users who 
fall into the category of "no_factor_set". NO reports are generated with this option. It is to be used only to 
generate user list for communication with affected users (to sign up for Okta verify).

Requires UNC path access to 4 server's log locations and to be run on a server that is enabled for message relay 
in order to automate sending of email to business analyst(s). \n
"""

single_run()

# print(msg)
# run_mode = input(r"Select run mode: 1, 2 or 3: ")

# if run_mode == "1": # single run
    # single_run

# elif run_mode == "2": # scheduled
#     last_run = None
#     while True: 
#         try: 
#             snoozer.sleep(60)
#             print("snoozing...")
#             if active_time_range(start=[9, 00], end=[9, 30]): 
#                 if previous_reset_time(last_run, datetime.now()): # 24 hour elapsed
#                     last_run = datetime.now() 
#                     if created_within_last_hour(userlist): 
#                         pass

#                     # while it's older than 1 hour
#         except Exception as e: 
#             print(e)
# elif run_mode == "3": # tail live log 
#     pass 
