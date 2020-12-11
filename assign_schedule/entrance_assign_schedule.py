from . import assign_schedule as assign_schedule
from . import solve_conflict as solve_conflict
import json
# debug
# import assign_class_SA_v3_SaveConflict_LockedCla as assign_schedule
# import solve_conflict as solve_conflict
import copy


# reference:https://blog.csdn.net/nigelyq/article/details/78930330

# data_source是DataSource的实例
def main(data_source):
    data1 = copy.deepcopy(data_source)
    # 将data1转化成solve_conflict_object
    solve_conflict_object = solve_conflict.SolveConflict(data1)

    data2 = copy.deepcopy(data_source)
    # 把一部分数据的1班2班转换成 1，2
    translate_data = assign_schedule.AssignSchedule.translate_from(data2)

    assign_schedule_object = assign_schedule.AssignSchedule(translate_data)
    # 主函数
    # try:
    #     result, conflict_list = assign_schedule_object.run(translate_data, solve_conflict_object.run_of_outer)
    # except Exception:
    #     print(Exception)
    result, conflict_list = assign_schedule_object.run(translate_data, solve_conflict_object.run_of_outer)
    return result, conflict_list
