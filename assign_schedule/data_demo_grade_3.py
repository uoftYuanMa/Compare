########################################################################################################################
###                                        排课算法数据文件                                                          ###
########################################################################################################################
#                                    项目名称：基于贪心和邻域搜索算法的排课算法                               #
#                                    程 序 员：张 鑫                                                          #
#                                    开始日期：2020年5月26日                                                  #
#                                    更新日期：2020年6月17日[1],2020年6月30日[2]                              #
# ---------------------------------------------------------------------------------------------------------------------#
# 变量：
#       WEEK                       :: 一周排课的天数
#       SECTION                    :: 一天排课节数
#       MORNING_CLASS_NUM          :: 上午课时数
#       LINK_COURSE_COUNT_PEER_DAY :: 一天连堂课最多节数
#       COURSE_TOTAL               :: 不同班级下课程对应的总课时数
#       COURSE_LINKED_HOURS        :: 不同班级下课程对应的连堂课课时数
#       COURSE_MORNING_TOTAL       :: 不同班级下课程对应的最大上午排课课时数
#       TEACHER_HEAD_TAIL_NUM      :: 某教师下午首节和末节安排的最大课时数,0表示不限制  格式: {教师:(上午首节最大课时数,上午末节课最大课时数,下午首节最大课时数,下午末节课最大课时数)} [2]
#       COURSE_SAME_TIME_NUM       :: 设置某门课最多可几个班同时上课（教室容量限制）    格式: 科目:最多几个班同时上课
#       CLASSES                    :: 班级列表，按顺序列数所有的班级
#       CLASSES_COURSE_TEACHER     :: 不同班级下课程对应的教师名称
#       CONFLICT_TEACHERS          :: 教师互斥信息，规定不能同一时间上课的教师，2人一组
#       EXTRA_ASSIGN_COURSE        :: 额外需要安排的课程
#       BIND_CLASSES               :: 对开课程
#       FLOW_CLASS_TIME            :: 走班课时间
#       NOT_ASSIGN_TIME            :: 不排课时间
#       NOT_ASSIGN_TEACHER         :: 固定教师不排课的时间
#       NOT_ASSIGN_COURSE          :: 固定科目不排课的时间
#       PART_SCHEDULE              :: 手排课时间，可提前手动安排课程
#       LINK_COURSE_TIMES          :: 连堂课可排时间(day -- 天数,section -- 节数)
########################################################################################################################
# 默认的规则(须知）:
# 1. 同一科目，一天只能排一节，可以是单独一节课（1课时），也可以是一节连堂课（2课时）
# 2. 同一科目的连排不能相邻
# 3. 一天8个课时，其中上午4课时，下午4课时
# 合理性检测规则:
# 1.总课时数不超过一周最大课时数
# 2.科目手排课+连堂课课时数不超过科目总课时数 + 手排课没有重复位置
# 3.连排课课时数数不超过总课时数
# 4.科目一周排课节数 <= 5 (包括连堂课，因为同科目一天不能排两次）另外: 如果通过增加连堂课节数能修正用户操作，则增加连堂课节数
# 5.COURSE_TOTAL COURSE_LINKED_HOURS COURSE_MORNING_TOTAL 置空需保留班级和科目
# 6.每个班连堂课总数<LINK_COURSE_COUNT_PEER_DAY*5 否则无法安排完所有的连堂课
########################################################################################################################
WEEK = 7
SECTION = 7
MORNING_CLASS_NUM = 4
LINK_COURSE_COUNT_PEER_DAY = 3
# COURSE_TOTAL = {
#     '1班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '2班': {'语': 6, '数': 6, '英': 6, '物': 5, '生': 5, '体': 2},
#     '3班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '4班': {'语': 6, '数': 6, '英': 6, '化': 5, '生': 5, '体': 2},
#     '5班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '6班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '7班': {'语': 6, '数': 6, '英': 6, '政': 5, '地': 5, '体': 2},
#     '8班': {'语': 6, '数': 6, '英': 6, '历': 5, '地': 5, '体': 2},
#     '9班': {'语': 6, '数': 6, '英': 6, '历': 5, '政': 5, '体': 2}
# }

COURSE_TOTAL = {
    '1班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '2班': {'1': 6, '2': 6, '3': 6, '4': 5, '6': 5, '0': 2},
    '3班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '4班': {'1': 6, '2': 6, '3': 6, '5': 5, '6': 5, '0': 2},
    '5班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '6班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '7班': {'1': 6, '2': 6, '3': 6, '9': 5, '8': 5, '0': 2},
    '8班': {'1': 6, '2': 6, '3': 6, '7': 5, '8': 5, '0': 2},
    '9班': {'1': 6, '2': 6, '3': 6, '7': 5, '9': 5, '0': 2}
}
# COURSE_LINKED_HOURS = {
#     '1班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '生': 0, '历': 0, '政': 0, '地': 0, '体': 0},
#     '2班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 0, '生': 1, '历': 0, '政': 0, '地': 0, '体': 0},
#     '3班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '生': 0, '历': 0, '政': 0, '地': 0, '体': 0},
#     '4班': {'语': 2, '数': 2, '英': 2, '物': 0, '化': 1, '生': 1, '历': 0, '政': 0, '地': 0, '体': 0},
#     '5班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '生': 0, '历': 0, '政': 0, '地': 0, '体': 0},
#     '6班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '生': 0, '历': 0, '政': 0, '地': 0, '体': 0},
#     '7班': {'语': 2, '数': 2, '英': 2, '物': 0, '化': 0, '生': 0, '历': 0, '政': 1, '地': 1, '体': 0},
#     '8班': {'语': 2, '数': 2, '英': 2, '物': 0, '化': 0, '生': 0, '历': 1, '政': 0, '地': 1, '体': 0},
#     '9班': {'语': 2, '数': 2, '英': 2, '物': 0, '化': 0, '生': 0, '历': 1, '政': 1, '地': 0, '体': 0}
# }

# COURSE_LINKED_HOURS = {
#     '1班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '体': 0},
#     '2班': {'语': 2, '数': 2, '英': 2, '物': 1, '生': 1, '体': 0},
#     '3班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '体': 0},
#     '4班': {'语': 2, '数': 2, '英': 2, '化': 1, '生': 1, '体': 0},
#     '5班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '体': 0},
#     '6班': {'语': 2, '数': 2, '英': 2, '物': 1, '化': 1, '体': 0},
#     '7班': {'语': 2, '数': 2, '英': 2, '政': 1, '地': 1, '体': 0},
#     '8班': {'语': 2, '数': 2, '英': 2, '历': 1, '地': 1, '体': 0},
#     '9班': {'语': 2, '数': 2, '英': 2, '历': 1, '政': 1, '体': 0}
# }

COURSE_LINKED_HOURS = {
    '1班': {'1': 2, '2': 2, '3': 2, '4': 1, '5': 1, '0': 0},
    '2班': {'1': 2, '2': 2, '3': 2, '4': 1, '6': 1, '0': 0},
    '3班': {'1': 2, '2': 2, '3': 2, '4': 1, '5': 1, '0': 0},
    '4班': {'1': 2, '2': 2, '3': 2, '5': 1, '6': 1, '0': 0},
    '5班': {'1': 2, '2': 2, '3': 2, '4': 1, '5': 1, '0': 0},
    '6班': {'1': 2, '2': 2, '3': 2, '4': 1, '5': 1, '0': 0},
    '7班': {'1': 2, '2': 2, '3': 2, '9': 1, '8': 1, '0': 0},
    '8班': {'1': 2, '2': 2, '3': 2, '7': 1, '8': 1, '0': 0},
    '9班': {'1': 2, '2': 2, '3': 2, '7': 1, '9': 1, '0': 0}
}

# COURSE_MORNING_TOTAL = {
#     '1班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '2班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '3班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '4班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '5班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '6班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '7班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '8班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2},
#     '9班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '生': 5, '历': 5, '政': 5, '地': 5, '体': 2}
# }

# COURSE_MORNING_TOTAL = {
#     '1班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '2班': {'语': 6, '数': 6, '英': 6, '物': 5, '生': 5, '体': 2},
#     '3班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '4班': {'语': 6, '数': 6, '英': 6, '化': 5, '生': 5, '体': 2},
#     '5班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '6班': {'语': 6, '数': 6, '英': 6, '物': 5, '化': 5, '体': 2},
#     '7班': {'语': 6, '数': 6, '英': 6, '政': 5, '地': 5, '体': 2},
#     '8班': {'语': 6, '数': 6, '英': 6, '历': 5, '地': 5, '体': 2},
#     '9班': {'语': 6, '数': 6, '英': 6, '历': 5, '政': 5, '体': 2}
# }

COURSE_MORNING_TOTAL = {
    '1班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '2班': {'1': 6, '2': 6, '3': 6, '4': 5, '6': 5, '0': 2},
    '3班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '4班': {'1': 6, '2': 6, '3': 6, '5': 5, '6': 5, '0': 2},
    '5班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '6班': {'1': 6, '2': 6, '3': 6, '4': 5, '5': 5, '0': 2},
    '7班': {'1': 6, '2': 6, '3': 6, '9': 5, '8': 5, '0': 2},
    '8班': {'1': 6, '2': 6, '3': 6, '7': 5, '8': 5, '0': 2},
    '9班': {'1': 6, '2': 6, '3': 6, '7': 5, '9': 5, '0': 2}
}

TEACHER_HEAD_TAIL_NUM = {'1': (0, 0, 0, 0)}
# COURSE_SAME_TIME_NUM = {'语': 6}
COURSE_SAME_TIME_NUM = {'1': 6}
# CLASSES = ['1班', '2班', '3班', '4班', '5班', '6班', '7班', '8班', '9班']
CLASSES = ['1班', '2班', '3班', '4班', '5班', '6班', '7班', '8班', '9班']
CLASSES_COURSE_TEACHER = {
    '1班': {'1': '1', '2': '6', '3': '11', '4': '16', '5': '22', '0': '28'},
    '2班': {'1': '2', '2': '7', '3': '12', '4': '17', '6': '23', '0': '29'},
    '3班': {'1': '3', '2': '7', '3': '13', '4': '18', '5': '24', '0': '29'},
    '4班': {'1': '1', '2': '8', '3': '14', '5': '19', '6': '25', '0': '29'},
    '5班': {'1': '4', '2': '9', '3': '15', '4': '17', '5': '24', '0': '29'},
    '6班': {'1': '4', '2': '10', '3': '14', '4': '18', '5': '19', '0': '29'},
    '7班': {'1': '3', '2': '8', '3': '12', '8': '20', '9': '26', '0': '29'},
    '8班': {'1': '5', '2': '9', '3': '13', '7': '21', '8': '27', '0': '30'},
    '9班': {'1': '2', '2': '6', '3': '11', '7': '21', '9': '26', '0': '30'}
}
# CLASSES_COURSE_TEACHER = {
#     '1班': {'语': '1', '数': '6', '3': '11', '4': '16', '5': '22', '0': '28'},
#     '2班': {'语': '2', '数': '7', '英': '12', '物': '17', '生': '23', '体': '29'},
#     '3班': {'语': '3', '数': '7', '英': '13', '物': '18', '化': '24', '体': '29'},
#     '4班': {'语': '1', '数': '8', '英': '14', '化': '19', '生': '25', '体': '29'},
#     '5班': {'语': '4', '数': '9', '英': '15', '物': '17', '化': '24', '体': '29'},
#     '6班': {'语': '4', '数': '10', '英': '14', '物': '18', '化': '19', '体': '29'},
#     '7班': {'语': '3', '数': '8', '英': '12', '地': '20', '政': '26', '体': '29'},
#     '8班': {'语': '5', '数': '9', '英': '13', '历': '21', '地': '14丽', '体': '30'},
#     '9班': {'语': '2', '数': '6', '英': '11', '历': '21', '政': '26', '体': '30'}
# }
######## CONFLICT_TEACHERS = {'教师1-教师2': [{'week': 4, 'section': 5}, {'week': 5, 'section': 8}]}
CONFLICT_TEACHERS = {}
# GO_TEACHERS = ['王碧雪', '王晓捷', '23', '于秀艳', '21', '雷志清', '刘壮壮', '许鑫']

# EXTRA_ASSIGN_COURSE = {
#     '1班': [{'course': '政', 'num': 2, 'teacher': '许鑫'}],
#     '2班': [{'course': '政', 'num': 2, 'teacher': '许鑫'}],
#     '3班': [{'course': '政', 'num': 2, 'teacher': '许鑫'}],
#     '4班': [{'course': '政', 'num': 2, 'teacher': '韩志红'}, {'course': '物', 'num': 2, 'teacher': '17'}],
#     '5班': [{'course': '政', 'num': 2, 'teacher': '韩志红'}],
#     '6班': [{'course': '政', 'num': 2, 'teacher': '韩志红'}],
#     '7班': [{'course': '物', 'num': 2, 'teacher': '17'}],
#     '8班': [{'course': '政', 'num': 2, 'teacher': '刘婕'}, {'course': '物', 'num': 2, 'teacher': '18'}],
#     '9班': [{'course': '物', 'num': 2, 'teacher': '王碧雪'}]
# }
EXTRA_ASSIGN_COURSE = {}
BIND_CLASSES = {'1班-5': {'class': '9班', 'subject': '7'}, '9班-9': {'class': '7班', 'subject': '8'}}
# BIND_CLASSES = {}
FLOW_CLASS_TIME = [
    {'week': 2, 'section': 5},
    {'week': 4, 'section': 5},
    {'week': 4, 'section': 6},
    {'week': 5, 'section': 5},
    {'week': 3, 'section': 3},
]
NOT_ASSIGN_TIME = [
    # {'week': 1, 'section': 7},
    # {'week': 2, 'section': 7},
]
GO_TEACHERS = []
NOT_ASSIGN_TEACHER = {
    # demo
    '8': [{'week': 1, 'section': 7}, {'week': 2, 'section': 7}, {'week': 3, 'section': 7}, {'week': 5, 'section': 7}],
    # '29': [{'week': 5, 'section': 1}, {'week': 5, 'section': 2}, {'week': 5, 'section': 3}, {'week': 5, 'section': 4},
    #      {'week': 5, 'section': 5}, {'week': 5, 'section': 6}, {'week': 5, 'section': 7}],
    # '30': [{'week': 1, 'section': 1}, {'week': 1, 'section': 2}, {'week': 1, 'section': 3}, {'week': 1, 'section': 4},
    #          {'week': 1, 'section': 6}, {'week': 1, 'section': 7},
    #          {'week': 3, 'section': 1}, {'week': 3, 'section': 2}, {'week': 3, 'section': 3}, {'week': 3, 'section': 4},
    #          {'week': 3, 'section': 5},
    #          {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
    #          {'week': 4, 'section': 6}, {'week': 4, 'section': 7},
    #         {'week': 5, 'section': 5},
    #         {'week': 5, 'section': 6}, {'week': 5, 'section': 7}
    #         ]
}
# NOT_ASSIGN_COURSE = {
#     '语': [{'week': 2, 'section': 5}, {'week': 2, 'section': 6}, {'week': 4, 'section': 5}, {'week': 4, 'section': 6},
#           {'week': 4, 'section': 7},
#           {'week': 3, 'section': 1}, {'week': 3, 'section': 2}, {'week': 3, 'section': 3}, {'week': 3, 'section': 4},
#           {'week': 1, 'section': 5}, {'week': 2, 'section': 5}, {'week': 3, 'section': 5}, {'week': 4, 'section': 5},
#           {'week': 5, 'section': 5}],
#     '数': [{'week': 4, 'section': 1}, {'week': 4, 'section': 2}, {'week': 4, 'section': 3}, {'week': 4, 'section': 4},
#           {'week': 2, 'section': 5}, {'week': 2, 'section': 6},
#           {'week': 5, 'section': 5}, {'week': 5, 'section': 6}, {'week': 5, 'section': 7}],
#     '英': [{'week': 3, 'section': 1}, {'week': 3, 'section': 2}, {'week': 3, 'section': 3}, {'week': 3, 'section': 4},
#           {'week': 2, 'section': 5}, {'week': 2, 'section': 6}, {'week': 2, 'section': 7}],
#     '物': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
#           {'week': 5, 'section': 3}, {'week': 5, 'section': 4}],
#     '化': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
#           {'week': 2, 'section': 1}, {'week': 2, 'section': 2}, {'week': 2, 'section': 3}, {'week': 2, 'section': 4},
#           {'week': 5, 'section': 1}, {'week': 5, 'section': 2}],
#     '生': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
#           {'week': 1, 'section': 1}, {'week': 1, 'section': 2}, {'week': 1, 'section': 3}, {'week': 1, 'section': 4},
#           {'week': 5, 'section': 1}, {'week': 5, 'section': 2}],
#     '历': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
#           {'week': 5, 'section': 1}, {'week': 5, 'section': 2}, {'week': 5, 'section': 3}, {'week': 5, 'section': 4}],
#     '政': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
#           {'week': 1, 'section': 5}, {'week': 1, 'section': 6}, {'week': 1, 'section': 7}, {'week': 5, 'section': 1},
#           {'week': 5, 'section': 2}],
#     '地': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
#           {'week': 5, 'section': 1}, {'week': 5, 'section': 2}, {'week': 5, 'section': 3}, {'week': 5, 'section': 4},
#           {'week': 1, 'section': 1}, {'week': 1, 'section': 2}],
#     '体': [{'week': 4, 'section': 5}, {'week': 4, 'section': 6}, {'week': 4, 'section': 7}],
#
# }
NOT_ASSIGN_COURSE = {
    '1': [{'week': 2, 'section': 5}, {'week': 2, 'section': 6}, {'week': 4, 'section': 5}, {'week': 4, 'section': 6},
          {'week': 4, 'section': 7},
          {'week': 3, 'section': 1}, {'week': 3, 'section': 2}, {'week': 3, 'section': 3}, {'week': 3, 'section': 4},
          {'week': 1, 'section': 5}, {'week': 2, 'section': 5}, {'week': 3, 'section': 5}, {'week': 4, 'section': 5},
          {'week': 5, 'section': 5}],
    '2': [{'week': 4, 'section': 1}, {'week': 4, 'section': 2}, {'week': 4, 'section': 3}, {'week': 4, 'section': 4},
          {'week': 2, 'section': 5}, {'week': 2, 'section': 6},
          {'week': 5, 'section': 5}, {'week': 5, 'section': 6}, {'week': 5, 'section': 7}],
    '3': [{'week': 3, 'section': 1}, {'week': 3, 'section': 2}, {'week': 3, 'section': 3}, {'week': 3, 'section': 4},
          {'week': 2, 'section': 5}, {'week': 2, 'section': 6}, {'week': 2, 'section': 7}],
    '4': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
          {'week': 5, 'section': 3}, {'week': 5, 'section': 4}],
    '5': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
          {'week': 2, 'section': 1}, {'week': 2, 'section': 2}, {'week': 2, 'section': 3}, {'week': 2, 'section': 4},
          {'week': 5, 'section': 1}, {'week': 5, 'section': 2}],
    '6': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
          {'week': 1, 'section': 1}, {'week': 1, 'section': 2}, {'week': 1, 'section': 3}, {'week': 1, 'section': 4},
          {'week': 5, 'section': 1}, {'week': 5, 'section': 2}],
    '7': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
          {'week': 5, 'section': 1}, {'week': 5, 'section': 2}, {'week': 5, 'section': 3}, {'week': 5, 'section': 4}],
    '9': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
          {'week': 1, 'section': 5}, {'week': 1, 'section': 6}, {'week': 1, 'section': 7}, {'week': 5, 'section': 1},
          {'week': 5, 'section': 2}],
    '8': [{'week': 3, 'section': 5}, {'week': 3, 'section': 6}, {'week': 3, 'section': 7},
          {'week': 5, 'section': 1}, {'week': 5, 'section': 2}, {'week': 5, 'section': 3}, {'week': 5, 'section': 4},
          {'week': 1, 'section': 1}, {'week': 1, 'section': 2}],
    '0': [{'week': 4, 'section': 5}, {'week': 4, 'section': 6}, {'week': 4, 'section': 7}],

}
PART_SCHEDULE = [
    # 手排课-demo
    # {'week': 2, 'section': 6, 'class': '1班', 'course': '体'},
]
LINK_COURSE_TIMES = [
    {'week': 1, 'section': 1},
    # {'week': 1, 'section': 2},
    {'week': 1, 'section': 3},
    {'week': 1, 'section': 5},
    {'week': 1, 'section': 6},
    # {'week': 1, 'section': 7},
    # {'week': 1, 'section': 8},
    {'week': 2, 'section': 1},
    # {'week': 2, 'section': 2},
    {'week': 2, 'section': 3},
    {'week': 2, 'section': 5},
    {'week': 2, 'section': 6},
    # {'week': 2, 'section': 7},
    # {'week': 2, 'section': 8},
    {'week': 3, 'section': 1},
    # {'week': 3, 'section': 2},
    {'week': 3, 'section': 3},
    {'week': 3, 'section': 5},
    {'week': 3, 'section': 6},
    # {'week': 3, 'section': 7},
    # {'week': 3, 'section': 8},
    {'week': 4, 'section': 1},
    # {'week': 4, 'section': 2},
    {'week': 4, 'section': 3},
    {'week': 4, 'section': 5},
    {'week': 4, 'section': 6},
    # {'week': 4, 'section': 7},
    # {'week': 4, 'section': 8},
    {'week': 5, 'section': 1},
    # {'week': 5, 'section': 2},
    {'week': 5, 'section': 3},
    {'week': 5, 'section': 5},
    {'week': 5, 'section': 6},
    # {'week': 5, 'section': 7},
    # {'week': 5, 'section': 8},
    {'week': 6, 'section': 1},
    # {'week': 5, 'section': 2},
    {'week': 6, 'section': 3},
    {'week': 6, 'section': 5},
    {'week': 6, 'section': 6},
    {'week': 7, 'section': 1},
    # {'week': 5, 'section': 2},
    {'week': 7, 'section': 3},
    {'week': 7, 'section': 5},
    {'week': 7, 'section': 6},
]
