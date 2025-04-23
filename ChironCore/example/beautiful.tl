penup
goto (-60, 0)
pendown
backward 50
left 90
forward 50
right 90
forward 50
penup

:deadvar = 5

if (5 > 3)[
  :deadvar = 6
] else [
  :deadvar = 7
]

goto (-40, 0)
pendown
forward 50
left 90
forward 25
left 90
forward 50
right 90
forward 25
right 90
forward 50
penup

goto (20, 25)
pendown
forward 10
penup

goto (30, 0)
pendown
forward 50
left 90
forward 25
left 90
forward 35
backward 35
right 90
forward 25
left 90
forward 50
penup

goto (100, 0)
pendown
right 180
forward 50
left 90
forward 25
left 90
forward 35
backward 35
right 90
forward 25
left 90
forward 50
penup

goto (175, 0)
pendown
right 180
forward 50
left 90
forward 25
left 90
forward 50
right 90
forward 25
right 90
forward 50
penup