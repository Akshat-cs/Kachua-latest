:size = 100
:angle = 144
:iterations = 5

:deadbase = 17

penup
goto(0, 0)
pendown

:heavycomputation = 0

repeat 5000 [
  :heavycomputation = :heavycomputation + :deadbase
  :heavycomputation = :heavycomputation * :deadbase
  :heavycomputation = :heavycomputation / (:deadbase - 10)
]

repeat :iterations [
  forward(:size)
  right(:angle)
  
  :heavyloop = 0
  repeat 500 [
    :heavyloop = :heavyloop + :heavycomputation
    :heavyloop = :heavyloop * 10
    :heavyloop = :heavyloop / 9
  ]
]

:results = 0
:flag = 0

if (:flag > 0) [
  repeat 1000 [
    :results = :results + :heavycomputation
    :results = :results * :heavyloop
    :results = :results / :deadbase
  ]
]

penup
goto(-150, -150)
pendown

:sides = 6
:radius = 100
:interior = 360 / :sides

:deadcalculation = 0
repeat 5000 [
  :deadcalculation = :deadcalculation + :heavycomputation
  :deadcalculation = :deadcalculation * :results
  :deadcalculation = :deadcalculation / (:deadbase + 5)
]

repeat :sides [
  :heavyside = 0
  repeat 1000 [
    :heavyside = :heavyside + :deadcalculation
    :heavyside = :heavyside * :sides
    :heavyside = :heavyside / (:sides - 1)
  ]
  
  forward(:radius)
  right(:interior)
]

:finalresult = :heavycomputation + :heavyloop + :results + :deadcalculation + :heavyside

penup