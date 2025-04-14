:x = 20
:y = 10
:z = 50
:w = :z + :x 
if (:y > :x) [
:y = 0
left :y
] else [
right 50
]
forward :y


