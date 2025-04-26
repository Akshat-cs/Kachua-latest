:x = 5
:unusedvar = 10 
:total = 0
:z =0

:y = 5
:sum = 0

repeat :x [
    :total = :total + 1  
    :z = :z + 1
    repeat :y [
    :sum = :sum + 1  
    :z = :z + 1
    ]
]

forward :total