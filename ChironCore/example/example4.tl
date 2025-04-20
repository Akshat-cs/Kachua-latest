:x = 20
:y = 10
:z = 30     

pendown
forward :x  
:w = :x + 5  

if (:x > :y) [
  :a = 50   
  :x = 40 
  :y = 20
  right 90
] else [
  :b = 60    
  left 90
]

:c = :x * :y  
:d = :c + 10  

forward :y    

:result = 100 
penup