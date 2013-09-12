
data Cxt [ Ty : Cxt Ty -> Set ] : Set where
  nil  : Cxt Ty
  snoc : (G : Cxt Ty) -> Ty G -> Cxt Ty

data Ext [ Ty : Cxt Ty -> Set ] (G : Cxt Ty) : Set where
  nilE  : Ext Ty G
  consE : (a : Ty G) -> Ext Ty (snoc Ty G a) -> Ext Ty G

append : [ Ty : Cxt Ty -> Set ] -> (G : Cxt Ty) -> Ext Ty G -> Cxt Ty
append Ty G nilE = G
append Ty G (consE a D) = append Ty (snoc Ty G a) D

