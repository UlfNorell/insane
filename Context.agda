
data Cxt [ Ty : Cxt Ty -> Set ] : Set where
  nil  : Cxt Ty
  snoc : (G : Cxt Ty) -> Ty G -> Cxt Ty

-- Cons-based context extension
data Ext [ Ty : Cxt Ty -> Set ] (G : Cxt Ty) : Set where
  nilE  : Ext Ty G
  consE : (a : Ty G) -> Ext Ty (snoc Ty G a) -> Ext Ty G

append : [ Ty : Cxt Ty -> Set ] -> (G : Cxt Ty) -> Ext Ty G -> Cxt Ty
append Ty G nilE = G
append Ty G (consE a D) = append Ty (snoc Ty G a) D

-- Snoc-based context extension
data ExtR [ Ty : Cxt Ty -> Set ] (G : Cxt Ty) : Set where
  nilR  : ExtR Ty G
  snocR : (E : ExtR Ty G) -> Ty (appendR Ty G E) -> ExtR Ty G

appendR : [ Ty : Cxt Ty -> Set ] -> (G : Cxt Ty) -> ExtR Ty G -> Cxt Ty
appendR Ty G nilR = G
appendR Ty G (snocR E a) = snoc Ty (appendR Ty G E) a

