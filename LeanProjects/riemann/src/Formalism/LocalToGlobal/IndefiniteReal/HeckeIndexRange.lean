import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.LocalToGlobal.Divisibility.HeckeRI
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV

section Comap

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]

def HeckeTie.comap {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    {P : ClassPres ι S σ ρ J χ} {I : Type} {op : I → Module.End K S.Forms} {inR : I → Prop} {isT isLoc : I → G → Prop}
    (H : HeckeTie ι P op inR isT isLoc) {I' : Type} (f : I' → I) :
    HeckeTie ι P (op ∘ f) (inR ∘ f) (isT ∘ f) (isLoc ∘ f) where
  hx := H.hx ∘ f
  hA := H.hA ∘ f
  hx_ok := fun i h => H.hx_ok (f i) h
  hA_loc := fun i h => H.hA_loc (f i) h
  chi_loc := fun i h => H.chi_loc (f i) h
  hDC := fun i h => H.hDC (f i) h
  op_eq := fun i h => H.op_eq (f i) h

def LevEnvG.comap {I : Type} (l : LevEnvG G I) {I' : Type} (f : I' → I) : LevEnvG G I' :=
  ⟨l.lev, l.isT ∘ f, l.isLoc ∘ f⟩

def SideRealG.comap {I : Type} {c : CoefDatG Γ} {l : LevEnvG G I} {σ : K →+* ℂ} {S : CSD K} {G0 : Type} [Group G0]
    {act : Representation K G0 S.Forms} {op : I → Module.End K S.Forms} {inR : I → Prop}
    (R : SideRealG ι (envOf c l) σ S act op inR) {I' : Type} (f : I' → I) :
    SideRealG ι (envOf c (l.comap f)) σ S act (op ∘ f) (inR ∘ f) where
  pres := R.pres
  act_tie := R.act_tie
  hecke := R.hecke.comap f

end Comap

section Tie3

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

def heckeIndexRange {P Q : Type} (n : ℕ) (tyOk : ℕ → Ty → Prop) : (P × ℕ) ⊕ (Q × Ty) → Prop :=
  Sum.elim (fun i => 1 ≤ i.2 ∧ i.2 ≤ n) (fun i => tyOk n i.2)

structure FamReal3K {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A3 : FamIn3 K G Pl0 I0 Ty T m)
    (tyOk : ℕ → Ty → Prop) (cR : CoefDat D D.sp.X') (cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1)))
    (lR : ∀ t, LevEnv D D.sp.X' ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty)))
    (lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty))) where

  R : ∀ t, SideRealG (ratF D.sp.X') (envOf cR (lR t)) σ (A3.A.MtildeCSD t) (A3.A.leftGroupActionRight t)
    (Sum.elim (A3.A.heckeR t) (A3.heckeRI t)) (heckeIndexRange D.sp.X'.rank tyOk)

  L : ∀ (i : Fin m) t, SideRealG (ratF (D.sp.V ((i : ℕ) + 1))) (envOf (cL i) (lL i t)) σ (A3.A.MtCSD i t)
    (A3.A.leftGroupActionLift i t) (Sum.elim (A3.A.heckeL i t) (A3.heckeLI i t)) (heckeIndexRange (D.sp.V ((i : ℕ) + 1)).rank tyOk)

  rankR : D.sp.X'.rank = A3.A.r + m * A3.A.t

  rankL : ∀ i : Fin m, (D.sp.V ((i : ℕ) + 1)).rank = A3.A.r + A3.A.t

abbrev FamReal3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (tyOk : ℕ → Ty → Prop) (cR : CoefDat D D.sp.X')
    (cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1)))
    (lR : ∀ t, LevEnv D D.sp.X' ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty)))
    (lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty))) :=
  FamReal3K D D.what₂.embLL A3 tyOk cR cL lR lL

def Realised3K {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A3 : FamIn3 K G Pl0 I0 Ty T m)
    (tyOk : ℕ → Ty → Prop) (cR : CoefDat D D.sp.X') (cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1)))
    (lR : ∀ t, LevEnv D D.sp.X' ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty)))
    (lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty))) : Prop :=
  Nonempty (FamReal3K D σ A3 tyOk cR cL lR lL)

variable {D} {A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m} {tyOk : ℕ → Ty → Prop} {cR : CoefDat D D.sp.X'}
  {cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1))}
  {lR : ∀ t, LevEnv D D.sp.X' ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty))}
  {lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty))}

def FamReal3.toFamReal (B : FamReal3 D A3 tyOk cR cL lR lL) :
    FamReal D A3.A cR cL (fun t => (lR t).comap Sum.inl) (fun i t => (lL i t).comap Sum.inl) where
  R := fun t => (B.R t).comap Sum.inl
  L := fun i t => (B.L i t).comap Sum.inl
  rankR := B.rankR
  rankL := B.rankL

def Realised3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (tyOk : ℕ → Ty → Prop) (cR : CoefDat D D.sp.X')
    (cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1)))
    (lR : ∀ t, LevEnv D D.sp.X' ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty)))
    (lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) ((A3.A.ok t × ℕ) ⊕ (A3.okI t × Ty))) : Prop :=
  Nonempty (FamReal3 D A3 tyOk cR cL lR lL)

def InertOff (P : Pl D.host.E) (S : Set (Pl D.host.E)) : Prop :=
  Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal ∧ P ∉ S

structure InertTie (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (plI : I0 → Pl D.host.E) (S : Set (Pl D.host.E))
    (Qt : T → Finset (Pl D.host.E)) : Prop where
  plI_inj : Function.Injective plI
  okI : ∀ t Q, Q ∈ A3.okI t ↔ InertOff (plI Q) (S ∪ (Qt t : Set (Pl D.host.E)))

end Tie3

end Formalism.IndefR.Bridge
