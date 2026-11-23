import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV

section Generic

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def AdForms (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) : Submodule ℂ (G → W) where
  carrier := {F | ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h)}
  add_mem' := by
    intro F F' hF hF' γ h k
    simp only [Pi.add_apply, hF γ h k, hF' γ h k, map_add, smul_add]
  zero_mem' := by
    intro γ h k
    simp
  smul_mem' := by
    intro a F hF γ h k
    simp only [Pi.smul_apply, hF γ h k, map_smul]
    rw [smul_comm]

def stab (J : Subgroup G) (y : G) : Subgroup Γ := J.comap ((MulAut.conj y⁻¹).toMonoidHom.comp ι)

theorem mem_stab {J : Subgroup G} {y : G} {γ : Γ} : γ ∈ stab ι J y ↔ y⁻¹ * ι γ * y ∈ J := by
  simp [stab, MulAut.conj_apply]

def stabK {J : Subgroup G} {y : G} (γ : stab ι J y) : J :=
  ⟨(y⁻¹ * ι (γ : Γ) * y)⁻¹, J.inv_mem ((mem_stab ι).1 γ.2)⟩

theorem stabK_spec {J : Subgroup G} {y : G} (γ : stab ι J y) : ι (γ : Γ) * y * (stabK ι γ : G) = y := by
  simp only [stabK]
  group

def IsReps (J : Subgroup G) {I : Type} (y : I → G) : Prop :=
  ∀ h : G, ∃! i : I, ∃ (γ : Γ) (k : J), h = ι γ * y i * k

def adInner (J : Subgroup G) {I : Type} [Fintype I] (y : I → G) (F F' : G → W) : ℂ :=
  ∑ i, ((Nat.card (stab ι J (y i)) : ℂ))⁻¹ * inner ℂ (F (y i)) (F' (y i))

def g0Act {Q : Subgroup G} (ch : Q →* ℂˣ) (κ : Q) (F : G → W) : G → W :=
  fun h => (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : G))

def dcOp (A : Finset G) (F : G → W) : G → W := fun h => ∑ a ∈ A, F (h * a)

def IsDC (J : Subgroup G) (x : G) (A : Finset G) : Prop :=
  (∀ a ∈ A, ∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) ∧
    ∀ g : G, (∃ k₁ k₂ : J, g = (k₁ : G) * x * k₂) → ∃! a, a ∈ A ∧ a⁻¹ * g ∈ J

end Generic

section Pres

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure ClassPres (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) where

  y : S.Cl → G
  reps : IsReps ι J y

  stabI : ∀ c, S.Gam c ≃* stab ι J (y c)

  coef : S.V →ₛₗ[σ] W
  coef_li : LinearIndependent ℂ fun i => coef (S.bV i)
  coef_span : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤

  coef_pair : ∀ x x' : S.V, inner ℂ (coef x) (coef x') = σ (S.pair x x')

  coef_act : ∀ c (g : S.Gam c) (x : S.V),
    coef (S.ρ c g x) = (χ (stabK ι (stabI c g)) : ℂ) • ρ (stabI c g : Γ) (coef x)

namespace ClassPres

variable {ι} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
  (P : ClassPres ι S σ ρ J χ)

def decC (h : G) : S.Cl := (P.reps h).exists.choose

def decG (h : G) : Γ := (P.reps h).exists.choose_spec.choose

def decK (h : G) : J := (P.reps h).exists.choose_spec.choose_spec.choose

theorem dec_spec (h : G) : h = ι (P.decG h) * P.y (P.decC h) * (P.decK h : G) := by
  exact (P.reps h).exists.choose_spec.choose_spec.choose_spec

def ext (f : S.Cl → S.V) : G → W :=
  fun h => (χ (P.decK h) : ℂ) • ρ (P.decG h) (P.coef (f (P.decC h)))

def extL : S.Forms →ₛₗ[σ] (G → W) where
  toFun f := P.ext f
  map_add' := by
    intro f f'
    funext h
    simp only [ext, Submodule.coe_add, Pi.add_apply, map_add, smul_add]
  map_smul' := by
    intro a f
    funext h
    simp only [ext, Submodule.coe_smul, Pi.smul_apply, map_smulₛₗ, Pi.smul_apply, RingHom.id_apply]
    rw [smul_comm]

theorem extL_apply (f : S.Forms) : P.extL f = P.ext f := rfl

end ClassPres

structure ActTie {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : ClassPres ι S σ ρ J χ) (Q : Subgroup G) (ch : Q →* ℂˣ) {G0 : Type} [Group G0]
    (act : Representation K G0 S.Forms) where
  red : Q →* G0
  red_surj : Function.Surjective red
  red_ker : ∀ q : Q, red q = 1 ↔ (q : G) ∈ J
  act_eq : ∀ (g : G0) (κ : Q), red κ = g → ∀ f : S.Forms,
    P.ext ((act g f : S.Forms) : S.Cl → S.V) = g0Act ch κ (P.ext (f : S.Cl → S.V))

structure HeckeTie {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : ClassPres ι S σ ρ J χ) {I : Type} (op : I → Module.End K S.Forms) (inR : I → Prop)
    (isT isLoc : I → G → Prop) where
  hx : I → G
  hA : I → Finset G
  hx_ok : ∀ i, inR i → isT i (hx i)
  hA_loc : ∀ i, inR i → ∀ a ∈ hA i, isLoc i a
  chi_loc : ∀ i, inR i → ∀ k : J, isLoc i k → χ k = 1
  hDC : ∀ i, inR i → IsDC J (hx i) (hA i)
  op_eq : ∀ i, inR i → ∀ f : S.Forms,
    P.ext ((op i f : S.Cl → S.V) : S.Cl → S.V) = dcOp (hA i) (P.ext (f : S.Cl → S.V))

structure CoefDatG (Γ : Type) [Group Γ] where
  W : Type
  [nW : NormedAddCommGroup W]
  [iW : InnerProductSpace ℂ W]
  ρ : Γ →* Module.End ℂ W

attribute [instance] CoefDatG.nW CoefDatG.iW

structure LevDatG (G : Type) [Group G] where
  J : Subgroup G
  χ : J →* ℂˣ
  Q : Subgroup G
  J_le : J ≤ Q
  ch : Q →* ℂˣ
  ch_J : ∀ k : J, ch ⟨k, J_le k.2⟩ = χ k

structure SideEnvG (G Γ : Type) [Group G] [Group Γ] (I : Type) where
  coef : CoefDatG Γ
  lev : LevDatG G
  isT : I → G → Prop
  isLoc : I → G → Prop

structure LevEnvG (G : Type) [Group G] (I : Type) where
  lev : LevDatG G
  isT : I → G → Prop
  isLoc : I → G → Prop

def envOf {G Γ : Type} [Group G] [Group Γ] {I : Type} (c : CoefDatG Γ) (l : LevEnvG G I) : SideEnvG G Γ I :=
  ⟨c, l.lev, l.isT, l.isLoc⟩

structure SideRealG {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (E : SideEnvG G Γ I)
    {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0]
    (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (inR : I → Prop) where

  pres : ClassPres ι S σ E.coef.ρ E.lev.J E.lev.χ

  act_tie : ActTie ι pres E.lev.Q E.lev.ch act

  hecke : HeckeTie ι pres op inR E.isT E.isLoc

end Pres

section Theta

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

abbrev Gf (V : Formalism.BasicNotions.TH.HSp D) := (finHom V).range

def ratF (V : Formalism.BasicNotions.TH.HSp D) : GQ V →* Gf V := (finHom V).rangeRestrict.comp (GQ V).subtype

end Theta

section Comparison₂

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G]

abbrev CoefDat (V : Formalism.BasicNotions.TH.HSp D) := CoefDatG (GQ V)

abbrev LevDat (V : Formalism.BasicNotions.TH.HSp D) := LevDatG (Gf V)

abbrev SideEnv (V : Formalism.BasicNotions.TH.HSp D) (I : Type) := SideEnvG (Gf V) (GQ V) I

abbrev LevEnv (V : Formalism.BasicNotions.TH.HSp D) (I : Type) := LevEnvG (Gf V) I

abbrev SideReal (V : Formalism.BasicNotions.TH.HSp D) {I : Type} (E : SideEnv D V I) (S : CSD D.what₂.LL)
    (act : Representation D.what₂.LL G S.Forms) (op : I → Module.End D.what₂.LL S.Forms) (deg : I → ℕ) :=
  SideRealG (ratF V) E D.what₂.embLL S act op (fun i => 1 ≤ deg i ∧ deg i ≤ V.rank)

variable {Pl0 T : Type} {m : ℕ}

structure FamReal (A : FamIn D.what₂.LL G Pl0 T m) (cR : CoefDat D D.sp.X') (cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1)))
    (lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)) (lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)) where

  R : ∀ t, SideReal D D.sp.X' (envOf cR (lR t)) (A.MtildeCSD t) (A.leftGroupActionRight t) (A.heckeR t) (fun i => i.2)

  L : ∀ (i : Fin m) t, SideReal D (D.sp.V ((i : ℕ) + 1)) (envOf (cL i) (lL i t)) (A.MtCSD i t) (A.leftGroupActionLift i t) (A.heckeL i t)
    (fun i => i.2)

  rankR : D.sp.X'.rank = A.r + m * A.t

  rankL : ∀ i : Fin m, (D.sp.V ((i : ℕ) + 1)).rank = A.r + A.t

namespace FamReal

variable {D} {A : FamIn D.what₂.LL G Pl0 T m} {cR : CoefDat D D.sp.X'} {cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1))}
  {lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
  (B : FamReal D A cR cL lR lL)

def jR (t : T) : A.fam.amb.FR t →ₛₗ[D.what₂.embLL] (Gf D.sp.X' → cR.W) := (B.R t).pres.extL

def jL (i : Fin m) (t : T) : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] (Gf (D.sp.V ((i : ℕ) + 1)) → (cL i).W) :=
  (B.L i t).pres.extL

def imR (t : T) (Z : Submodule D.what₂.LL (A.fam.amb.FR t)) : Submodule ℂ (Gf D.sp.X' → cR.W) :=
  Submodule.span ℂ (B.jR t '' Z)

def imL (i : Fin m) (t : T) (Z : Submodule D.what₂.LL (A.fam.amb.FL i t)) :
    Submodule ℂ (Gf (D.sp.V ((i : ℕ) + 1)) → (cL i).W) :=
  Submodule.span ℂ (B.jL i t '' Z)

def partR (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : Formalism.L2.Indef.DefSub A.fam.amb) (t : T) (p : A.fam.base.Ix) :
    Submodule ℂ (Gf D.sp.X' → cR.W) :=
  Submodule.span ℂ ((fun x : Fin ((A.side P ψ Zs).dQ t) → D.what₂.LL => B.jR t ((A.fam.R t).toF (A.fam.lvl P ψ) (Zs.Z t) x)) ''
    ((A.side P ψ Zs).Qp t p : Set _))

def partL (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : Formalism.L2.Indef.DefSub A.fam.amb) (i : Fin m) (t : T) (p : A.fam.base.Ix) :
    Submodule ℂ (Gf (D.sp.V ((i : ℕ) + 1)) → (cL i).W) :=
  Submodule.span ℂ ((fun x : Fin ((A.side P ψ Zs).dZ i t) → D.what₂.LL => B.jL i t ((A.fam.L i t).toF (A.fam.lvlA P ψ) (Zs.Zl i t) x)) ''
    ((A.side P ψ Zs).Zp i t p : Set _))

end FamReal

def Realised (A : FamIn D.what₂.LL G Pl0 T m) (cR : CoefDat D D.sp.X') (cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1)))
    (lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)) (lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)) : Prop :=
  Nonempty (FamReal D A cR cL lR lL)

end Comparison₂

section Props

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]

def ClassPres.ExtMem {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : ClassPres ι S σ ρ J χ) : Prop :=
  ∀ f : S.Forms, P.ext f ∈ AdForms ι ρ J χ

def ClassPres.ExtBij {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : ClassPres ι S σ ρ J χ) : Prop :=
  LinearIndependent ℂ (fun i => P.extL (S.basis i)) ∧ Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ

def ClassPres.Isom {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : ClassPres ι S σ ρ J χ) : Prop :=
  ∀ f f' : S.Forms, adInner ι J P.y (P.ext f) (P.ext f') = σ (S.csum f f')

def AdInnerIndep (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) : Prop :=
  (∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') → (∀ k, ‖(χ k : ℂ)‖ = 1) →
    ∀ (I I' : Type) [Fintype I] [Fintype I'] (y : I → G) (y' : I' → G), IsReps ι J y → IsReps ι J y' →
      ∀ F ∈ AdForms ι ρ J χ, ∀ F' ∈ AdForms ι ρ J χ, adInner ι J y F F' = adInner ι J y' F F'

def LiftIndependentAction (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) {Q : Subgroup G} {G0 : Type}
    [Group G0] (red : Q →* G0) (ch : Q →* ℂˣ) : Prop :=
  ∀ (hJ : J ≤ Q), (∀ q : Q, red q = 1 ↔ (q : G) ∈ J) → (∀ k : J, ch ⟨k, hJ k.2⟩ = χ k) →
    ∀ κ κ' : Q, red κ = red κ' → ∀ F ∈ AdForms ι ρ J χ, ∀ h,
      (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ) = (((ch κ')⁻¹ : ℂˣ) : ℂ) • F (h * κ')

end Props

end Formalism.IndefR.Bridge
