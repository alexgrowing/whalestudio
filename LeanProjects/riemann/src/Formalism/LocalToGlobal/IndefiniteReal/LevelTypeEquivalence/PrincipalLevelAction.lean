import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def principalLevelAction (g : G) : (GA D (Yc D 0) → ℂ) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)

def actYt (t : T) (j : ℕ) (g : G) : (GA D (Yc D j) → ℂ) →ₗ[ℂ] (GA D (Yc D j) → ℂ) :=
  actL (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.eG g)

def actX (t : T) (g : G) : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) := actL D.sp.X' R.βX (R.datXt t) (R.eG g)

def actW (i : Fin D.R.m) (g : G) : (GA D (Wc D i) → ℂ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)

def fX (t : T) : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def GUnitC : Prop := ∀ (g : G) (x y : R.HE.H), inner ℂ (R.gE g x) (R.gE g y) = inner ℂ x y

def GEquivC : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), R.Th t (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) = R.gE g (R.Th t (R.jX t x))

def LevTypeC (b : Bool) : Prop :=
  ∀ x : R.HE.H, R.HE.e x ∈ R.EEat (R.levR F b) ↔
    ∀ h : (F.lvl b).P, R.gE (h : G) x = D.what₂.embLL (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • x

def GUnitLC : Prop :=
  ∀ i (g : G) (x y : (R.HW i (sg0 D A)).H), inner ℂ (R.gW i (sg0 D A) g x) (R.gW i (sg0 D A) g y) = inner ℂ x y

def GEquivLC : Prop :=
  ∀ i t (g : G) (x : A.fam.amb.FL i t),
    R.thG i t (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t x))

def LevTypeLC (b : Bool) : Prop :=
  ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i (sg0 D A)).e x ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ↔
    (R.HW i (sg0 D A)).e x ∈ R.Wat i (sg0 D A) R.triv ∧
      ∀ h : (F.lvl b).P, R.gW i (sg0 D A) (h : G) x = sg0 D A ((((F.lvl b).ψ h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • x

def LiftsAll : Prop :=
  LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) ∧
    (∀ t j, j < D.R.m → LiftsExist (Yc D j) (R.βY j) (R.datYt t j R.triv)) ∧
    (∀ t, LiftsExist D.sp.X' R.βX (R.datXt t)) ∧
    (∀ i, LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)) ∧
    (∀ i t, LiftsExist (Vc D i) (R.βV i) (R.datVt i t))

variable {R} in

def IrrX (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop := ∀ χ ∈ A.X, IsAbsIrrChar χ

def MultAdd {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∀ T T' : MMap M, IsMultMap θ M J χ T → IsMultMap θ M J χ T' → IsMultMap θ M J χ (T + T')

def ActTieX : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), fX R t (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) = actX R t g ∘ₗ fX R t (R.jX t x)

def EquivIoX : Prop :=
  ∀ t (g : G) (F F' : LinearMap.range (fX R t)),
    (F' : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) = actX R t g ∘ₗ (F : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) →
      ((R.ioX t F' : R.CC t (D.R.m - 1)) : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) =
        actYt R t (D.R.m - 1) g ∘ₗ
          ((R.ioX t F : R.CC t (D.R.m - 1)) : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ))

def EquivIoY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ (g : G) (F F' : R.CC t (k + 1)),
    (F' : SmT (R.MY (k + 1)) →ₗ[ℂ] (GA D (Yc D (k + 1)) → ℂ)) =
        actYt R t (k + 1) g ∘ₗ (F : SmT (R.MY (k + 1)) →ₗ[ℂ] (GA D (Yc D (k + 1)) → ℂ)) →
      ((R.ioY t k F' : R.CC t k) : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ)) =
        actYt R t k g ∘ₗ ((R.ioY t k F : R.CC t k) : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ))

def ThFEquiv : Prop :=
  ∀ i t (g : G) (x : A.fam.amb.FL i t),
    R.thF i t (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) = postOn (R.MW i (sg0 D A)) (actW R i g) (R.thF i t (R.jV i t x))

def GUnitOf : Prop := R.IsModels → LiftsAll R → UnimodGA (Yc D 0) → GUnitC R

def GEquivOf : Prop :=
  R.IsModels → R.IsChain → LiftsAll R → IrrX A → ActTieX R → EquivIoX R → EquivIoY R → GEquivC R

def LevTypeOf (b : Bool) : Prop :=
  R.IsModels → LiftsAll R →
    MultAdd R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) →
      LevTypeC R F b

def GUnitLOf : Prop := R.IsModels → LiftsAll R → (∀ i, UnimodGA (Wc D i)) → GUnitLC R

def GEquivLOf : Prop := R.IsModels → R.IsThP → LiftsAll R → IrrX A → ThFEquiv R → GEquivLC R

def LevTypeLOf (b : Bool) : Prop :=
  R.IsModels → LiftsAll R →
    (∀ i, MultAdd R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))) →
      LevTypeLC R F b

end Defs

end Formalism.IndefR.Eqv.Act

end
