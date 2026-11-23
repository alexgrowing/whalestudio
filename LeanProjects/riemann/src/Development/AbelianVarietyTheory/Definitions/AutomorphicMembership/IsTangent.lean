import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F] (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (w : Fin n → Y.Fn) (c : Fin Y.dim → Fin n → 𝓞 E)

def GeomPt : Type :=
  {y : Sp (AlgebraicClosure E) ⟶ Y.X // y ≫ Y.str = spMap ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))}

def GenAt (x : Y.X) (k : Fin n) : Prop := w k ≠ 0 ∧ ∀ l, RegAt x (w l / w k)

def coef (i : Fin Y.dim) (l : Fin n) : AlgebraicClosure E := algebraMap E _ (c i l : E)

def cutSet : Set (GeomPt Y E) :=
  {y | ∀ k, GenAt Y w (below y.1) k → ∀ i, ∑ l, coef Y E c i l * valAt y.1 (w l / w k) = 0}

def IsTangent (y : GeomPt Y E) (δ : Y.X.presheaf.stalk (below y.1) →+ AlgebraicClosure E) : Prop :=
  (∀ a b, δ (a * b) = (Scheme.stalkClosedPointTo y.1).hom a * δ b + (Scheme.stalkClosedPointTo y.1).hom b * δ a) ∧
    ∀ (a : Y.X.presheaf.stalk (below y.1)) (t : F), algebraMap _ Y.Fn a = algebraMap F Y.Fn t → δ a = 0

def ReducedAt (y : GeomPt Y E) : Prop :=
  ∀ k, GenAt Y w (below y.1) k → ∀ u : Fin n → Y.X.presheaf.stalk (below y.1),
    (∀ l, algebraMap _ Y.Fn (u l) = w l / w k) → ∀ δ, IsTangent Y E y δ →
      (∀ i, ∑ l, coef Y E c i l * δ (u l) = 0) → δ = 0

def cutGood (bd : Y.Cl) : Prop :=
  (∀ x, ∃ k, GenAt Y w x k) ∧ (cutSet Y E w c).Finite ∧
    ∀ y ∈ cutSet Y E w c, ReducedAt Y E w c y ∧ below y.1 ∉ bd

def cutHt {C : CxSt F} (A : Adl C Y) : ℝ := ∑ᶠ y ∈ cutSet Y E w c, A.ht (below y.1)

def cutOrd (Δ : Y.Dv) (f : Y.Fn) : ℕ :=
  sSup {a : ℕ | ∀ y ∈ cutSet Y E w c, ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
    algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn)}

def cutSt [StarRing F] (C : CxSt F) : CutSt C where
  cutGood := fun Y bd E _ _ _ _ w c => cutGood Y E w c bd
  cutHt := fun Y A E _ _ _ _ w c => cutHt Y E w c A
  cutOrd := fun Y E _ _ _ _ w c Δ f => cutOrd Y E w c Δ f

end GlobalTheory.TrueGeo
