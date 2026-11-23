import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartEigenMemRange
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem eigen_pair_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (σ : OE →+* R) (a0 : OE), IsUnit (σ a0 - σ (star a0)) → ∀ u u' : Fin d → R, (∀ a, (linPart (B.A.act a)).mulVec u = σ a • u) → (∀ a, (linPart (B.A.act a)).mulVec u' = σ a • u') → ∀ w : OE, dotProduct (fun i => algebraMap R k (u i)) ((ReciprocityTheory.ChartRestriction.G.TB.bilinPart k h).mulVec ((ReciprocityTheory.ChartRestriction.G.TB.dAct k B w).mulVec (fun i => algebraMap R k (u' i)))) ∈ (algebraMap R k).range := by
  intro R _ d OE _ _ k _ _ _ B h hc σ a0 ha u u' hu hu' w
  have key : ∀ v : Fin d → R, (∀ a, (linPart (B.A.act a)).mulVec v = σ a • v) → ∀ a,
      (ReciprocityTheory.ChartRestriction.G.TB.dAct k B a).mulVec (fun i => algebraMap R k (v i)) =
        algebraMap R k (σ a) • (fun i => algebraMap R k (v i)) := by
    intro v hv a
    funext i
    have e := congrArg (algebraMap R k) (congrFun (hv a) i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, linPart,
      Matrix.of_apply] at e ⊢
    rw [← e]
    rfl
  have h3 := GlobalTheory.bilinPart_eigen_mem_range R d OE k B h hc a0 u u' _ _ (key u hu a0) (key u' hu' (star a0)) ha
  rw [key u' hu' w, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  exact Subring.mul_mem _ ⟨_, rfl⟩ h3

end GlobalTheory.CharDepth
