import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActioStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

theorem DivOrder.mul_comm_of_eq_int {O : Type} [Ring O] {x y : O} {c : ℤ}
    (htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a))
    (hxy : x * y = (c : O))
    (hy : ∀ y : O, y ≠ 0 → ∃ w : O, ∃ c' : ℤ, c' ≠ 0 ∧ y * w = (c' : O)) :
    y * x = (c : O) := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [mul_zero] at hxy
    rw [zero_mul, hxy]
  obtain ⟨w, c', hc', hyw⟩ := hy y hy0
  have h1 : (c : O) * w = (c' : O) * x := by
    have : x * (y * w) = (x * y) * w := (_root_.mul_assoc _ _ _).symm
    rw [hyw, hxy, ← Int.cast_comm] at this
    exact this.symm
  have h2 : (c' : O) * (y * x) = (c' : O) * (c : O) := by
    calc (c' : O) * (y * x) = y * ((c' : O) * x) := (Int.cast_commute c' y).left_comm x
      _ = y * ((c : O) * w) := by rw [h1]
      _ = (c : O) * (y * w) := ((Int.cast_commute c y).left_comm w).symm
      _ = (c' : O) * (c : O) := by rw [hyw, Int.cast_comm]
  have h3 : c' • (y * x) = c' • (c : O) := by
    simpa [zsmul_eq_mul] using h2
  exact htf c' hc' h3

theorem DivOrder.exists_zsmul_eq_tmul (O : Type) [Ring O] (z : ℚ ⊗[ℤ] O) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x : O, n • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨(q.den : ℤ), by exact_mod_cast q.den_nz, q.num • o, ?_⟩
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    congr 1
    rw [zsmul_eq_mul, zsmul_eq_mul, _root_.mul_one]
    push_cast
    exact Rat.den_mul_eq_num q
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨n₁, hn₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, hn₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, n₂ • x₁ + n₁ • x₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, e₁, mul_comm, mul_smul, e₂, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem DivOrder.isUnit_of_ne_zero (O : Type) [Ring O] [Module.Free ℤ O]
    (hdiv : ∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O))
    (z : ℚ ⊗[ℤ] O) (hz : z ≠ 0) : IsUnit z := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have htf : ∀ n : ℤ, n ≠ 0 → Function.Injective (fun a : O => n • a) := by
    intro n hn a b hab
    apply hinj
    have h' : (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] a) = (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] b) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_smul]
      exact congrArg _ hab
    exact smul_right_injective _ (by exact_mod_cast hn : (n : ℚ) ≠ 0) h'
  obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
  have hx : x ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, ← Int.cast_smul_eq_zsmul ℚ] at e
    exact hz ((smul_eq_zero.mp e).resolve_left (by exact_mod_cast hn))
  obtain ⟨y, c, hc, hxy⟩ := hdiv x hx
  have hyx : y * x = (c : O) := DivOrder.mul_comm_of_eq_int htf hxy hdiv
  set jj : O →ₐ[ℤ] ℚ ⊗[ℤ] O := Algebra.TensorProduct.includeRight with hjj
  have hjx : IsUnit (jj x) := by
    rw [isUnit_iff_exists]
    refine ⟨algebraMap ℚ _ ((c : ℚ)⁻¹) * jj y, ?_, ?_⟩
    · rw [Algebra.left_comm, ← map_mul, hxy, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
    · rw [_root_.mul_assoc, ← map_mul, hyx, map_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] O)),
        ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one]
  have hz' : z = algebraMap ℚ _ ((n : ℚ)⁻¹) * jj x := by
    have : jj x = (1 : ℚ) ⊗ₜ[ℤ] x := rfl
    rw [← Algebra.smul_def, this, ← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [hz']
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hn))).map _).mul hjx

theorem potModel_of_intDivOrder_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hsm O _ _ _ act hmon h1 hmul hadd hdiv hg
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℚ).injective_int
  have hspan : Submodule.span ℚ (Set.range
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨n, hn, x, e⟩ := DivOrder.exists_zsmul_eq_tmul O z
    have hz : z = ((n : ℚ)⁻¹) • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
      rw [← e, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
        one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hrank : Module.finrank ℚ (ℚ ⊗[ℤ] O) = Module.finrank ℤ O := Module.finrank_baseChange
  exact GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_leftAction V K A g hA hsm O act hmon h1 hmul hadd (ℚ ⊗[ℤ] O)
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom
    (DivOrder.isUnit_of_ne_zero O hdiv) hinj hspan (hrank ▸ hg)

end GlobalTheory
