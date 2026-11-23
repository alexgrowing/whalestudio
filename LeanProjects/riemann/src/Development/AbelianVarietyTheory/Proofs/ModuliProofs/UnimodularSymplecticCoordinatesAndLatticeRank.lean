import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem hermForm_self_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z : Fin g → ℂ) : (hermForm Hm z z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
    Pi.star_apply, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← h.apply j k, Complex.star_def]
  ring

theorem free_finite_finrank_of_discrete_span {La : Type} [AddCommGroup La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hd : DiscreteTopology Q.range)
    (hsp : Submodule.span ℝ (Set.range Q) = ⊤) :
    Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g := by
  set L : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    rw [hL, LinearMap.coe_range]
    exact hsp⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem unimodular_symplectic_coordinates_and_lattice_rank :
    (∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ), Function.Bijective EF → (∀ x, EF x x = 0) → Module.finrank ℤ La = 2 * g → ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La, ∀ a b, EF (bas a) (bas b) = omegaStd a b) ∧ ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧ ∀ x, EF x x = 0 := by
  refine ⟨fun La _ _ _ EF g hbij halt hrk => ?_,
    fun La _ EF g Q Hm ⟨hinj, hd, hsp, hH, _, hIm⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank (B := EF) halt hbij hrk
    have hf : IsSymplecticFamily EF (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i))
        (fun _ => 1) := hb
    classical
    refine ⟨b.equivFun.symm, fun x y => ?_⟩
    simp only [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, map_add, LinearMap.add_apply,
      map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [hf.left_left, hf.right_right, hf.left_right, hf.right_left halt, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, _root_.mul_one, mul_neg,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, omegaStd]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_discrete_span Q hinj hd hsp
    exact ⟨h1, h2, h3, fun x => by
      have e : ((EF x x : ℤ) : ℝ) = 0 := by rw [← hIm x x]; exact hermForm_self_im_eq_zero hH _
      exact_mod_cast e⟩

end GlobalTheory
