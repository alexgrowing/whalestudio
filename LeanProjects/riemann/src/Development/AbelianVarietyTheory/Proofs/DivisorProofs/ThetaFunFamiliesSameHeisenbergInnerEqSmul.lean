import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

open MeasureTheory

noncomputable section
open MeasureTheory

namespace GlobalTheory.ThetaSchurFam

theorem two_families_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ι : Type)
    (X Y : ι → Formalism.IndefR.Datum.WO S T → ℂ) (act : Formalism.IndefR.Datum.WO S T → ι → ι)
    (g : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T), Function.Surjective g →
    (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (X i)) → (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (Y i)) →
    (∀ w i, X (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (X i)) →
    (∀ w i, Y (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (Y i)) →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), μ.IsAddHaarMeasure →
      MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕 μ →
      (∀ i j, ∫ x in 𝓕, X i x * star (X j x) ∂μ = ∫ x in 𝓕, Y i x * star (Y j x) ∂μ) →
      ∃ c : ℂ, ∀ i, X i = c • Y i := by
  intro D ψ hψ S T ι X Y act g hg hX hY hXa hYa μ 𝓕 hμ h𝓕 hI
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hint : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
      Integrable (fun x => f x * star (f' x)) (μ.restrict 𝓕) := fun f f' hf hf' => by
    have hcont : Continuous fun x => f x * star (f' x) := hf.cont.mul hf'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hf hf' hγ w]
    exact hC _ h
  have h1 : ∀ i j x, X i x * star (X j x) = Y i x * star (Y j x) := fun i j x => by
    have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
      (fun γ x => ψ (symplO S T x γ))
      (fun γ => by
        have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
          GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
        simp only [← l4]
        exact hψ.1.1.comp (this.add this))
      (fun γ x y => by
        simp only [← l4, l1, AddChar.map_add_eq_mul]
        ring)
      (fun γ γ' x => by
        simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
        ring)
      (fun x => by
        simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
      (fun γ x => hψ.1.2.1 _)
      (fun x => by
        rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
        exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
      μ 𝓕 hμ h𝓕 (fun x => X i x * star (X j x) - Y i x * star (Y j x))
      (((hX i).cont.mul (hX j).cont.star).sub ((hY i).cont.mul (hY j).cont.star))
      (fun γ hγ x => by
        rw [GlobalTheory.ThetaSchur.prod_periodic hψ (hX i) (hX j) hγ, GlobalTheory.ThetaSchur.prod_periodic hψ (hY i) (hY j) hγ])
      (fun γ => by
        obtain ⟨w, hw⟩ := hg (γ : WO S T)
        have e : (fun x => ψ (symplO S T x γ) * (X i x * star (X j x) - Y i x * star (Y j x))) = fun x =>
            X (act w i) x * star (X j x) - Y (act w i) x * star (Y j x) := by
          funext x
          rw [hXa, hYa, hw, GlobalTheory.ThetaSchur.heisO_rat (hX i) γ.2, GlobalTheory.ThetaSchur.heisO_rat (hY i) γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hX _) (hX j)) (hint _ _ (hY _) (hY j)), hI, sub_self])
    exact sub_eq_zero.1 (congrFun key x)
  have h2 : ∀ i j x y, X i x * star (X j y) = Y i x * star (Y j y) := fun i j x y => by
    obtain ⟨w, hw⟩ := hg (y - x)
    have h := h1 i (act w j) x
    rw [hXa, hYa, hw] at h
    simp only [heisO, add_sub_cancel, star_mul'] at h
    linear_combination ψ (symplOH S T x (y - x)) * h -
      (X i x * star (X j y) - Y i x * star (Y j y)) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T x (y - x))
  by_cases h0 : ∃ j y, Y j y ≠ 0
  · obtain ⟨j, y, hy⟩ := h0
    have e1 := h2 j j y y
    have hn1 : ‖X j y‖ = ‖Y j y‖ := by
      have := congrArg norm e1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : X j y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (X j y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (Y j y) / star (X j y), fun i => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 i j x y, mul_comm]
  · push_neg at h0
    refine ⟨0, fun i => ?_⟩
    funext x
    have e1 := h2 i i x x
    rw [h0 i x, zero_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at e1
    rw [e1, Pi.smul_apply, h0 i x, smul_zero]

end GlobalTheory.ThetaSchurFam
end
