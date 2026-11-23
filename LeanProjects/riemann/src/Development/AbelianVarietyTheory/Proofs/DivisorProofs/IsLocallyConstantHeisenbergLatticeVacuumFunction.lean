import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisLast

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.HeisLatVac

theorem lc_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IsotropicVectorExistence.main
  | exact _root_.GlobalTheory.IsotropicVectorExistence.main
  | (apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsotropicVectorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsotropicVectorExistence.main ..)

theorem lc_exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀) : ∃ U₀ : OpenAddSubgroup K, ∀ t ∈ U₀, ψ₀ t = 1 := by
  have hV : {t : K | ‖ψ₀ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => lc_pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem lc_val {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dif_pos h]
  obtain ⟨hw, hwe⟩ := h.choose_spec
  generalize h.choose = w at hw hwe ⊢
  have h1 : w.1 = u.1 := (add_left_cancel hwe).symm
  have hyΛ : ((0 : κ → K), w.2 - u.2) ∈ Λ := by
    have e : ((0 : κ → K), w.2 - u.2) = w - u := Prod.ext (by simp [h1]) rfl
    rw [e]; exact Λ.sub_mem hw hu
  have hwu : w = u + (0, w.2 - u.2) := Prod.ext (by simp [h1]) (by simp)
  have e2 : χ w = χ u * χ (0, w.2 - u.2) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ (w.2 - u.2) - (0 : κ → K) ⬝ᵥ u.2)) := by
    conv_lhs => rw [hwu]
    exact hco u hu _ hyΛ
  rw [e2, hy _ hyΛ, h1, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [zero_dotProduct, sub_zero, dotProduct_sub]
  ring

theorem isLocallyConstant_vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] [TopologicalSpace K]
    [IsTopologicalRing K] [NonarchimedeanAddGroup K] (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (hΛ : IsOpen (Λ : Set ((κ → K) × (κ → K))))
    (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) : IsLocallyConstant (vacFn ψ₀ Λ χ x₀) := by
  obtain ⟨U₀, hU₀⟩ := lc_exists_open_ker ψ₀ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have hN : {s : κ → K | (⅟(2 : K) • s, (0 : κ → K)) ∈ Λ ∧ s ⬝ᵥ u.2 ∈ (U₀ : Set K)} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds ?_ ?_
      · refine (hΛ.preimage ?_).inter (U₀.isOpen.preimage ?_)
        · exact (continuous_id.const_smul (⅟(2 : K))).prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K))
        · exact continuous_id.dotProduct continuous_const
      · refine ⟨?_, ?_⟩
        · show (⅟(2 : K) • (0 : κ → K), (0 : κ → K)) ∈ Λ
          rw [smul_zero, Prod.mk_zero_zero]; exact Λ.zero_mem
        · show (0 : κ → K) ⬝ᵥ u.2 ∈ (U₀ : Set K)
          rw [zero_dotProduct]; exact U₀.zero_mem
    filter_upwards [hN] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : (s, (0 : κ → K)) ∈ Λ := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact Λ.add_mem hs1 hs1
    have hχs : χ (s, 0) = 1 := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact h2 _ hs1
    have hx' : x₀ + u.1 + s = x₀ + (u + (s, 0)).1 := by simp [add_assoc]
    have hneg : ψ₀ (-(s ⬝ᵥ u.2)) = 1 := hU₀ _ (U₀.neg_mem hs2)
    rw [hx', lc_val ψ₀ Λ χ x₀ hco hy _ (Λ.add_mem hu hs0), lc_val ψ₀ Λ χ x₀ hco hy u hu,
      hco u hu _ hs0, hχs, mul_one, mul_assoc, ← AddChar.map_add_eq_mul]
    have key : ⅟(2 : K) * (u.1 ⬝ᵥ (s, (0 : κ → K)).2 - (s, (0 : κ → K)).1 ⬝ᵥ u.2) +
        (-(x₀ ⬝ᵥ (u + (s, 0)).2) - ⅟(2 : K) * ((u + (s, 0)).1 ⬝ᵥ (u + (s, 0)).2)) =
        -(s ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, add_zero, dotProduct_zero, add_dotProduct]
      linear_combination (-(s ⬝ᵥ u.2)) * (invOf_two_add_invOf_two : ⅟(2 : K) + ⅟(2 : K) = 1)
    rw [key, AddChar.map_add_eq_mul, hneg, one_mul]
  · have h0 : vacFn ψ₀ Λ χ x₀ x = 0 := by rw [vacFn, dif_neg hx]
    have hN : {s : κ → K | (s, (0 : κ → K)) ∈ Λ} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds (hΛ.preimage (continuous_id.prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K)))) ?_
      show ((0 : κ → K), (0 : κ → K)) ∈ Λ
      rw [Prod.mk_zero_zero]; exact Λ.zero_mem
    filter_upwards [hN] with s hs
    rw [h0, vacFn, dif_neg]
    rintro ⟨u, hu, e⟩
    refine hx ⟨u - (s, 0), Λ.sub_mem hu hs, ?_⟩
    simp only [Prod.fst_sub]
    rw [← add_sub_assoc, ← e, add_sub_cancel_right]

end GlobalTheory.HeisLatVac

open GlobalTheory.HeisLatVac in

theorem GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  intro F _ _ v κ _ ψ₀ hψ Λ hΛ χ x₀ hco hy h2
  exact isLocallyConstant_vacFn ψ₀ hψ Λ hΛ χ x₀ hco hy h2
