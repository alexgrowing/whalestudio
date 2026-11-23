import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeOperatorSplitOnePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProdStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_eq_zero_of_finrank_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (h : Module.finrank ℂ M = 0) : trOn M L = 0 := by
  unfold trOn
  split_ifs with hL
  · by_cases hf : FiniteDimensional ℂ M
    · haveI := hf
      haveI : Subsingleton M := Module.finrank_zero_iff.mp h
      rw [Subsingleton.elim (L.restrict hL) 0, map_zero]
    · rw [LinearMap.trace, dif_neg]
      · rfl
      · rintro ⟨s, ⟨b⟩⟩
        exact hf (Module.Finite.of_basis b)
  · rfl

theorem trOn_of_eq_smul {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (c : ℂ) (h : ∀ v ∈ M, L v = c • v) : trOn M L = c * Module.finrank ℂ M := by
  have hM : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [h v hv]; exact M.smul_mem c hv
  unfold trOn
  rw [dif_pos hM]
  have hr : L.restrict hM = c • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, h v v.2]
  rw [hr, map_smul, smul_eq_mul]
  by_cases hf : FiniteDimensional ℂ M
  · rw [LinearMap.trace_id]
  · rw [LinearMap.trace, dif_neg, Module.finrank_of_not_finite hf]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hf (Module.Finite.of_basis b)

theorem trOn_hop_eq_dimW_mul_finprod_twTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  intro E _ _ _ hU n hn π hπ S hS lam hlam K' hK' σ hσ f hf
  have hTW := fun w => GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (K' w) (hK'.1 w) (σ w)
  have hcongr : ∀ g g' : ∀ w : Pl E, UL n w → ℂ, (∀ w ∈ S, g w = g' w) → hop S K' g = hop S K' g' := by
    intro g g' h
    have : globFn S g = globFn S g' := by
      funext x
      unfold globFn
      exact finprod_mem_congr rfl (fun w hw => by rw [h w hw])
    unfold hop
    rw [this]
  have hfin : {w | ¬ ((f w = ((KL n w : Set (UL n w)).indicator 1) ∧ K' w = KL n w) ∧
      Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1)}.Finite :=
    Filter.eventually_cofinite.1 ((hf.2.and hK'.2).and (GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all E hU n hn π hπ σ hσ))
  set F := hfin.toFinset with hF
  have hout : ∀ w, w ∉ F → f w = (K' w : Set (UL n w)).indicator 1 ∧
      twTr (σ w).ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = 1 ∧
      (K' w).relIndex (KL n w) = 1 ∧ Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by
    intro w hw
    rw [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    have hr : (K' w).relIndex (KL n w) = 1 := by rw [h2]; exact Subgroup.relIndex_self _
    have hd : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by rw [h2]; exact h3
    refine ⟨by rw [h1, h2], ?_, hr, hd⟩
    rw [(hTW w).2.2.1, hr, hd]
    simp
  set one : ∀ w : Pl E, UL n w → ℂ := fun w => (K' w : Set (UL n w)).indicator 1 with hone
  have key : ∀ U : Finset (Pl E), (↑U : Set (Pl E)) ⊆ S →
      trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
        ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) *
        trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one, one_mul]
    | insert a U ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a U)
      have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hg : IsTest (KL n) K' (fun w => if w ∈ insert a U then f w else one w) := by
        refine ⟨fun w => ?_, ?_⟩
        · by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact hf.1 w
          · simp only [h, if_false]; exact (hTW w).1
        · filter_upwards [hf.2, hK'.2] with w h1 h2
          by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact h1
          · simp only [h, if_false, hone]; rw [h2]
      have hstep := GlobalTheory.T.trace_heckeOperator_split_one_place E hU n hn π hπ S hS K' hK' _ hg a haS (σ a) (hσ a)
      have hupd : Function.update (fun w => if w ∈ insert a U then f w else one w) a
          ((K' a : Set (UL n a)).indicator 1) = fun w => if w ∈ U then f w else one w := by
        funext w
        by_cases h : w = a
        · subst h
          simp [ha, hone]
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd] at hstep
      simp only [Finset.mem_insert_self, if_true] at hstep
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have e1 : twTr (σ a).ρ (KL n a) (K' a) (one a) LinearMap.id =
          twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id := rfl
      rw [e1]
      calc _ = (trOn (π ⊓ fixed (RF E n) (globLev S K'))
              (hop S K' (fun w => if w ∈ insert a U then f w else one w)) *
            twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id := by ring
        _ = twTr (σ a).ρ (KL n a) (K' a) (f a) LinearMap.id *
            (trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id) := by rw [hstep]; ring
        _ = _ := by rw [ih hUS]; ring
  set U := F.filter (· ∈ S) with hUdef
  have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => (Finset.mem_filter.1 hx).2
  have hfU : hop S K' (fun w => if w ∈ U then f w else one w) = hop S K' f := by
    refine hcongr _ _ fun w hw => ?_
    by_cases h : w ∈ F
    · have : w ∈ U := Finset.mem_filter.2 ⟨h, hw⟩
      simp only [this, if_true]
    · have : w ∉ U := fun h' => h (Finset.mem_filter.1 h').1
      simp only [this, if_false, hone]
      exact ((hout w h).1).symm
  have hkey := key U hUS
  rw [hfU] at hkey

  have hfp : ∀ g : Pl E → ℂ, (∀ w, w ∉ F → g w = 1) → ∏ᶠ w ∈ S, g w = ∏ w ∈ U, g w := by
    intro g hg
    refine finprod_mem_eq_prod_of_subset g ?_ (fun x hx => (Finset.mem_filter.1 hx).2)
    rintro w ⟨hwS, hw1⟩
    by_cases h : w ∈ F
    · exact Finset.mem_filter.2 ⟨h, hwS⟩
    · exact absurd (hg w h) hw1
  have hRf := hfp (fun w => (((K' w).relIndex (KL n w) : ℕ) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.1])
  have hDf := hfp (fun w => (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.2])
  have hTf := hfp (fun w => twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) (fun w hw => by
    rw [(hout w hw).1]; exact (hout w hw).2.1)
  have hbase : trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) =
      (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) :=
    trOn_of_eq_smul _ _ _ fun φ hφ => GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index E hU n hn S hS K' hK' φ (Submodule.mem_inf.1 hφ).2
  have hdim := GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn π hπ S hS lam hlam K' hK' σ hσ
  have hone_w : ∀ w, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      ((((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ * (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) :=
    fun w => (hTW w).2.2.1
  rw [Finset.prod_congr rfl (fun w _ => hone_w w)] at hkey
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at hkey
  rw [hbase, hdim, hRf, hDf] at hkey
  rw [hTf]
  have hR : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => Nat.cast_ne_zero.2 (hTW w).2.1
  by_cases hD : (∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) = 0
  · obtain ⟨w, hwU, hw0⟩ := Finset.prod_eq_zero_iff.1 hD
    have hw0' : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 0 := by exact_mod_cast hw0
    have hT0 : (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) = 0 :=
      Finset.prod_eq_zero hwU ((hTW w).2.2.2 hw0' (f w))
    rw [hT0, mul_zero]
    apply trOn_eq_zero_of_finrank_eq_zero
    have : (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = 0 := by
      rw [hdim, hDf, hD, mul_zero]
    exact_mod_cast this
  · have hne : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        ∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hR) hD
    apply mul_right_cancel₀ hne
    rw [hkey]
    ring

end GlobalTheory.BCT
