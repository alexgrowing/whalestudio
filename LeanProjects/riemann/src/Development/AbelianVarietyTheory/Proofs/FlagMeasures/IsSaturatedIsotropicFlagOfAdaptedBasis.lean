import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.AdSat

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem isSatFlag_of_isAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (_hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) :
    IsSatFlag I (lamX I (1, xf)) j S := by
  classical
  obtain ⟨-, -, hΛ, h1, h2, -, hL, hS⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  let p : ∀ i, (Fin I.n → I.E) →ₗ[I.E] (Fin (j i) → I.E) := fun i => ((T' i)ᴴ * I.J).mulVecLin
  have hsw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := fun i k => by
    simp [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc]
  have pT : ∀ i x, p i (T i *ᵥ x) = x := fun i x => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h2 i).1]; simp
  have pT' : ∀ i k x, k ≠ i → p i (T k *ᵥ x) = 0 := fun i k x hk => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h1 k i).2.2 hk]; simp
  have pS : ∀ i (u : ∀ i, Fin (j i) → I.E), p i (∑ k, T k *ᵥ u k) = u i := fun i u => by
    rw [map_sum, Finset.sum_eq_single i (fun k _ hk => pT' i k _ hk) (by simp), pT]
  have hsp : ∀ k z, z ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) →
      z = ∑ i, T i *ᵥ p i z ∧ ∀ i : Fin a, ¬ i.castSucc < k → p i z = 0 := fun k z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, -, hu, rfl⟩ := (hS k z).1 hz
      simp only [pS]
      exact ⟨trivial, hu⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, fun i hi => by rw [map_add, hx.2 i hi, hy.2 i hi, add_zero]⟩
      simp only [map_add, mulVec_add, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    | smul c x _ hx =>
      refine ⟨?_, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩
      simp only [map_smul, mulVec_smul, ← Finset.smul_sum]
      rw [← hx.1]
  have hmono : Monotone S := fun k l hkl z hz => by
    obtain ⟨u, hu, hu0, rfl⟩ := (hS k z).1 hz
    exact (hS l _).2 ⟨u, hu, fun i hi => hu0 i fun h => hi (h.trans_le hkl), rfl⟩
  refine ⟨?_, hmono, fun i => ?_, fun k y => ⟨fun hy => ⟨?_, Submodule.subset_span hy⟩, ?_⟩, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨u, -, hu0, rfl⟩ := (hS 0 z).1 hz
    have : ∀ i, u i = 0 := fun i => hu0 i (by simp)
    simp [this]
  · have hsup : Submodule.span I.E (S i.succ : Set (Fin I.n → I.E)) =
        Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊔ LinearMap.range (T i).mulVecLin := by
      apply le_antisymm
      · refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨u, hu, hu0, rfl⟩ := (hS _ z).1 hz
        have e1 : ∑ k, T k *ᵥ u k = ∑ k, T k *ᵥ Function.update u i 0 k + T i *ᵥ u i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ (fun k => T k *ᵥ Function.update u i 0 k) (Finset.mem_univ i)]
          rw [Finset.sum_congr rfl (s₁ := univ.erase i) (f := fun k => T k *ᵥ Function.update u i 0 k)
            (g := fun k => T k *ᵥ u k)
            (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])]
          simp [add_comm]
        rw [e1]
        refine Submodule.add_mem_sup (Submodule.subset_span ((hS _ _).2 ⟨_, fun k => ?_, fun k hk => ?_, rfl⟩))
          ⟨u i, rfl⟩
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]; exact hu k
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]
            refine hu0 k fun h => hk ?_
            rw [Fin.castSucc_lt_succ_iff] at h
            exact Fin.castSucc_lt_castSucc_iff.2 (lt_of_le_of_ne h hki)
      · refine sup_le (Submodule.span_mono (hmono (Fin.castSucc_lt_succ).le)) ?_
        rw [LinearMap.range_eq_map, ← (hΛ i).span_eq_top, Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine (hS _ _).2 ⟨Pi.single i x, fun k => ?_, fun k hk => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; simpa using hx
          · rw [Pi.single_eq_of_ne hki]; exact zero_mem _
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          exact hk Fin.castSucc_lt_succ
        · rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mulVec_zero]) (by simp)]
          simp
    have hinf : Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊓ LinearMap.range (T i).mulVecLin = ⊥ := by
      refine eq_bot_iff.2 ?_
      rintro _ ⟨hz, x, rfl⟩
      have : x = 0 := (pT i x).symm.trans ((hsp _ _ hz).2 i (lt_irrefl _))
      simp [this]
    have hinj : Function.Injective (T i).mulVecLin := fun x y hxy => by
      rw [← pT i x, ← pT i y]; exact congrArg (p i) hxy
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)))
      (LinearMap.range (T i).mulVecLin)
    rw [hinf, ← hsup, LinearMap.finrank_range_of_inj hinj] at this
    simpa [Formalism.HN.rkK] using this
  · obtain ⟨u, hu, -, rfl⟩ := (hS k y).1 hy
    refine (hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simpa using zero_mem _, zero_mem _, ?_⟩
    have : (fun l => e ((0 : Fin I₀.n → I₀.E) l)) = 0 := by ext; simp
    rw [this]
    simp
  · rintro ⟨hy, hy'⟩
    obtain ⟨u, u', y₀, hu, -, -, hz⟩ := (hL y).1 hy
    have hp : ∀ i, p i y = u i := fun i => by
      have a1 : ∀ k, p i (T' k *ᵥ u' k) = 0 := fun k => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h1 i k).2.1]; simp
      have a2 : ∀ x, p i (T₀ *ᵥ x) = 0 := fun x => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h2 i).2.2]; simp
      rw [hz, map_add, map_add, pS, a2, map_sum]
      simp [a1]
    obtain ⟨b1, b2⟩ := hsp k y hy'
    exact (hS k y).2 ⟨fun i => p i y, fun i => by simpa only [hp] using hu i, b2, b1⟩
  · intro x hx y hy
    obtain ⟨u, -, -, rfl⟩ := (hS _ x).1 hx
    obtain ⟨v, -, -, rfl⟩ := (hS _ y).1 hy
    rw [hform_eq, star_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mulVec_sum, dotProduct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, (h1 i k).1]
    simp

end GlobalTheory.FlagBase.AdSat
