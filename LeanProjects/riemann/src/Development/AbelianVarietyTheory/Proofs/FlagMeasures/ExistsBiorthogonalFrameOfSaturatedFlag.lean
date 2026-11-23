import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplOfSaturated
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_biorth {E : Type} [Field E] {n m : ℕ} {r : ℕ → ℕ}
    (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (hr : ∀ b, m ≤ b → r b = 0)
    (hn : n = ∑ b ∈ Finset.range m, r b)
    (hs : ∀ y : Fin n → E, ∃ u : ∀ b, Fin (r b) → E, y = ∑ b ∈ Finset.range m, T b *ᵥ u b) :
    ∃ T' : ∀ b, Matrix (Fin (r b)) (Fin n) E, Biorth r m T T' := by
  classical
  let Φ : ((b : Fin m) → Fin (r b) → E) →ₗ[E] (Fin n → E) :=
    ∑ b : Fin m, (T b).mulVecLin ∘ₗ LinearMap.proj b
  have hΦ : ∀ u : ∀ b, Fin (r b) → E, Φ (fun b => u b) = ∑ b ∈ Finset.range m, T b *ᵥ u b := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun b => T b *ᵥ u b)]
    simp [Φ]
  have hsurj : Function.Surjective Φ := fun y => by
    obtain ⟨u, hu⟩ := hs y
    exact ⟨_, (hΦ u).trans hu.symm⟩
  have hinj : Function.Injective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hn, Fin.sum_univ_eq_sum_range]
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let T' : ∀ b, Matrix (Fin (r b)) (Fin n) E := fun b =>
    if h : b < m then LinearMap.toMatrix'
      ((LinearMap.proj (⟨b, h⟩ : Fin m) : ((b : Fin m) → Fin (r b) → E) →ₗ[E] _) ∘ₗ e.symm.toLinearMap)
    else 0
  have hemp : ∀ b, ¬ b < m → IsEmpty (Fin (r b)) := fun b hb => by
    rw [hr b (by omega)]; infer_instance
  have hT' : ∀ (b : Fin m) y, T' b *ᵥ y = e.symm y b := fun b y => by
    simp only [T', dif_pos b.2]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have H1 : ∀ (u : ∀ b, Fin (r b) → E) b, T' b *ᵥ (∑ c ∈ Finset.range m, T c *ᵥ u c) = u b := by
    intro u b
    by_cases hb : b < m
    · rw [hT' ⟨b, hb⟩, ← hΦ]
      exact congrFun (e.symm_apply_apply _) _
    · have := hemp b hb
      exact Subsingleton.elim _ _
  have H2 : ∀ b c v, T' b *ᵥ (T c *ᵥ v) = (Pi.single c v : ∀ b, Fin (r b) → E) b := by
    intro b c v
    rw [← H1 (Pi.single c v) b]
    congr 1
    by_cases hc : c < m
    · rw [Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd])
        (fun h => absurd (Finset.mem_range.2 hc) h)]
      simp
    · have := hemp c hc
      obtain rfl : v = 0 := Subsingleton.elim _ _
      simp
  refine ⟨T', fun b => ?_, fun b c hbc => ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp [Pi.single_eq_of_ne hbc]
  · refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    obtain ⟨u, rfl⟩ := hs y
    simp only [Matrix.toLin'_apply]
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Matrix.mulVec_mulVec, H1]

theorem exists_biorth_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  intro E _ _ n m F r hmono h0 hm hL hsat hrk
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hmono h
    · exact (hm b h).le
  have key : ∀ b, ∃ A : Submodule (𝓞 E) (Fin n → E), A ⊓ F b = ⊥ ∧ A ⊔ F b = F (b + 1) := by
    intro b
    refine exists_compl_of_saturated _ _ (hmono b.le_succ) (Submodule.FG.of_le hL.fg (hle _)) ?_
    intro c y hc hy hcy
    apply hsat _ y (hle _ hy)
    have hc' : (c : E) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span hcy
  choose A hA1 hA2 using key
  have hAF : ∀ b, A b ≤ F (b + 1) := fun b => hA2 b ▸ le_sup_left
  have hAr : ∀ b, Formalism.HN.rkK (A b) = r b := fun b => by
    have := AdaptedExists.rkK_add (hA1 b)
    rw [hA2, hrk] at this
    omega
  choose Λ T hΛ hT using fun b => AdaptedExists.exists_model (A b)
    (Submodule.FG.of_le hL.fg ((hAF b).trans (hle _))) (hAr b)
  have hdec : ∀ k, ∀ y ∈ F k, ∃ u : ∀ b, Fin (r b) → E, (∀ b, u b ∈ Λ b) ∧
      y = ∑ b ∈ Finset.range k, T b *ᵥ u b := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [h0, Submodule.mem_bot] at hy
      exact ⟨0, fun b => zero_mem _, by simpa using hy⟩
    | succ k ih =>
      intro y hy
      rw [← hA2] at hy
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨v, hv, rfl⟩ := (hT k a).1 ha
      obtain ⟨u, hu, rfl⟩ := ih z hz
      refine ⟨Function.update u k v, fun b => ?_, ?_⟩
      · by_cases hb : b = k
        · subst hb; simpa using hv
        · rw [Function.update_of_ne hb]; exact hu b
      · rw [Finset.sum_range_succ, add_comm, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Function.update_of_ne (Finset.mem_range.1 hc).ne]
  have hr0 : ∀ b, m ≤ b → r b = 0 := fun b hb => by
    have := hrk b
    rw [hm b hb, hm (b + 1) (by omega)] at this
    omega
  have hsum : ∀ k, Formalism.HN.rkK (F k) = ∑ b ∈ Finset.range k, r b := by
    intro k
    induction k with
    | zero => rw [h0]; simp [Formalism.HN.rkK]
    | succ k ih => rw [hrk, ih, Finset.sum_range_succ]
  have hn : n = ∑ b ∈ Finset.range m, r b := by
    rw [← hsum, Formalism.HN.rkK, hL.span_eq_top]
    simp
  obtain ⟨T', hB⟩ := exists_biorth T hr0 hn (fun y => by
    obtain ⟨c, hc, hcy⟩ := AdaptedExists.exists_smul_mem (L := F m) (x := y)
      (by rw [hL.span_eq_top]; trivial)
    obtain ⟨u, -, hu⟩ := hdec m _ hcy
    have hc' : (c : E) ≠ 0 := by simpa using hc
    refine ⟨fun b => (c : E)⁻¹ • u b, ?_⟩
    simp only [Matrix.mulVec_smul]
    rw [← Finset.smul_sum, ← hu, eq_inv_smul_iff₀ hc']
    rfl)
  refine ⟨T, T', Λ, hB, hΛ, fun k y => ⟨fun hy b => ?_, fun hy => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := hdec k y hy
    have h1 : T' b *ᵥ (∑ c ∈ Finset.range k, T c *ᵥ u c) = if b < k then u b else 0 := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec]
      split_ifs with hb
      · rw [Finset.sum_eq_single b (fun c _ hc => by rw [hB.2.1 b c hc.symm, Matrix.zero_mulVec])
          (fun h => absurd (Finset.mem_range.2 hb) h), hB.1, Matrix.one_mulVec]
      · refine Finset.sum_eq_zero fun c hc => ?_
        rw [hB.2.1 b c (by have := Finset.mem_range.1 hc; omega), Matrix.zero_mulVec]
    rw [h1]
    refine ⟨?_, fun h => if_neg (by omega)⟩
    split_ifs
    · exact hu b
    · exact zero_mem _
  · have h1 : y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, hB.2.2, Matrix.one_mulVec]
    rw [h1]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · rw [(hy b).2 hb, Matrix.mulVec_zero]; exact zero_mem _
    · exact hmono (show b + 1 ≤ k by omega) (hAF b ((hT b _).2 ⟨_, (hy b).1, rfl⟩))

end GlobalTheory.RadCov
