import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSeparated

open Finset

namespace GlobalTheory

theorem packing_geometric_mean_subspaces : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (U : ι → Submodule ℝ W) (N : ℕ), (∀ v, Module.finrank ℝ (U v) ≤ N) → ∀ (α : Type) (T : Finset α) (y : α → ι → W) (la X : ℝ), 0 < la → 0 < X → (∀ t ∈ T, ∀ v, y t v ∈ U v ∧ ‖y t v‖ ≤ X) → (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → la ≤ (∏ v, ‖y t v - y t' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → (T.card : ℝ) ≤ (1 + 2 * X / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ U N hU α T y la X hla hX hT hsep
  classical
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hexp : (1 : ℝ) / Fintype.card ι ≠ 0 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
    positivity

  have hinj : Set.InjOn y T := by
    intro t ht t' ht' he
    by_contra hne
    have h := hsep t ht t' ht' hne
    rw [he] at h
    simp only [sub_self, norm_zero] at h
    have h0 : (∏ _v : ι, (0 : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) rfl
    rw [h0, Real.zero_rpow hexp] at h
    linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  ·
    subst hN
    have hzero : ∀ t ∈ T, y t = 0 := by
      intro t ht
      funext v
      have hb : U v = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp (hU v))
      have hm := (hT t ht v).1
      rw [hb, Submodule.mem_bot] at hm
      exact hm
    have h1 : T.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact hinj ha hb (by rw [hzero a ha, hzero b hb])
    simp only [zero_mul, pow_zero]
    exact_mod_cast h1
  ·
    have key := packing_geometric_mean_separated ι
      (fun v => ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ)) N hN
      (fun v => by
        simp only [Module.finrank_prod, Module.finrank_fin_fun]
        have := hU v
        omega)
      la
      (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))))
      (fun _ => X) hla (fun _ => hX)
    have hnormpt : ∀ (v : ι) (a : U v),
        ‖((a, (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) :
          ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ = ‖(a : W)‖ := by
      intro v a
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      rfl
    obtain ⟨-, hbound⟩ := key (by
      intro s hs s' hs' hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs hs'
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := hs'
      have hab : (a : α) ≠ b := by
        intro h
        apply hne
        rw [Subtype.ext h]
      have e : ∀ v, ‖((⟨y a v, (hT a a.2 v).1⟩ : U v),
            (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) -
          ((⟨y b v, (hT b b.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ =
          ‖y a v - y b v‖ := by
        intro v
        rw [Prod.mk_sub_mk, sub_zero, hnormpt]
        rfl
      simp only [e]
      exact hsep a a.2 b b.2 hab)
    have hset : {s ∈ (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) :
          Set (∀ v, ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))) |
          ∀ v, ‖s v‖ ≤ (fun _ => X) v} =
        ↑(T.attach.image (fun t : T => fun v =>
          ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) := by
      apply Set.sep_eq_self_iff_mem_true.mpr
      intro s hs
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs
      obtain ⟨a, rfl⟩ := hs
      intro v
      rw [hnormpt]
      exact (hT a a.2 v).2
    have hinj' : Function.Injective (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))) := by
      intro a b hab
      apply Subtype.ext
      apply hinj a.2 b.2
      funext v
      have := congrFun hab v
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
      exact this.1
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj',
      Finset.card_attach] at hbound
    have hX' : (∏ _v : ι, X) ^ ((1 : ℝ) / Fintype.card ι) = X := by
      rw [Finset.prod_const, Finset.card_univ, one_div]
      exact Real.pow_rpow_inv_natCast hX.le hcard.ne'
    rw [hX'] at hbound
    exact hbound

end GlobalTheory
