import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.PDivGroup

theorem surjective_of_cotangentPullback_surjective_nilAug {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [Module.Finite k A] (f : B →ₐc[k] A)
    (hA : ∀ a ∈ augIdeal k A, IsNilpotent a) (hf : Function.Surjective (cotMap f)) :
    Function.Surjective f := by
  set I := augIdeal k A with hIdef
  set J := augIdeal k B with hJdef
  have hfJ : ∀ b ∈ J, f b ∈ I := by
    intro b hb
    have hb' : counit (R := k) b = 0 := hb
    show counit (R := k) (f b) = 0
    rw [CoalgHomClass.counit_comp_apply]; exact hb'

  have step1 : ∀ x ∈ I, ∃ b ∈ J, x - f b ∈ I ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := hf (AugCot.d (counitAlgHom k A) x)
    obtain ⟨b0, rfl⟩ := AugCot.d_surjective _ c
    rw [cotMap_d] at hc
    set b := b0 - algebraMap k B (counit b0) with hb
    have hbJ : b ∈ J := by
      show counit (R := k) b = 0
      simp [hb]
    have hdb : AugCot.d (counitAlgHom k A) (f b) = AugCot.d (counitAlgHom k A) (f b0) := by
      rw [hb, map_sub, AlgHomClass.commutes, map_sub, AugCot.d_algebraMap, sub_zero]
    refine ⟨b, hbJ, ?_⟩
    have h1 : AugCot.d (counitAlgHom k A) (x - f b) = 0 := by
      rw [map_sub, hdb, ← hc, sub_self]
    have hmem : x - f b ∈ I := I.sub_mem hx (hfJ b hbJ)
    rw [AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h1
    exact h1

  have step2 : ∀ m : ℕ, ∀ y ∈ I ^ (m + 1), ∃ b ∈ J ^ (m + 1), y - f b ∈ I ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [zero_add, pow_one] at hy
      obtain ⟨b, hb, h⟩ := step1 y hy
      exact ⟨b, by rwa [zero_add, pow_one], h⟩
    | succ m ih =>
      intro y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro x hx z hz
        obtain ⟨b1, hb1, hu⟩ := step1 x hx
        obtain ⟨b2, hb2, hv⟩ := ih z hz
        have hfb1 : f b1 ∈ I := hfJ b1 hb1
        have hfb2 : f b2 ∈ I ^ (m + 1) := by
          have : f b2 = z - (z - f b2) := by ring
          rw [this]
          exact (I ^ (m + 1)).sub_mem hz (Ideal.pow_le_pow_right (by omega) hv)
        refine ⟨b1 * b2, ?_, ?_⟩
        · rw [pow_succ']; exact Ideal.mul_mem_mul hb1 hb2
        · set u := x - f b1
          set v := z - f b2
          have hx' : x = f b1 + u := by simp [u]
          have hz' : z = f b2 + v := by simp [v]
          have : x * z - f (b1 * b2) = f b1 * v + u * f b2 + u * v := by
            rw [hx', hz', map_mul]; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul hfb1 hv
          · rw [show m + 1 + 2 = 2 + (m + 1) by omega, pow_add]
            exact Ideal.mul_mem_mul hu hfb2
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul (Ideal.pow_le_self (by norm_num) hu) hv
      · rintro y1 y2 ⟨b1, hb1, h1⟩ ⟨b2, hb2, h2⟩
        refine ⟨b1 + b2, Ideal.add_mem _ hb1 hb2, ?_⟩
        have : y1 + y2 - f (b1 + b2) = (y1 - f b1) + (y2 - f b2) := by rw [map_add]; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
  have step3 : ∀ m : ℕ, ∀ x ∈ I, ∃ b : B, x - f b ∈ I ^ (m + 1) := by
    intro m
    induction m with
    | zero => intro x hx; exact ⟨0, by rw [map_zero, sub_zero, zero_add, pow_one]; exact hx⟩
    | succ m ih =>
      intro x hx
      obtain ⟨b, hb⟩ := ih x hx
      obtain ⟨b', -, hb'⟩ := step2 m _ hb
      refine ⟨b + b', ?_⟩
      have : x - f (b + b') = x - f b - f b' := by rw [map_add]; ring
      rw [this]; exact hb'

  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hnil : IsNilpotent I := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).2 ?_
    intro a ha
    exact (mem_nilradical).2 (hA a ha)
  obtain ⟨N, hN⟩ := hnil
  have hI : ∀ x ∈ I, ∃ b : B, f b = x := by
    intro x hx
    obtain ⟨b, hb⟩ := step3 N x hx
    have : x - f b ∈ I ^ N := Ideal.pow_le_pow_right (by omega) hb
    rw [hN] at this
    exact ⟨b, (sub_eq_zero.1 ((Submodule.mem_bot _).1 this)).symm⟩
  intro a
  have ha : a - algebraMap k A (counit a) ∈ I := by
    show counit (R := k) (a - algebraMap k A (counit a)) = 0
    simp
  obtain ⟨b, hb⟩ := hI _ ha
  refine ⟨b + algebraMap k B (counit a), ?_⟩
  rw [map_add, AlgHomClass.commutes, hb, sub_add_cancel]

theorem app_surjective_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  intro p _ k _ _ G H q hG hq n
  refine surjective_of_cotangentPullback_surjective_nilAug (q.app n) (hG n) fun w => ?_
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective n w
  obtain ⟨u, rfl⟩ := hq v
  exact ⟨u.1 n, rfl⟩

end GlobalTheory.PDivGroup
