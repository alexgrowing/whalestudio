import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N

namespace GlobalTheory

open scoped BigOperators

theorem ssRep_of_normal_finiteIndex : ∀ (H k : Type) [Group H] [Field k] [CharZero k] (a : ℕ)
    (ρ : H →* GL (Fin a) k) (N : Subgroup H), N.Normal → N.FiniteIndex →
    IsSSRep (ρ.comp N.subtype) → IsSSRep ρ := by
  intro H k _ _ _ a ρ N hN hfi hss W hW
  classical

  let T : H → (Fin a → k) →ₗ[k] (Fin a → k) := fun g => Matrix.mulVecLin (ρ g : Matrix (Fin a) (Fin a) k)
  have hTapp : ∀ g v, T g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := fun g v => rfl
  have hTmul : ∀ g h v, T (g * h) v = T g (T h v) := by
    intro g h v
    simp only [hTapp, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hTone : ∀ v, T 1 v = v := by
    intro v; simp [hTapp]
  have hTinv : ∀ g v, T g (T g⁻¹ v) = v := by
    intro g v; rw [← hTmul, mul_inv_cancel, hTone]
  have hTinv' : ∀ g v, T g⁻¹ (T g v) = v := by
    intro g v; rw [← hTmul, inv_mul_cancel, hTone]
  have hWN : IsInv (ρ.comp N.subtype) W := fun n v hv => hW n v hv
  obtain ⟨W', hW', hc⟩ := hss W hWN
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ Submodule.projectionOnto W W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (Submodule.projectionOnto W W' hc v).2
  have hpid : ∀ w ∈ W, p w = w := by
    intro w hw
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hc ⟨w, hw⟩)
  have hp0 : ∀ w ∈ W', p w = 0 := by
    intro w hw
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_right hc ⟨w, hw⟩)
  have hpN : ∀ n ∈ N, ∀ v, T n (p v) = p (T n v) := by
    intro n hn v
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : T n w ∈ W := hW n w hw
    have h2 : T n w' ∈ W' := hW' ⟨n, hn⟩ w' hw'
    rw [map_add p w w', hpid w hw, hp0 w' hw', add_zero, map_add (T n), map_add p, hpid _ h1,
      hp0 _ h2, add_zero]
  let C : H → (Fin a → k) →ₗ[k] (Fin a → k) := fun g => T g ∘ₗ p ∘ₗ T g⁻¹
  have hC : ∀ g n, n ∈ N → C (g * n) = C g := by
    intro g n hn
    refine LinearMap.ext fun v => ?_
    simp only [C, LinearMap.comp_apply, mul_inv_rev]
    rw [hTmul, hTmul, hpN n hn, hTinv]
  let C' : H ⧸ N → (Fin a → k) →ₗ[k] (Fin a → k) :=
    Quotient.lift C (by
      intro g g' hgg'
      have hm : g⁻¹ * g' ∈ N := QuotientGroup.leftRel_apply.mp hgg'
      have : g' = g * (g⁻¹ * g') := by group
      rw [this, hC g _ hm])
  have hC'mk : ∀ g : H, C' (g : H ⧸ N) = C g := fun g => rfl
  haveI : Fintype (H ⧸ N) := Fintype.ofFinite _
  have hm0 : (Fintype.card (H ⧸ N) : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let q : (Fin a → k) →ₗ[k] (Fin a → k) := (Fintype.card (H ⧸ N) : k)⁻¹ • ∑ c : H ⧸ N, C' c
  have hqW : ∀ v, q v ∈ W := by
    intro v
    simp only [q, LinearMap.smul_apply, LinearMap.sum_apply]
    refine W.smul_mem _ (W.sum_mem fun c _ => ?_)
    induction c using QuotientGroup.induction_on with
    | H g =>
      rw [hC'mk]
      exact hW g _ (hpW _)
  have hqid : ∀ w ∈ W, q w = w := by
    intro w hw
    have hterm : ∀ c : H ⧸ N, C' c w = w := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H g =>
        rw [hC'mk]
        simp only [C, LinearMap.comp_apply]
        have hm : T g⁻¹ w ∈ W := hW g⁻¹ w hw
        rw [hpid _ hm, hTinv]
    simp only [q, LinearMap.smul_apply, LinearMap.sum_apply, hterm,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hm0, one_smul]
  have hcomm : ∀ h : H, ∀ c : H ⧸ N, ∀ v, T h (C' c v) = C' (h • c) (T h v) := by
    intro h c v
    induction c using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, hC'mk, hC'mk]
      simp only [C, LinearMap.comp_apply, smul_eq_mul, mul_inv_rev]
      rw [hTmul, hTmul, hTinv']
  have hqT : ∀ h v, T h (q v) = q (T h v) := by
    intro h v
    simp only [q, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
      hcomm]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (H ⧸ N)) (fun c => C' c (T h v))
  refine ⟨LinearMap.ker q, ?_, ?_⟩
  · intro h v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hTapp, ← hqT, hv, map_zero]
  · have hf : ∀ x : W, (q.codRestrict W hqW) x = x := by
      intro x; ext1; exact hqid x x.2
    have := LinearMap.isCompl_of_proj hf
    rwa [LinearMap.ker_codRestrict] at this

end GlobalTheory
