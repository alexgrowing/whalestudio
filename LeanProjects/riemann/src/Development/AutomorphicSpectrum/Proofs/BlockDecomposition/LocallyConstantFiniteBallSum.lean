import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_finset_eq_sum_polyBall_translates :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  intro k _ _ _ _ n E _ _ φ s S hinv hsupp
  classical
  set L := polyBall (k := k) n s with hL
  let q : Multiplicative (Fin n → k) → Multiplicative (Fin n → k) ⧸ L := QuotientGroup.mk
  have hopen : IsOpen (L : Set (Multiplicative (Fin n → k))) := isOpen_polyBall n s
  have hcov : ∃ T : Finset (Multiplicative (Fin n → k)),
      ((polyBall (k := k) n S : Subgroup _) : Set (Multiplicative (Fin n → k))) ⊆
        ⋃ x ∈ T, (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))) := by
    refine (isCompact_polyBall n S).elim_finite_subcover
      (fun x : Multiplicative (Fin n → k) => (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))))
      (fun x => (Homeomorph.mulLeft x).isOpenMap _ hopen) ?_ |>.imp fun T hT => ?_
    · intro x _
      exact Set.mem_iUnion.2 ⟨x, 1, L.one_mem, by simp⟩
    · simpa using hT
  obtain ⟨T, hT⟩ := hcov
  let f : Multiplicative (Fin n → k) ⧸ L → (Fin n → k) := fun c => (Quotient.out c).toAdd
  have hf : Function.Injective f := fun a b hab =>
    Quotient.out_injective (Multiplicative.toAdd.injective hab)
  have hmem : ∀ (v : Fin n → k) (c : Multiplicative (Fin n → k) ⧸ L),
      Multiplicative.ofAdd (v - f c) ∈ L ↔ q (Multiplicative.ofAdd v) = c := by
    intro v c
    have hc : q (Quotient.out c) = c := QuotientGroup.out_eq' c
    have hinvEq : Multiplicative.ofAdd (v - f c) =
        ((Multiplicative.ofAdd v)⁻¹ * Quotient.out c)⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp [f, sub_eq_add_neg, add_comm]
    rw [hinvEq, L.inv_mem_iff, ← QuotientGroup.eq]
    exact (by rw [hc] : q (Multiplicative.ofAdd v) = q (Quotient.out c) ↔ _)
  have hval : ∀ v : Fin n → k, φ (f (q (Multiplicative.ofAdd v))) = φ v := by
    intro v
    have h := hinv (f (q (Multiplicative.ofAdd v))) (v - f (q (Multiplicative.ofAdd v)))
      ((hmem v _).2 rfl)
    rw [add_sub_cancel] at h
    exact h.symm
  refine ⟨(T.image q).image f, fun v => ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => hf h)]
  by_cases hv : q (Multiplicative.ofAdd v) ∈ T.image q
  · rw [Finset.sum_eq_single_of_mem _ hv
      (fun b _ hb => if_neg (fun h => hb ((hmem v b).1 h).symm)),
      if_pos ((hmem v _).2 rfl), hval]
  · have h0 : φ v = 0 := by
      by_contra hne
      obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hT (hsupp v hne))
      refine hv (Finset.mem_image.2 ⟨x, hx, ?_⟩)
      have hxv : x⁻¹ * Multiplicative.ofAdd v ∈ L := by
        rw [← hxy]
        simpa using hy
      exact QuotientGroup.eq.2 hxv
    rw [h0]
    refine (Finset.sum_eq_zero fun b hb => if_neg fun h => hv ?_).symm
    rw [(hmem v b).1 h]
    exact hb

end GlobalTheory.CompanionTheory.MirFourier
