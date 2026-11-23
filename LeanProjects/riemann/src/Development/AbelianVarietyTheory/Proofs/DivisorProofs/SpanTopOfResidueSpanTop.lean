import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem span_top_of_residue_span_top :
    ∀ (A k ι : Type) [CommRing A] [IsLocalRing A] [Field k] [Fintype ι] (h : ℕ) (c : A →+* k)
      (g : ι → Fin h → A), Function.Surjective c →
      Submodule.span k (Set.range fun i => fun j => c (g i j)) = ⊤ →
      Submodule.span A (Set.range g) = ⊤ := by
  intro A k ι _ _ _ _ h c g hc hspan
  have hker : RingHom.ker c = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective c hc)
  set N : Submodule A (Fin h → A) := Submodule.span A (Set.range g) with hN

  have hlift : ∀ w : Fin h → k, w ∈ Submodule.span k (Set.range fun i => fun j => c (g i j)) →
      ∃ v ∈ N, ∀ j, c (v j) = w j := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨g i, Submodule.subset_span ⟨i, rfl⟩, fun _ => rfl⟩
    | zero => exact ⟨0, N.zero_mem, fun j => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, N.add_mem ha hb, fun j => by simp [ha', hb']⟩
    | smul t x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨s, rfl⟩ := hc t
      exact ⟨s • a, N.smul_mem s ha, fun j => by simp [ha']⟩
  have hm : ∀ x : Fin h → A, (∀ j, x j ∈ IsLocalRing.maximalIdeal A) →
      x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (Fin h → A)) := by
    intro x hx
    have hx' : x = ∑ j, x j • (Pi.single j 1 : Fin h → A) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hx j) Submodule.mem_top
  have hle : (⊤ : Submodule A (Fin h → A)) ≤
      N ⊔ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (Fin h → A)) := by
    intro v _
    obtain ⟨n, hn, hn'⟩ := hlift (fun j => c (v j)) (by rw [hspan]; trivial)
    have hd : v - n ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (Fin h → A)) := by
      apply hm
      intro j
      rw [← hker, RingHom.mem_ker]
      simp [hn']
    have : v = n + (v - n) := by abel
    rw [this]
    exact Submodule.add_mem_sup hn hd
  have hjac : IsLocalRing.maximalIdeal A ≤ (⊥ : Ideal A).jacobson :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact top_le_iff.mp
    (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac hle)

end GlobalTheory.DetInv
