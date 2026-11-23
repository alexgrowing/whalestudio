import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.MovesU

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

theorem fixed_of_good {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ : AddSubgroup V)
    (g0 : GoodLat H α A B Λ₀) (θ : V → ℂ) (hθ : θ ∈ fixedBy H α Λ₀) :
    (∀ a ∈ Λ₀.addSubgroupOf A, wA H α A a θ = θ) ∧
      ∀ b, (∀ a ∈ Λ₀.addSubgroupOf A, cU H A B b a = 1) → wB H α B b θ = θ := by
  constructor
  · intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    funext z
    exact hθ _ ha z
  · intro b hb
    have hbΛ : (b : V) ∈ Λ₀ := g0.2.2.2.2 b b.2 fun a ha haΛ =>
      (cU_eq_one_iff H A B b ⟨a, ha⟩).1 (hb ⟨a, ha⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using haΛ))
    funext z
    exact hθ _ hbΛ z

theorem GenModelXi_of (hXE : XiExists) (hMU : MovesU) (hExt : ExtendLin) : GenModelXi := by
  intro V _ _ H α Λ₀ M ι Λ Y vol hH θ hθ hfam
  classical
  refine hExt ℂ (M → ℂ) (V → ℂ) ι (fun i => Set.indicator (Y i) 1)
    (fun i => ((Real.sqrt (vol i) : ℝ) : ℂ) • inter H α Λ₀ (Λ i) θ) ?_
  intro s r hr
  obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hfam s
  obtain ⟨hbc, hheis⟩ := heisenberg_unitary_holds V H α A B hH hA hB
  obtain ⟨hfa, hfb⟩ := fixed_of_good H α A B Λ₀ g0 θ hθ
  obtain ⟨Xi, hXi, -⟩ := hXE ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) θ hfa hfb
  obtain ⟨Xi', hXi'⟩ := LinearMap.exists_extend Xi
  have hterm : ∀ i ∈ s, ((Real.sqrt (vol i) : ℝ) : ℂ) • inter H α Λ₀ (Λ i) θ =
      Xi' (ind (((Λ i).addSubgroupOf A : AddSubgroup A) : Set A)) := by
    intro i hi
    obtain ⟨gi, hfin, hmem, hvol⟩ := hs i hi
    obtain ⟨h, hpos, heq⟩ := hMU V H α A B Λ₀ (Λ i) hH hA hB g0 gi hfin θ hθ Xi hXi
    have e1 : Xi' (ind (((Λ i).addSubgroupOf A : AddSubgroup A) : Set A)) = Xi ⟨_, h⟩ := by
      rw [← hXi']; rfl
    rw [e1, heq, hvol, smul_smul]
    have hs0 : Real.sqrt (volA A Λ₀ (Λ i)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hs0, Complex.ofReal_one, one_smul]
  rw [Finset.sum_congr rfl fun i hi => by rw [hterm i hi]]
  simp_rw [← map_smul]
  rw [← map_sum]
  have hz : ∑ i ∈ s, r i • (ind (((Λ i).addSubgroupOf A : AddSubgroup A) : Set A) : A → ℂ) = 0 := by
    funext a
    have := congrFun hr (φ a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨-, -, hmem, -⟩ := hs i hi
    congr 1
    unfold ind
    simp only [SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf, Set.indicator, Pi.one_apply]
    by_cases ha : (a : V) ∈ Λ i
    · rw [if_pos ha, if_pos ((hmem a).1 ha)]
    · rw [if_neg ha, if_neg (fun h => ha ((hmem a).2 h))]
  rw [hz, map_zero]

end Formalism.L2.PairingIndexBounds.Mv
