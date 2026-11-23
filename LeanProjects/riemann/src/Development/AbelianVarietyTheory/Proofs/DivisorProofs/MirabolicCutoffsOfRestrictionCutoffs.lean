import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDiaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnionStatement

noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

variable {F : Type} [NormedField F]

namespace Red

theorem mul_mem_cell_iff {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)} {u : GL (Fin n) F}
    (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) : u * g ∈ cell z U ↔ g ∈ cell z U := by
  constructor
  · rintro ⟨v, hv, k, hk, e⟩
    refine ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, k, hk, ?_⟩
    have : g = u⁻¹ * (u * g) := by group
    rw [this, e]
    simp only [mul_assoc]
  · rintro ⟨v, hv, k, hk, rfl⟩
    exact ⟨u * v, mul_mem hu hv, k, hk, by simp only [mul_assoc]⟩

theorem cell_eq_of_mem {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (hg : g ∈ cell z (U : Set (GL (Fin n) F))) : cell g (U : Set (GL (Fin n) F)) = cell z U := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  ext x
  constructor
  · rintro ⟨u, hu, k', hk', rfl⟩
    exact ⟨u * v, mul_mem hu hv, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩
  · rintro ⟨u, hu, k', hk', rfl⟩
    refine ⟨u * v⁻¹, mul_mem hu (inv_mem hv), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
    group

theorem act_mul_left {ψ : AddChar F ℂ} {n : ℕ} (T : GL (Fin n) F →₀ ℂ) {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f)
    {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    act T f (u * g) = ψ (superDiag u) * act T f g := by
  unfold act Finsupp.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u g k, hf u hu, mul_left_comm]

theorem indicator_cell_mul_left {ψ : AddChar F ℂ} {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    (cell z U).indicator f (u * g) = ψ (superDiag u) * (cell z U).indicator f g := by
  classical
  by_cases hg : g ∈ cell z U
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff hu g).2 hg), hf u hu]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg hg, if_neg (fun h => hg ((mul_mem_cell_iff hu g).1 h)),
      mul_zero]

end Red

open Red

theorem cuts_mir_of_res : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  intro F _ _ _ ψ _ _ m H U hUc hUo z
  classical
  by_cases hz : ∃ h₀ : GL (Fin (m + 1)) F, cor h₀ ∈ cell z (U : Set (GL (Fin (m + 2)) F))
  swap
  · refine ⟨0, fun f _ _ p hp => ?_⟩
    rw [act_zero, Set.indicator_apply, if_neg]
    intro hpc
    obtain ⟨h, x, rfl⟩ := exists_mir hp
    rw [mir_eq, mul_mem_cell_iff (mir_mem_iff.2 (one_mem _))] at hpc
    exact hz ⟨h, hpc⟩
  obtain ⟨h₀, hh₀⟩ := hz
  have hzc : cell z (U : Set (GL (Fin (m + 2)) F)) = cell (cor h₀) U := (Red.cell_eq_of_mem hh₀).symm
  obtain ⟨B, hBc, _, hUB, hcell⟩ := GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff U hUc hUo
  let B' : Subgroup (GL (Fin (m + 1)) F) := U.comap cor
  have hB'o : IsOpen (B' : Set (GL (Fin (m + 1)) F)) := hUo.preimage continuous_cor
  have hB'B : B' ≤ B := fun b hb => hUB b hb
  have hB'c : IsCompact (B' : Set (GL (Fin (m + 1)) F)) :=
    hBc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hB'o) hB'B
  let L : Set (Fin (m + 1) → F) := {y | mir 1 y ∈ U}
  have hL : L ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    refine (hUo.preimage continuous_col).mem_nhds ?_
    show mir 1 0 ∈ U
    rw [mir_one]
    exact one_mem _
  obtain ⟨s, -, hsU, hsd⟩ := GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion B B' hBc hB'o hB'B h₀
  choose T hT using fun x : GL (Fin (m + 1)) F => H B' hB'c hB'o L hL x
  refine ⟨∑ x ∈ s, T x, fun f hf hfU => ?_⟩
  have hB'f : ∀ b ∈ B', ∀ g, f (g * cor b) = f g := fun b hb g => hfU _ hb g
  have hLf : ∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g := fun y hy g => hfU _ hy g
  have hcor : ∀ h, act (∑ x ∈ s, T x) f (cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (cor h) := by
    intro h
    rw [act_finset_sum]
    rw [Finset.sum_congr rfl fun x _ => hT x f hf hB'f hLf h]
    rw [← Finset.indicator_biUnion_apply s _ hsd, ← hsU, hzc]
    by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hcell h₀ h).2 hh)]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hh, if_neg fun h' => hh ((hcell h₀ h).1 h')]
  intro p hp
  obtain ⟨h, x, rfl⟩ := exists_mir hp
  have hu : mir 1 x ∈ unipB F (Fin (m + 2)) := mir_mem_iff.2 (one_mem _)
  rw [mir_eq]
  show act _ f (mir 1 x * cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (mir 1 x * cor h)
  rw [act_mul_left _ hf hu, indicator_cell_mul_left hf hu, hcor]

end GlobalTheory.JSW.Cut
