import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.LFun

private theorem esymm_scale (A : Multiset ℂ) (c : ℂ) (i : ℕ) :
    (A.map (· * c)).esymm i = c ^ i * A.esymm i := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  have h := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply]
  rw [Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, h, mul_comm]

private theorem satEig_scale (q n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ) (i : ℕ) :
    satEig q n (B.map (· * c)) i = (c : ℂ) ^ i * satEig q n B i := by
  have e : ((B.map (· * c)).map fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map (· * (c : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  simp only [satEig]
  rw [e, esymm_scale]
  ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.satSum :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.SatSum := by
  intro q a b hq B₁ B₂ c₁ c₂ h₁ h₂ j
  rw [GlobalTheory.ResW.SatWordAt.satEig_add hq rfl (C := B₁.map (· * c₁)) (B := B₂.map (· * c₂))
    (by simpa using h₁) (by simpa using h₂) j]
  have hL : ∀ i ∈ (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
      (q : ℂ) ^ (((j : ℂ) * (((a + b : ℕ) : ℂ) - j) - i.1 * (a - i.1) - i.2 * (b - i.2)) / 2) *
        (GlobalTheory.LFun.satEig q a (B₁.map (· * c₁)) i.1 * GlobalTheory.LFun.satEig q b (B₂.map (· * c₂)) i.2) =
      (if i.1 + i.2 = j then (q : ℂ) ^ ((((i.1 : ℂ)) * ((b : ℂ) - i.2) + ((i.2 : ℂ)) * ((a : ℂ) - i.1)) / 2) else 0) *
        (c₁ : ℂ) ^ i.1 * (c₂ : ℂ) ^ i.2 * (GlobalTheory.LFun.satEig q a B₁ i.1 * GlobalTheory.LFun.satEig q b B₂ i.2) := by
    intro i hi
    have hs : i.1 + i.2 = j := (Finset.mem_filter.1 hi).2
    have hsc : (j : ℂ) = (i.1 : ℂ) + i.2 := by exact_mod_cast hs.symm
    rw [if_pos hs, satEig_scale, satEig_scale]
    have e : ((j : ℂ) * (((a + b : ℕ) : ℂ) - j) - i.1 * (a - i.1) - i.2 * (b - i.2)) / 2 =
        (((i.1 : ℂ)) * ((b : ℂ) - i.2) + ((i.2 : ℂ)) * ((a : ℂ) - i.1)) / 2 := by
      rw [hsc]; push_cast; ring
    rw [e]
    ring
  rw [Finset.sum_congr rfl hL]
  set G : ℕ × ℕ → ℂ := fun i =>
    (if i.1 + i.2 = j then (q : ℂ) ^ ((((i.1 : ℂ)) * ((b : ℂ) - i.2) + ((i.2 : ℂ)) * ((a : ℂ) - i.1)) / 2) else 0) *
      (c₁ : ℂ) ^ i.1 * (c₂ : ℂ) ^ i.2 * (GlobalTheory.LFun.satEig q a B₁ i.1 * GlobalTheory.LFun.satEig q b B₂ i.2) with hG
  have hF : ∑ i ∈ (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j), G i =
      ∑ i ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1), G i := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun x hx hx' => ?_
    have hne : x.1 + x.2 ≠ j := fun e => hx' (Finset.mem_filter.2 ⟨hx, e⟩)
    simp [hG, hne]
  rw [hF, Finset.sum_product, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun x => ∑ y ∈ Finset.range (b + 1), G (x, y))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun y => G ((x : ℕ), y))]
  rfl
