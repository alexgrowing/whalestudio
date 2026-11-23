import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.GelfandEvenSmoothness.IntSmooth

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Sq

theorem val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  Matrix.det_ne_zero_of_left_inverse y.inv_mul

theorem unit_mem {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
  Matrix.det_ne_zero_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp k.2)

theorem mul_mem {n : ℕ} {y : Mat n} (hy : y ∈ GLs n) (k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    k₁.1 * y * k₂.1 ∈ GLs n := by
  have h1 := unit_mem k₁
  have h2 := unit_mem k₂
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at h1 h2 hy ⊢
  exact mul_ne_zero (mul_ne_zero h1 hy) h2

end Sq

theorem adjKer0 (hH : PositivityTheory.RgBcC.Mult.Hyp) (hAW : PositivityTheory.RgBcC.Mult.AdjWave) (hKB : PositivityTheory.RgBcC.Mult.KerBasic)
    (hKA : PositivityTheory.RgBcC.Mult.KerAgree) : AdjKer0 := by
  intro n μ hμ M g T k hg hk
  have : BorelSpace (G n) := ⟨rfl⟩
  have := hμ
  obtain ⟨k', hk'⟩ := hH.2.2.2.2.2.2 n μ M [] g T hg
  have hB := hKB hH n μ M [] g k hk
  have hB' := hKB hH n μ M [] g k' hk'
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have heq : ∀ y ∈ GLs n, PositivityTheory.RgBcC.Mult.kAdj M k y = k' y := by
    refine hKA hH n μ M (PositivityTheory.RgBcC.Mult.kAdj M k) k' hB.2.2.1 hB'.1 hB.2.2.2 hB'.2.1 ?_
    intro u hu hc
    exact (hAW hH n μ M [] g T k hg hk u hu hc 1 h1).trans (hk'.2.2.2 u hu 1 h1).symm
  change IsKer μ M [] g (PositivityTheory.RgBcC.Mult.kAdj M k)
  refine ⟨hk'.1.congr heq, ?_, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hk'.2.1
    exact ⟨R, fun y hy h => (heq y hy).trans (hR y hy h)⟩
  · intro y hy k₁ k₂
    rw [heq _ (Sq.mul_mem hy k₁ k₂), heq y hy]
    exact hk'.2.2.1 y hy k₁ k₂
  · intro u hu x hx
    have e : RgBcC.act μ M (PositivityTheory.RgBcC.Mult.kAdj M k) (u 0) x = RgBcC.act μ M k' (u 0) x := by
      unfold RgBcC.act
      congr 1
      funext y
      rw [heq _ (Sq.val_mem y)]
    rw [e]
    exact hk'.2.2.2 u hu x hx

theorem sqOk (h0 : AdjKer0) (h1 : BlockOperatorsProductAdjoint) (h2 : BlockWordOperators) : SqOk := by
  intro E _ _ _ B t g m ht hg hka hkb
  obtain ⟨-, -, -, -, hadjOk, hadjOp, -, -⟩ := h1 E B t t ht ht
  have hmult : ∀ {n : ℕ} (μ : Measure (G n)), μ.IsHaarMeasure → ∀ (M : Mods E n) (k : Kers M)
      (va : InfinitePlace E → Inf n → ℂ), (∀ v, IsKer μ (M v) [] g (k v) ∧ ∀ χ, va v χ = coshT g (cas χ)) →
      IsMults μ (adjK k) va t.T := by
    intro n μ hμ M k va h v
    refine ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => adjK k v,
      fun _ => ⟨hg, h0 n μ hμ (M v) g t.T (k v) hg (h v).1⟩, ?_, ?_⟩
    · intro y _
      simp
    · intro χ
      simp [zVal, (h v).2 χ]
  have hadj' : t.adj'.Ok :=
    ⟨ht.T, ht.r, hmult B.μa B.ha B.Ma t.ka t.va hka, hmult B.μb B.hb B.Mb t.kb t.vb hkb, hadjOk.ψ, hadjOk.size⟩
  have hw : ∀ s : PT B, s.Ok → (s.pw m).Ok ∧ (s.pw m).op = s.op ^ (m + 1) ∧
      ∀ χa χb, (s.pw m).val χa χb = s.val χa χb ^ (m + 1) := by
    intro s hs
    obtain ⟨hO, hop, -, -, -, hval⟩ := h2 E B (List.replicate m (Sum.inr s)) s (max s.T (s.r + B.c))
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hs) hs (le_max_of_le_left hs.T)
      (fun s' hs' => by
        cases Sum.inr.inj (List.eq_of_mem_replicate hs')
        exact ⟨le_max_left _ _, le_max_right _ _⟩)
    refine ⟨hO, ?_, ?_⟩
    · simp [BGen.sc, BGen.op, List.map_replicate, List.prod_replicate] at hop
      rw [pow_succ]
      exact hop.symm
    · intro χa χb
      have e := hval χa χb
      simp [List.map_replicate, List.prod_replicate] at e
      rw [pow_succ]
      exact e
  obtain ⟨hpO, hpop, hpval⟩ := hw t ht
  obtain ⟨haO, haop, haval⟩ := hw t.adj' hadj'
  obtain ⟨-, -, hmO, hmop, -, -, hmval, -⟩ := h1 E B (t.adj'.pw m) (t.pw m) haO hpO
  have eop : t.adj'.op = t.adj.op := rfl
  have evl : ∀ χa χb, t.adj'.val χa χb = t.val χa χb := fun _ _ => rfl
  refine ⟨hpO, hpop, hmO, ?_, ?_, rfl⟩
  · show ((t.adj'.pw m).mul (t.pw m)).op = _
    rw [hmop, haop, hpop, eop, hadjOp, star_pow, ContinuousLinearMap.star_eq_adjoint]
  · intro χa χb
    show ((t.adj'.pw m).mul (t.pw m)).val χa χb = _
    rw [hmval, haval, hpval, evl, ← pow_add, two_mul]

end PositivityTheory.Rg.BcB.F

end
