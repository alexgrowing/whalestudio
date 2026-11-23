import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul {e : AE D} {l m n : ℕ} (M : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem isHalf_add {e : AE D} {m n : ℕ} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_resT_iff {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} (t : WO T S) :
    IsHalf e t ↔ IsHalf e (o.pA ⬝ t) ∧ IsHalf e (o.pB ⬝ t) := by
  refine ⟨fun h => ⟨isHalf_mul _ h, isHalf_mul _ h⟩, fun h => ?_⟩
  have := (o.resT T).symm_apply_apply t
  rw [← this, OrthDec.resT_symm_apply, OrthDec.resT_apply]
  exact isHalf_add (isHalf_mul _ h.1) (isHalf_mul _ h.2)

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_rat_pr {l m : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) : (rat M).map p.pr = M.map (p.pr.comp (incA D)) := by
  rw [rat, Matrix.map_map]; rfl

theorem sumFrame_b' {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (hs : IsSumFrame o ζ α α₀) :
    α₀.b' = fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) ((p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
        ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) := by
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  have hinj : Function.Injective ι := ι.injective
  set c := p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hζ.2
    apply hinj
    rw [map_zero]; exact h
  set M := fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) (c⁻¹ • ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) with hM
  have hcol : (fun i => p.pr (ratV (vecB o ζ) i)) = o.iB.map ι *ᵥ fun j => ι (ζ j) := by
    funext i
    simp only [ratV, vecB]
    exact (RingHom.map_mulVec ι o.iB ζ i)
  have hpA : o.pA.map p.pr = o.qA.map ι := map_rat_pr _
  have hpB : o.pB.map p.pr = o.qB.map ι := map_rat_pr _
  have hjA : o.jA.map p.pr = o.iA.map ι := map_rat_pr _
  have key : M * α₀.b = 1 := by
    rw [hs, hM, Matrix.fromRows_mul, Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_fromCols_eq_fromBlocks,
      ← Matrix.fromBlocks_one]
    have eA : o.qA.map ι * o.iA.map ι = 1 := by rw [← Matrix.map_mul, o.qA_iA]; simp
    have eAB : o.qA.map ι * o.iB.map ι = 0 := by rw [← Matrix.map_mul, o.qA_iB]; simp
    have eBA : o.qB.map ι * o.iA.map ι = 0 := by rw [← Matrix.map_mul, o.qB_iA]; simp
    have eB : o.qB.map ι * o.iB.map ι = 1 := by rw [← Matrix.map_mul, o.qB_iB]; simp
    have hu : (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) = fun j => ι ((star ζ ᵥ* L.gram) j) := rfl
    have hdot : (fun j => ι ((star ζ ᵥ* L.gram) j)) ⬝ᵥ (fun j => ι (ζ j)) = c := by
      rw [hc, Matrix.dotProduct_mulVec, ← RingHom.comp_apply, ← hι, RingHom.map_dotProduct]; rfl
    rw [hcol, hpA, hpB, hjA, hu, ← Matrix.smul_vecMul, Matrix.replicateRow_vecMul, Matrix.replicateCol_mulVec]
    congr 1
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eA, Matrix.one_mul, α.b'b]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eAB, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eBA, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eB, Matrix.one_mul, Matrix.replicateRow_mul_replicateCol]
      ext i j
      simp only [Matrix.of_apply, smul_dotProduct, hdot, smul_eq_mul, inv_mul_cancel₀ hc0]
      fin_cases i; fin_cases j; simp
  calc α₀.b' = (M * α₀.b) * α₀.b' := by rw [key, Matrix.one_mul]
    _ = M := by rw [Matrix.mul_assoc, α₀.bb', Matrix.mul_one]

theorem rd_sumFrame {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO T S) :
    rd β α₀ t = fromRows (rd β α (o.pA ⬝ t)) (replicateRow (Fin 1) (zrow β ζ (o.pB ⬝ t))) := by
  rw [rd, sumFrame_b' o ζ hζ α α₀ hs, Matrix.fromRows_mul, Matrix.fromRows_mul]
  congr 1
  · rw [rd, Matrix.map_mul, Matrix.mul_assoc α.b']
  · rw [← Matrix.replicateRow_vecMul, ← Matrix.replicateRow_vecMul]
    congr 1
    have hv : (fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* (o.pB ⬝ t)) i)) =
        (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* (o.pB ⬝ t).map p.pr := by
      funext i; exact RingHom.map_vecMul p.pr _ _ i
    rw [zrow, hv, Matrix.map_mul]
    simp only [Matrix.smul_vecMul, Matrix.vecMul_vecMul]

theorem extFun_tensRow (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ) (α : Frame p A n')
    (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (Ψ : Matrix n' n k → ℂ)
    (b : (n → k) → ℂ) :
    extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  funext t
  simp only [OrthDec.boxT, extFun, rowFun]
  rw [OrthDec.resT_apply]
  by_cases h : IsHalf p.e t
  · have h' := (isHalf_resT_iff o t).1 h
    rw [if_pos h, if_pos h'.1, if_pos h'.2, rd_sumFrame o ζ hζ α α₀ β hs t]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.pA ⬝ t)
    · rw [if_neg fun hB => h ((isHalf_resT_iff o t).2 ⟨hA, hB⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end Frames

end GlobalTheory.FinPl.ExtZero

end
