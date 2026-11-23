import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul_right {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, hu]

theorem isHalf_add_of {e : AE D} {m n : ℕ} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_resS_iff {S A L T : HSp D} (o : OrthDec S A L) (e : AE D) (t : WO S T) :
    IsHalf e t ↔ IsHalf e (t * o.jA) ∧ IsHalf e (t * o.jB) := by
  refine ⟨fun h => ⟨isHalf_mul_right h _, isHalf_mul_right h _⟩, fun h => ?_⟩
  have ht : t = (o.resS T).symm (o.resS T t) := ((o.resS T).symm_apply_apply t).symm
  rw [ht, OrthDec.resS_symm_apply, OrthDec.resS_apply]
  exact isHalf_add_of (isHalf_mul_right h.1 _) (isHalf_mul_right h.2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rd_sum_inl {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (rd α₀ β t).submatrix id Sum.inl = rd α β (t * o.jA) := by
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  simp only [rd, hs', Matrix.mul_fromCols]
  ext i j
  simp only [submatrix_apply, id, fromCols_apply_inl]
  rw [Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem rd_sum_inr {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (fun i => rd α₀ β t i (Sum.inr 0)) = zcol β ζ (t * o.jB) := by
  have h1 : (t * o.jB) *ᵥ (fun j => incA D (ζ j)) = t *ᵥ ratV (vecB o ζ) := by
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp only [OrthDec.jB, rat, vecB, ratV]
    exact (RingHom.map_mulVec (incA D) o.iB ζ i).symm
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  funext i
  simp only [rd, hs', Matrix.mul_fromCols, fromCols_apply_inr, zcol, h1]
  rw [show (fun i => p.pr ((t *ᵥ ratV (vecB o ζ)) i)) = t.map p.pr *ᵥ fun i => p.pr (ratV (vecB o ζ) i) from
    funext fun i => RingHom.map_mulVec p.pr t _ i]
  rw [Matrix.mulVec_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, replicateCol]

theorem extFun_tensCol_sum (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) :
    IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ),
      extFun α₀ β (tensCol Ψ a) = o.boxS T (extFun α β Ψ) (GlobalTheory.FinPl.ExtZero.colFun β ζ a) := by
  intro hs Ψ a
  funext t
  simp only [extFun, OrthDec.boxS, colFun]
  have key : IsHalf p.e t ↔ IsHalf p.e (o.resS T t).1 ∧ IsHalf p.e (o.resS T t).2 := isHalf_resS_iff o p.e t
  by_cases h : IsHalf p.e t
  · obtain ⟨hA, hL⟩ := key.1 h
    rw [if_pos h, if_pos hA, if_pos hL, tensCol, rd_sum_inl o ζ α α₀ β hs, rd_sum_inr o ζ α α₀ β hs]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.resS T t).1
    · rw [if_neg fun hL => h (key.2 ⟨hA, hL⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end GlobalTheory.FinPl.ExtZero
