import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ConjHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vecMul_jA_eq_zero (p : SplitPt D k) {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr = 0 := by
  have h0 : o.iAᴴ * HSpace.gram S₀ * o.iB = 0 := by
    have := congrArg Matrix.conjTranspose o.orth
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, gram_conjTranspose] using this
  have h1 : o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ) = 0 := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  funext l
  have h2 : ∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l =
      star ((o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ)) l) := by
    rw [Matrix.mulVec, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, star_mul', star_star, mul_comm]
  have h3 : ((fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr) l =
      (p.pr.comp (incA D)) (∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l) := by
    show ∑ i, (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) * (p.pr.comp (incA D)) (o.iA i l) = _
    rw [map_sum]
    simp only [map_mul]
  rw [h3, h2, h1, Pi.zero_apply, star_zero, map_zero]
  rfl

theorem sum_mul_star_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  have e1 : ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = vecB o ζ ⬝ᵥ star (HSpace.gram S₀ *ᵥ vecB o ζ) := rfl
  rw [e1, Matrix.star_mulVec, gram_conjTranspose, dotProduct_comm, ← Matrix.dotProduct_mulVec, vecB,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem sumFrame_dot (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (hsum : IsSumFrame o ζ α α₀)
    (x' : n ⊕ Fin 1 → k) :
    (α₀.b *ᵥ x') ⬝ᵥ (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
      x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
  have e2 : ((o.jA.map p.pr * α.b) *ᵥ (x' ∘ Sum.inl)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, vecMul_jA_eq_zero]
    simp only [Matrix.zero_vecMul, zero_dotProduct]
  have e3 : ((replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) *ᵥ (x' ∘ Sum.inr)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
        x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
    rw [← sum_mul_star_eq]
    show ∑ i, (∑ j : Fin 1, (p.pr.comp (incA D)) (vecB o ζ i) * x' (Sum.inr j)) *
        (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) =
      x' (Sum.inr 0) * (p.pr.comp (incA D)) (∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i))
    rw [map_sum, Finset.mul_sum]
    simp only [Fin.sum_univ_one, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, Matrix.fromCols_mulVec, add_dotProduct, e2, e3]
  exact zero_add _

theorem pair_eq (p : SplitPt D k) (S₀ : HSp D) (z : Fin S₀.rank → D.host.E) (c : AE D) (x : Fin S₀.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (HSpace.gram S₀ i j))) * (p.pr (cA D c) * p.pr (incA D (star (z j))))
      = p.pr (cA D c) * (x ⬝ᵥ fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ z) i)))) := by
  simp only [dotProduct, Finset.mul_sum, Matrix.mulVec, star_sum, map_sum, FrameLat.cA_incA, star_mul', map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conj_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hM hsum hlat c
  have hy : (fun r => cA D p.e * (c * incA D (vecB o ζ r))) =
      fun r => cA D (p.sec (p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))))) := by
    funext r
    have : p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))) = p.pr (cA D (c * incA D (vecB o ζ r))) := by
      simp only [map_mul, FrameLat.cA_incA]
    rw [this, p.sec_pr, map_mul, cA_cA]
  rw [hy, FrameLat.csec_mem_iff hM]
  constructor
  · intro H
    obtain ⟨x1, hx1l, hx1r⟩ : ∃ x1 : n ⊕ Fin 1 → k, x1 ∘ Sum.inl = 0 ∧ x1 (Sum.inr 0) = 1 :=
      ⟨Sum.elim 0 (fun _ => 1), Sum.elim_comp_inl _ _, rfl⟩
    have hx' : x1 ∈ lastKer Λ := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hx1l, hx1r]
      exact ⟨zero_mem _, one_mem _⟩
    have hx := H (α₀.b *ᵥ x1) ((hlat _).1 hx')
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum, hx1r, one_mul] at hx
    exact hx
  · intro H x hx
    have hxx : x = α₀.b *ᵥ (α₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
    rw [hxx] at hx ⊢
    have hl := ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer).1 ((hlat _).2 hx)).2
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum]
    convert mul_mem hl H using 1
    ring

end GlobalTheory.FinPl.ConjHalf
