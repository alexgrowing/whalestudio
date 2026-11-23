import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkKapInv

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem isHalf_mul_l {e : AE D} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hx k j]

theorem isHalf_mul_r {e : AE D} {l m n : ℕ} {x : Mx D l m} (hx : IsHalf e x) (A : Mx D m n) : IsHalf e (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hx i k]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) :=
  fun i j => by
    show cA D e * cA D (x j i) = cA D (x j i)
    rw [← map_mul, hx j i]

def tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (_l : Link B L' ζ') :
    Matrix (Fin L'.rank) (Fin B.L.rank) D.host.E := fun i j => -(B.ζ j)⁻¹ * ζ' i

theorem mul_tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    l.τ * tauPlus l = 1 := by
  obtain ⟨hr, hq⟩ := B.line
  have hsub : ∀ a b : Fin B.L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hne : ∀ a, B.ζ a ≠ 0 := by
    intro a ha
    apply hq
    have h0 : B.ζ = 0 := funext fun b => by rw [hsub b a]; exact ha
    rw [h0]; simp
  funext a b
  rw [hsub b a, Matrix.one_apply_eq, Matrix.mul_apply]
  have hm := congrFun l.map a
  rw [Pi.neg_apply, Matrix.mulVec, dotProduct] at hm
  simp only [tauPlus]
  calc ∑ k, l.τ a k * (-(B.ζ a)⁻¹ * ζ' k) = -(B.ζ a)⁻¹ * ∑ k, l.τ a k * ζ' k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [hm, neg_mul_neg, inv_mul_cancel₀ (hne a)]

theorem kappa_inv : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ')
    (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧
      ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  intro D ρ B L' ζ' l S P h
  refine ⟨(rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h, ?_, fun hh => ?_, fun e he => ?_⟩
  · show ofAdj B.L S ((rat l.τ : Mx D B.L.rank L'.rank) * ((rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h)) = h
    rw [← Matrix.mul_assoc, ← rat_mul, mul_tauPlus l, rat_one, Matrix.one_mul, GlobalTheory.LastOpPf.ofAdj_starAdj]
  · exact GlobalTheory.LastOpPf.mxAt_mul_l _ (GlobalTheory.LastOpPf.mxAt_smul _ (GlobalTheory.LastOpPf.mxAt_mul_l _
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LastOpPf.mxAt_adj hh) _)))
  · exact isHalf_mul_l _ (isHalf_smul _ (isHalf_mul_l _ (isHalf_mul_r (isHalf_adj he) _)))

end GlobalTheory.LinkKapInv
