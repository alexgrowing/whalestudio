import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatPairInt

variable {D : D7}

theorem cA_tmul (p : AF D.host.F) (t : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] t) = p ⊗ₜ[D.host.F] (star t) :=
  rfl

theorem intAt_zero (P : GlobalTheory.FinPl.Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem pair_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [zero_mul]) rfl

theorem term_eq (p q : AF D.host.F) (a g b : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] a) * incA D g * (q ⊗ₜ[D.host.F] b) = (p * q) ⊗ₜ[D.host.F] (star a * g * b) := by
  rw [cA_tmul]
  change (p ⊗ₜ[D.host.F] star a) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * (q ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pairing_mem (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : IsSelfDualC S L) (P : GlobalTheory.FinPl.Pl D → Prop)
    (z w : Fin S.rank → AE D) (hz : z ∈ latV S L P) (hw : w ∈ latV S L P) :
    (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβi, hβ, a', ha', x', hx', rfl⟩ := hw
      rw [Set.mem_singleton_iff] at ha ha'
      subst ha ha'
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have e : (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [term_eq, pair_mul, one_mul, one_mul]
      show (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) ∈ intAt D P
      rw [e]
      refine ⟨GlobalTheory.FinPlLoc.pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [GlobalTheory.FinPlLoc.finPart_pair]
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, b, rfl⟩
      rw [map_mul]; exact mul_mem (hβi v) (hαi v)
    | zero =>
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      exact intAt_zero P
    | add w₁ w₂ _ _ h₁ h₂ =>
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      exact intAt_add h₁ h₂
    | neg w _ h =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
      exact intAt_neg h
  | zero =>
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact intAt_zero P
  | add z₁ z₂ _ _ h₁ h₂ =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact intAt_add h₁ h₂
  | neg z _ h =>
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    exact intAt_neg h

theorem pairing_mem_at : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) :=
  fun _ S L hL v z w hz hw => pairing_mem S L hL (· = v) z w hz hw

end GlobalTheory.LatPairInt
