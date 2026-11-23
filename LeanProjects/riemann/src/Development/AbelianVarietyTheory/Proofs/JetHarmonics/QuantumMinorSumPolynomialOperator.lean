import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate

namespace GlobalTheory.HatNF.MinorPoly

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminor_words (k r m : ℕ) (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ⊤ UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        qminorOp (EabH (Hpk k r)) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin m) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin m => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin m))).toList.flatMap
      (fun σ => (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map
        fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨fun X hX => (this.1 X hX).1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((ts σ).length : ℕ∞) f g := fun σ =>
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top (hf g hgU)
    have e1 : qminorOp (EabH (Hpk k r)) a b u f g =
        ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT, ts, List.map_ofFn]
      rfl
    rw [e1, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq (ts σ) f g hg (hloc σ), List.map_map,
      ← Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def scalarTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := w
  word_lie := hw
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right]
    simp

theorem isPolyDeg_mul_const {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) (c : ℂ) :
    U.IsPolyDeg κ fun g => P g * c := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [he g]⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simpa using hq

theorem exists_polyOp_words (m κ : ℕ) (P : B.Mat k r → ℂ) (hP : U.IsPolyDeg κ P)
    (L : List (ℂ × List (B.Mat k r))) (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) :
    ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F g,
      B.opApply Θ F g = P g • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction L with
  | nil => exact ⟨[], fun T hT => by simp at hT, fun F g => by simp [B.opApply]⟩
  | cons cw L ih =>
    obtain ⟨Θ, hΘ, he⟩ := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    have h0 := hL cw List.mem_cons_self
    refine ⟨scalarTerm (fun g => P g * cw.1) cw.2 h0.1 :: Θ, ?_, fun F g => ?_⟩
    · intro T hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact ⟨h0.2, fun g => P g * cw.1, isPolyDeg_mul_const hP _, fun _ => rfl, fun _ => rfl⟩
      · exact hΘ T hT
    · have h1 := he F g
      simp only [B.opApply, List.map_cons, List.sum_cons] at h1 ⊢
      rw [h1, smul_add, smul_smul]
      rfl

end terms

theorem minor_polyOp : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  intro Wp Wq _ _ _ _ _ _ k r m κ ι _ a b u co hco
  choose L hL hE using fun i => qminor_words k r m (a i) (b i) u
  choose Θ hΘ hA using fun i => exists_polyOp_words (Wp := Wp) (Wq := Wq) m κ (co i) (hco i) (L i) (hL i)
  refine ⟨(Finset.univ : Finset ι).toList.flatMap Θ, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 hT
    exact hΘ i T hi
  · intro F g hg V _ hgV hF
    unfold B.opApply
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE i _ _ F hF g ⟨hg, hgV⟩ hg, ← hA i F g]
    rfl

end

end GlobalTheory.HatNF.MinorPoly
