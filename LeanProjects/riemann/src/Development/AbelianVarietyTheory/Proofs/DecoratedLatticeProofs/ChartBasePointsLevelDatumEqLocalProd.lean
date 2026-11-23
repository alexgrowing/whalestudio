import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnConditionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumnsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

open Classical in

theorem phiT_base_eq_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  intro B X I _ _ l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ j hj α γ z
  have hj0 : j ≤ B.R.m := Nat.le_of_succ_le hj
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hLj, hSj⟩ := hS2 j hj0
  obtain ⟨hLj', hSj'⟩ := hS2 (j + 1) hj
  have hG := GlobalTheory.T.phi_one_eq_one_iff_column_condition B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 (B.fields.conjO (X.piT u))
    (A.p0 j α).1.1.deco.2 (A.p0 (j + 1) γ).1.1.deco.2 (hA.base j hj0 α).2 (hA.base (j + 1) hj γ).2
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA j hj0 α P x hx r hr c hc)
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA (j + 1) hj γ P x hx r hr c hc)
    (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)
  have hLoc : ∀ i, (Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) ↔
      ColCond (e i).1 (B.fields.conjO (X.piT u)) (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) :=
    fun i => GlobalTheory.T.maps_rd_iff_colCond_toHom (p i) (e i).1 (he i) _ _ (β j i) (β (j + 1) i) (Q j i) (Q (j + 1) i) (L j) (L (j + 1)) _ hLj hLj'
      (hSj i).1 (hSj' i).1 (hSj i).2 (hSj' i).2 z
  have key : (∀ P : (B.primes X).vT u, ColCond P.1 (B.fields.conjO (X.piT u))
      (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) ↔
      ∀ i ∈ J, Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) := by
    refine ⟨fun h i _ => (hLoc i).2 (h (e i)), fun h P => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective P
    exact (hLoc i).1 (h i (hJ.all i))
  have hprod : ∀ (J' : List ι) (c : ι → Prop), (J'.map fun i => (if c i then (1 : ℂ) else 0)).prod =
      if ∀ i ∈ J', c i then 1 else 0 := by
    intro J' c
    induction J' with
    | nil => simp
    | cons i J' ih =>
      rw [List.map_cons, List.prod_cons, ih]
      by_cases h : c i <;> simp [h]
  have hv : ∀ x, Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 1 ∨
      Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 0 := by
    intro x
    unfold Formalism.L2.Col.phiT
    split_ifs <;> simp
  simp only [phiOne]
  rw [hprod]
  split_ifs with hc
  · rw [hG.2 (key.2 hc), map_one]
  · rcases hv (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z) with h1 | h0
    · exact absurd (key.1 (hG.1 h1)) hc
    · rw [h0, map_zero]

end GlobalTheory.PhiOneVal

end
