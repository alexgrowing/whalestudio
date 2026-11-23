import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerDecAtRef

open Formalism.BasicNotions in

theorem vAdd_nonneg_of_int {K : Type} [Field K] [NumberField K] (la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) : 0 ≤ vAdd la (a : K) := by
  have h : la.valuation K (a : K) ≤ 1 := la.valuation_le_one a
  unfold vAdd
  rcases eq_or_ne (la.valuation K (a : K)) 0 with h0 | h0
  · rw [h0, WithZero.log_zero]; simp
  · have h1 : WithZero.log (la.valuation K (a : K)) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp h0]
      simpa using h
    exact neg_nonneg.mpr h1

end GlobalTheory.PerDecAtRef

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PerDecAtRef.perDec0At_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → Formalism.MainNotions.RT.PeriodPointConditions.PerDec0At F := by
  intro B X I hI l Z hZ u Ch chOf F hF
  intro x hx G hG c
  classical
  obtain ⟨y0, hy0, hrd⟩ := hZ.ref u G hG c
  have hpr : ∀ w, ((I.perIn u I.mu0).per B.fields.emb B.embLL (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)).period w
      (((I.rec7 l Z).eMt u).symm G) = (I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0)
      (F.jM (((I.rec7 l Z).eMt u).symm G)) w := by
    intro w
    have hper := F.per
    unfold Formalism.L2.Forms.PerTie at hper
    exact hper.2.2 w _
  have key := GlobalTheory.T.classPairing_integral_form_row_isIntegral B.fields.emb B.embLL (I.perIn u I.mu0) (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)
    (l.fmL u I.mu0).famP (((I.rec7 l Z).eMt u).symm G) (F.jM (((I.rec7 l Z).eMt u).symm G)) hpr c y0 ?ha ?hb
  case ha =>
    clear hpr hZ hI hx hG hrd hF
    have hL : (I.perIn u I.mu0).S'.Lsh c.fst ((I.perIn u I.mu0).S'.rep c) = (((I.stX I.mu0).rep c).1.1.deco).1.N :=
      GlobalTheory.PeriodOnStep.Lsh_eq_N _
    rw [hL]
    exact hy0
  case hb =>
    clear hpr hZ hI hx hG hy0 hF
    convert hrd using 2
  obtain ⟨a, ha⟩ := key x hx
  refine ⟨(a : B.fields.K), ?_, ?_⟩
  · have hw := hF.eW
    have hsingle : ∀ (dec : ∀ c' : ((I.rec7 l Z).fm u).clsP, Decidable (c' = c)) (v : ((I.rec7 l Z).mem u).P.Wrow),
        F.valP.eW.symm (fun c' => @ite _ (c' = c) (dec c') (F.valP.eW v c') 0) =
          fun (c' : (I.perIn u I.mu0).S'.Cl) => if c' = c then v c' else 0 := by
      intro dec v
      apply F.valP.eW.injective
      rw [LinearEquiv.apply_symm_apply]
      funext c' s
      erw [hw _ c' s ⟨s.1, s.2⟩ rfl]
      by_cases h : c' = c
      · rw [if_pos h, if_pos (show @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        erw [hw v c' s ⟨s.1, s.2⟩ rfl]
      · rw [if_neg h, if_neg (show ¬ @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        rfl
    unfold Formalism.MainNotions.RT.PeriodPointConditions.pcL Formalism.MainNotions.RT.PeriodPointConditions.resC
    rw [hsingle, hsingle]
    clear key hpr hrd hy0 hG hZ hI hx hsingle hw hF
    refine ha.trans ?_
    congr! 4
    exact congrArg (fun f => ⇑((I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0) f))
      (funext fun c' => by by_cases h : c' = c <;> simp [h])
  · intro w
    right
    exact GlobalTheory.PerDecAtRef.vAdd_nonneg_of_int _ a
