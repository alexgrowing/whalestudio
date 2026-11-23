import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem perDecTwT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) (Y : DivX (I.rec7 l Z)), I.StdTw l Z l0 t → ∀ u a ha, GlobalTheory.PerQ.PerDecTwT Y t u a ha := by
  intro B X I hI l Z l0 hR cf nch tp C t Y hS u a ha x hx F hF c
  have hP := (t.ptE.per u a ha).2.2
  classical
  have hres : ∀ z, GlobalTheory.PerQ.resCTw t u a ha c z = fun c' => if c' = c then z c' else 0 := by
    intro z
    apply (t.pt.val u a ha).eW.injective
    rw [GlobalTheory.PerQ.resCTw, LinearEquiv.apply_symm_apply]
    funext c' s
    have e1 := hS.2.2.eW u a ha (fun c' => if c' = c then z c' else 0) c' s s rfl
    have e2 := hS.2.2.eW u a ha z c' s s rfl
    refine Eq.trans ?_ e1.symm
    split_ifs
    all_goals first | exact e2 | rfl | (exfalso; contradiction)
  obtain ⟨y, hy, hyv⟩ := hR.tw u a F hF c
  have hyQ : y ∈ nabAt B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c)) := by
    have := GlobalTheory.PeriodOnStep.Lsh_eq_N ((I.stX a).rep c).1.1.deco
    show y ∈ nabAt _ _ (((I.stX a).rep c).1.1.deco.1.Lsh)
    rw [this]; exact hy
  obtain ⟨b, hb⟩ := @GlobalTheory.T.classPairing_integral_form_row_isIntegral _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL _ _ (I.perIn u a) (l.ch u a) (l.per u a) (B.hcW u)
    (l.fmL u a).famP (((I.rec7 l Z).eMtTw u a).symm F) (t.ptE.jM u a (((I.rec7 l Z).eMtTw u a).symm F))
    (fun w => hP w _) c (fun p q => Classical.propDecidable (p = q)) y hyQ hyv x hx
  refine ⟨(b : B.fields.K), ?_, fun w _ => ?_⟩
  · show B.embLL (b : B.fields.K) = _
    rw [hb, GlobalTheory.PerQ.pcLTw, hres, hres]
    rfl
  · by_cases h0 : (b : B.fields.K) = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      unfold vAdd
      have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := (I.rec7 l Z).what₂.LL) ((I.rec7 l Z).plEq w) b
      have h2 := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 h0) one_ne_zero).2 h
      rw [WithZero.log_one] at h2
      exact neg_nonneg.mpr h2

end GlobalTheory.PerTwClose
