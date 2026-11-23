import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnsGoodChartsMiddleStepsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceStepZeroChartsGoodStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodChartLastStepAllTuplesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

set_option maxHeartbeats 1000000 in

theorem goodCharts_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)), (∀ i hi, Finite (Ch i hi) ∧ I.IdY l Z u a i hi (eY i hi) ∧ ReadsOne I l Z u a i hi (chOf i hi) (Kc i hi) ∧ ∀ β, FunKilled ((Kc i hi) β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, ((Kc i hi) β).lev.chi κ ^ n = 1) ∧ Subsingleton (Ch 0 (Nat.zero_le _)) ∧ (∀ β, ((Kc 0 (Nat.zero_le _)) β).lev.Lb = F.to0.cls0.lev.Lb ∧ ((Kc 0 (Nat.zero_le _)) β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ ((Kc 0 (Nat.zero_le _)) β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : ((Kc 0 (Nat.zero_le _)) β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → ((Kc 0 (Nat.zero_le _)) β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, (((Kc 0 (Nat.zero_le _)) ((chOf 0 (Nat.zero_le _)) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hOk hPins l Z u Ch0 chOf0 F a Q hQ hStd

  have hS : ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch)
      (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧
        ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
    intro i hi h1
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact GlobalTheory.T.trueColumns_goodCharts_middleSteps I hOk hPins l Z u F a Q hQ hStd i hi h1 hlt
    · subst heq
      exact GlobalTheory.T.exists_good_chart_lastStep_allTuples I hOk hPins l Z u F a Q hQ hStd
  choose ChS hfin chOfS KcS hgood using hS
  obtain ⟨K0, h0a, h0b, h0c⟩ := GlobalTheory.T.trueColumnChoice_stepZero_charts_good I hOk hPins l Z u F a Q hQ hStd
  have hC := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have hE : ∀ i (hi : i ≤ B.R.m), ∃ eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi,
      I.IdY l Z u a i hi eY := by
    intro i hi
    obtain ⟨e, he, -⟩ := ((hC.2.2.2 i hi).2.2 u a).2
    exact ⟨e, he⟩
  choose eY heY using hE
  let Ch : ∀ i, i ≤ B.R.m → Type := fun i => Nat.casesOn (motive := fun i => i ≤ B.R.m → Type) i
    (fun _ => Unit) (fun j hj => ChS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
  let chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi := fun i => Nat.casesOn
    (motive := fun i => ∀ hi : i ≤ B.R.m, (I.stp u a i).Cl → Ch i hi) i
    (fun _ _ => ()) (fun j hj => chOfS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
  let Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi) := fun i => Nat.casesOn
    (motive := fun i => ∀ hi : i ≤ B.R.m, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)) i
    (fun _ => K0) (fun j hj => KcS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
  refine ⟨Ch, chOf, eY, Kc, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero =>
      refine ⟨(inferInstance : Finite Unit), heY 0 hi, h0a.1, h0a.2⟩
    | succ j =>
      exact ⟨hfin _ hi _, heY _ hi, (hgood _ hi _).1, (hgood _ hi _).2⟩
  · show Subsingleton Unit
    infer_instance
  · exact h0b
  · exact h0c

end GlobalTheory.TwU.AtTrue
