import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientTranslationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientProductFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyPlaceAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyUnipotentInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyLeviShiftStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory

theorem weight_split_places : GlobalTheory.Published.LabesseWaldspurger → ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ Tr, ∃ C Dd : Finset (SV (wittIndex V)) → GA D V → ℂ, (∀ Q ∈ parF (aP P) ∅, Continuous (C Q) ∧ (∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ y, C Q (m * y) = C Q y) ∧ ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ y, C Q (n * y) = C Q y) ∧ (∀ z, Dd ∅ z = 1) ∧ (∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (y * z) : ℂ) = ∑ Q ∈ parF (aP P) ∅, C Q y * Dd Q z) ∧ ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ x, weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (m * x) = weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x := by
  intro hLW D V Φ L a hG P hP Tr
  obtain ⟨⟨hEFI, hFS, hFP⟩, hY⟩ := hLW
  have hOrth : ∀ x T, IsOrth (aP P) (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x T) := fun x T =>
    ((hY D V Φ L a hG).1 x T).1.mono le_top
  have hLevi : IsLevi (aP P) := ⟨P, hP, rfl⟩
  refine ⟨fun Q y => cM (aP P) Q (expFam (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0)) 0,
    fun Q z => cP Q ∅ (expFam (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr)) 0, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    have hsub : ∀ P' ∈ parP (aP P) Q, P' ∈ parP (aP P) ∅ ∧ IsPar P' ∧ Q ⊆ P' := fun P' h' => by
      obtain ⟨h1, h2, h3⟩ := mem_parP.1 h'
      exact ⟨mem_parP.2 ⟨h1, h2, Finset.empty_subset _⟩, h1, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact GlobalTheory.T.chamber_coefficient_continuous hFS _ (aP P) hLevi Q hQ (GA D V) (fun z => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z 0 - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0)
        (fun z => (hOrth z 0).sub (hOrth 1 0))
        (fun P' hP' => ((GlobalTheory.T.truncation_family_place_additive D V Φ L a hG P' (hsub P' hP').2.1).1 0).sub continuous_const)
    · intro m hm y
      obtain ⟨h, hh⟩ := GlobalTheory.T.truncation_family_levi_shift D V Φ L a hG P hP m hm
      exact GlobalTheory.T.chamber_coefficient_translation hFS _ (aP P) hLevi Q hQ _ _ ((hOrth y 0).sub (hOrth 1 0)) h
        (fun P' hP' => by simp only [Pi.sub_apply, hh P' (hsub P' hP').1]; abel)
    · intro u hu hW n hn y
      exact GlobalTheory.T.chamber_coefficient_translation hFS _ (aP P) hLevi Q hQ _ _ ((hOrth y 0).sub (hOrth 1 0)) 0
        (fun P' hP' => by
          simp only [Pi.sub_apply, GlobalTheory.T.truncation_family_unipotent_invariant D V Φ L a hG P' (hsub P' hP').2.1 u ((hsub P' hP').2.2 hu) hW n hn,
            map_zero, add_zero])
  · intro z
    exact (GlobalTheory.T.chamber_coefficient_product_formula hEFI hFP _ (aP P) hLevi (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr) (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr)
      (fun Q => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q) (hOrth z Tr) (hOrth z Tr) (fun _ _ => rfl)).2.2
  · intro S y hy z hz
    have e := GlobalTheory.T.chamber_coefficient_product_formula hEFI hFP _ (aP P) hLevi (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0) (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr)
      (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr) ((hOrth y 0).sub (hOrth 1 0)) (hOrth z Tr)
      (fun P' hP' => (GlobalTheory.T.truncation_family_place_additive D V Φ L a hG P' (mem_parF.1 hP').1).2 S y hy z hz Tr)
    exact e.1.trans e.2.1
  · intro m hm x
    obtain ⟨h, hh⟩ := GlobalTheory.T.truncation_family_levi_shift D V Φ L a hG P hP m hm
    have h0 : IsOrth (aP P) (0 : Finset (SV (wittIndex V)) → A0 (wittIndex V)) := fun _ _ _ _ => by simp
    have e : ∀ x, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x : ℂ) = cM (aP P) ∅ (expFam (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr)) 0 := fun x =>
      (GlobalTheory.T.chamber_coefficient_product_formula hEFI hFP _ (aP P) hLevi (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr) 0 (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr) (hOrth x Tr) h0
        (fun _ _ => by simp)).1
    have hE : (∅ : Finset (SV (wittIndex V))) ∈ parF (aP P) ∅ :=
      mem_parF.2 ⟨⟨by simp, by simp⟩, vecSpan_mono (Finset.empty_subset P), Finset.Subset.refl _⟩
    apply Complex.ofReal_injective
    rw [e, e]
    exact GlobalTheory.T.chamber_coefficient_translation hFS _ (aP P) hLevi ∅ hE _ _ (hOrth x Tr) h (fun P' hP' => hh P' hP' x Tr)

end GlobalTheory
