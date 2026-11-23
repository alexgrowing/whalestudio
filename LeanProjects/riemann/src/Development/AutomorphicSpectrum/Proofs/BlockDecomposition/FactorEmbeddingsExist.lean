import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def localization₂ (a b : ℕ) (w : Pl E) : (GLw a w × GLw b w) →* Hf E a b :=
  (locGL E a w).prodMap (locGL E b w)

theorem continuous_locP (w : Pl E) : Continuous (localization₂ (E := E) a b w) :=
  ((GlobalTheory.EulerTw.continuous_locGL_spl E a w).comp continuous_fst).prodMk
    ((GlobalTheory.EulerTw.continuous_locGL_spl E b w).comp continuous_snd)

theorem atW_locP (w : Pl E) (m : GLw a w × GLw b w) : atW w (localization₂ a b w m) = m :=
  Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)

theorem component_localEmbedding_eq_one_of_ne {v w : Pl E} (h : v ≠ w) (m : GLw a w × GLw b w) : atW v (localization₂ a b w m) = 1 :=
  Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)

theorem pc_thF_of_one {n : ℕ} {v : Pl E} {x : GL (Fin n) (Af E)}
    (h : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x = 1) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = 1 := by
  refine (GlobalTheory.EulerTwU.pc_thF v x).trans ?_
  rw [h]
  exact (congrArg _ (map_one (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv v)))).trans (map_one _)

theorem component_conj_localEmbedding_eq_one_of_ne {v w : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ w) (m : GLw a w × GLw b w) :
    atW v (thP E a b (localization₂ a b w m)) = 1 := by
  exact Prod.ext (pc_thF_of_one (pLoc_locGL_of_ne h m.1)) (pc_thF_of_one (pLoc_locGL_of_ne h m.2))

def localEmb (a b : ℕ) {S : Set (Pl E)} : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b
  | .inl w => localization₂ a b w.1
  | .inr w => (thP E a b).comp (localization₂ a b w.1)

theorem continuous_factorEmb {S : Set (Pl E)} (i : Slot S) : Continuous (localEmb (E := E) a b i) := by
  rcases i with w | w
  · exact continuous_locP w.1
  · exact GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP.comp (continuous_locP w.1)

theorem cp_factorEmb {S : Set (Pl E)} (i : Slot S) (m : GLw a i.pl × GLw b i.pl) : i.cp a b (localEmb a b i m) = m := by
  rcases i with w | w
  · exact atW_locP w.1 m
  · change atW w.1 (thP E a b (thP E a b (localization₂ a b w.1 m))) = m
    rw [GlobalTheory.CompanionTheory.FinLevelTw.thP_thP]
    exact atW_locP w.1 m

theorem cp_factorEmb_of_ne {S : Set (Pl E)} (hS : IsSection S) (i j : Slot S) (m : GLw a i.pl × GLw b i.pl) (hij : i ≠ j) :
    j.cp a b (localEmb a b i m) = 1 := by
  rcases i with w | w <;> rcases j with v | v
  · exact component_localEmbedding_eq_one_of_ne (fun h => hij (congrArg Sum.inl (Subtype.ext h.symm))) m
  · refine component_conj_localEmbedding_eq_one_of_ne (fun h => ?_) m
    exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (h ▸ w.2)
  · refine component_conj_localEmbedding_eq_one_of_ne (fun h => ?_) m
    refine GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 ?_
    have h' : GlobalTheory.EulerTw.cPl E v.1 = w.1 := h
    rw [← h', GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    exact v.2
  · change atW v.1 (thP E a b (thP E a b (localization₂ a b w.1 m))) = 1
    rw [GlobalTheory.CompanionTheory.FinLevelTw.thP_thP]
    exact component_localEmbedding_eq_one_of_ne (fun h => hij (congrArg Sum.inr (Subtype.ext h.symm))) m

theorem finGL_thF (n : ℕ) (k : GL (Fin n) (Af E)) :
    finGL E n (thF E n k) = thetaGL n (conjAd E) (finGL E n k) :=
  (GlobalTheory.ThetaPull.thetaA_finGL k).symm

end GlobalTheory.CompanionTheory.FinActS

theorem GlobalTheory.CompanionTheory.FinActS.exists_factorEmb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) {S : Set (Pl E)} (hS : IsSection S),
    ∃ e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b,
      (∀ i, Continuous (e i)) ∧ (∀ (i : Slot S) m, i.cp a b (e i m) = m) ∧ (∀ (i j : Slot S) m, i ≠ j → j.cp a b (e i m) = 1) ∧
      (∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2)) ∧
      ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2) := by
  intro E _ _ _ a b S hS
  refine ⟨localEmb a b, continuous_factorEmb, cp_factorEmb, fun i j m h => cp_factorEmb_of_ne hS i j m h, fun w m => rfl, fun w m => ?_⟩
  exact Prod.ext (finGL_thF a _) (finGL_thF b _)

end
