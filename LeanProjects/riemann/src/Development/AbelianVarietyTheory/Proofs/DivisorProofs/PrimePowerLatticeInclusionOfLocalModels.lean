import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpoFrobIndep
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lIncl_of_models : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z w ι _ _ P W hN hl hR fr cj I X hC hX
  obtain ⟨hH, hL, hW, -⟩ := hN
  obtain ⟨hW', hJ⟩ := GlobalTheory.expo_frob_indep P hH hL ι W hW fr cj
  have hEq := hJ _ hl hR
  apply hC
  intro i
  obtain ⟨hu, hLk⟩ := hX i
  have hWI := Formalism.CohomologicalDescent.ShortWeightBounds.weight_inputs_of_linkage_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hR.1 hLk
  have h := (Formalism.CohomologicalDescent.Top.inclusion_w_seven_real_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hu hR.1 hWI).1
  unfold reFr at h
  rw [hEq] at h
  exact h

end GlobalTheory.ExpTie
