import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.OrbitMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.HermitianFormStandardFrameVanishes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IndexFormulaOfSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.MemSecondProjectionIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalLatticeOfGlobal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SplitB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.MeasurableConjugateCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.NonDeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

def StepCT : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E)) (T : F)
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)),
    LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 → P.IsStd σ J T → etaV (E := E) v = 1 →
    LocMassOrdW.IsLatLoc v Λ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g →
    (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 →
    μS (KSv σ J v P Λ) = μS0 (stabilizerCompact σ J v Λ P) * sdE (E := E) ψ v (UIdx r) (UO v r)

theorem stepCT_of (hKU : KUnip1) : StepCT := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μG μS μS0 Fr hP hEta hL hg hgv hN ha
  have hPr : IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P))) := by
    have := Fr.2.2.2.2.2.2.2.2.2
    rwa [one_smul] at this
  have key := LocMassOrdSC.stepC_at σ J ψ v P Λ μG μS μS0 1 Fr
    (LocMassOrdSC.measConj σ J v Λ Fr.2.2.1 1) (LocMassOrdSC.measurable_unipotent_orbit v r)
    (unipSplitF PI.LocMassTypS.split_reduction (PI.LocMassTypL.latStd_of PI.LocMassTypS.split_reduction)
      σ J ψ v P Λ T Fr.1 hP Fr.2.2.1 Fr.2.2.2.1 hEta hL hPr)
    (fun x hx => by
      obtain ⟨s, hs, hsx⟩ := hKU σ J ψ v g P Λ T μS0
        ⟨Fr.1, hP, Fr.2.2.1, Fr.2.2.2.1, hg, hgv, hN, hEta, hPr, hL, Fr.2.2.2.2.2.2.1, ha⟩ x hx
      exact ⟨s, hsx, by simpa using hs⟩)
  rwa [KSv_eq, stabilizer_compact_eq] at key

theorem local_mass_type_formula (hOm : StepOm) (hC : StepCT) (hIdx : StepIdx) (hG : LatOfGlob)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ := by
  intro hStd T T' hP hP' hSD hUn hGL hg hgv hN hEta hκ μG hμG μS hμS hTie μS' hμS' hTie' hPr hPr'
  have hL := hG v Λ hGL
  obtain ⟨κ, hκK, hκc⟩ := hκ
  obtain ⟨μS0, hμS0, hCm, hPU⟩ := hTie
  obtain ⟨μS0', hμS0', hCm', hPU'⟩ := hTie'
  have Fr : LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 :=
    ⟨hStd, ⟨T, hP⟩, hSD, hUn, hμG, hμS, hμS0, hCm, hPU, by rw [one_smul]; exact hPr⟩
  have Fr' : LocMassOrdW.FrameHyp σ J ψ v P' Λ μG μS' μS0' 1 :=
    ⟨hStd, ⟨T', hP'⟩, hSD, hUn, hμG, hμS', hμS0', hCm', hPU', by rw [one_smul]; exact hPr'⟩
  have ha : (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 := by
    rw [← stabilizer_compact_eq]; exact LocMassOrdND.nondegenerate_lattice σ J ψ v P Λ μG μS μS0 1 Fr hL
  have ha' : (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0 := by
    rw [← stabilizer_compact_eq]; exact LocMassOrdND.nondegenerate_lattice σ J ψ v P' Λ μG μS' μS0' 1 Fr' hL
  have h1 := hC σ J ψ v g P Λ T μG μS μS0 Fr hP hEta hL hg hgv hN ha
  have h2 := hC σ J ψ v g P' Λ T' μG μS' μS0' Fr' hP' hEta hL hg hgv hN ha'
  have h1r := congrArg ENNReal.toReal h1
  have h2r := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_mul] at h1r h2r
  have hu := PI.LocMassTypU.unitary_local_mass_identity σ J ψ v (r := r) g hStd hg hgv
  rw [hu, h1r, h2r]
  have hM := hOm σ J ψ v g P P' Λ T T' κ μG μS0 μS0' hStd hP hP' hSD hUn hg hgv hN hEta hκK hκc
    hμG hμS0 hCm hμS0' hCm' hPr hPr' hL ha ha'
  have hi := hIdx σ J ψ v g P Λ T μG μS0 hStd hP hSD hUn hg hgv hN hEta hPr hμG hL hμS0 ha
  exact arith _ _ _ _ _ _ _ _ _ _ hM rfl rfl hi ha ha' (PI.LocMassTypU.positivity_of_local_mass σ J ψ v g hStd hg hgv)

theorem local_mass_type_of_parts (hRK : RightK) (hKU : KUnip1)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ :=
  local_mass_type_formula
    (stepOm_ofK (stepW_of PI.LocMassTypS.split_reduction (PI.LocMassTypL.latStd_of PI.LocMassTypS.split_reduction)
      saturated_split_lattice transitiveOverLocalRings) PI.LocMassTypM.orbit_measure hRK LocMassOrdSF.orbit_measure_sFinite)
    (stepCT_of hKU) (PI.LocMassTypL.index_formula_of_split PI.LocMassTypS.split_reduction hKU)
    PI.LocMassTypL.local_lattice_of_global σ J ψ v g P P' Λ

end PI.LocMassTypW
