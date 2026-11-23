import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ModelIdentificationHolds
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PbSmithLam
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TauP

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem qPh_proved : QPh :=
  qPh_of_rest tauP smithP

theorem contraction_standard_lattice_holds (hCO : CartanOnto) : ContractionStandardLattice :=
  contraction_of_pairing_GL qPh_proved hCO

theorem restCloudMaps_proved (hCD : CartanDomain) (hCO : CartanOnto) (hIncl : DualHeightInclusion) : RestCloudMaps :=
  cloud_maps_of_contraction (contraction_standard_lattice_holds hCO) hCD hCO hIncl

theorem theorem_I_closed_form_holds (D : Formalism.BasicNotions.D7) : SecondPartClosed D :=
  theorem_I_of_pairing_GL D qPh_proved

theorem theorem_I_family_form_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : SecondPartFamilyClosed Fm := by
  intro hA
  by_cases hne : ∃ x, Nonempty (Fm.Ix x)
  · obtain ⟨x, ⟨i⟩⟩ := hne

    have hD : AdmBE (Fm.D x i) := by
      intro Cc hCc
      obtain ⟨T0, hT0, h0⟩ := hA Cc hCc
      refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
      obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
      refine ⟨T1, hT1, fun CE1 CE2 Cm e1 e2 e3 => ?_⟩
      obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm e1 e2 e3
      refine ⟨T2, hT2, fun CH hCH => ?_⟩
      obtain ⟨CA, Ckap, Ct, Cs, a1, a2, a3, a4, hP⟩ := h2 CH hCH
      exact ⟨CA, Ckap, Ct, Cs, a1, a2, a3, a4, hP x i⟩

    obtain ⟨T0, hT0, h0⟩ := theorem_I_closed_form_holds (Fm.D x i) hD
    refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
    obtain ⟨T2, C, hT2, hC, h2⟩ := h0 C₀ hC₀
    refine ⟨T2, C, hT2, hC, fun CH hCH => ?_⟩
    intro x' i'
    exact h2 CH hCH
  · refine ⟨1, one_pos, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun CH _ => ?_⟩⟩
    intro x i
    exact absurd ⟨x, ⟨i⟩⟩ hne

theorem stmt2EDF_proved (Fm : Formalism.MainNotions.DFamP) : UniformEpsilonConclusionClosedOfHypothesesClosed Fm := by
  intro hA
  by_cases hne : ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52) (x : _), Nonempty ((Fm ε h0 h1).Ix x)
  · obtain ⟨ε, h0, h1, x, ⟨i⟩⟩ := hne
    have hD : AdmBE ((Fm ε h0 h1).D x i) := by
      intro Cc hCc
      obtain ⟨T0, hT0, k0⟩ := hA Cc hCc
      refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
      obtain ⟨T1, hT1, k1⟩ := k0 C₀ hC₀
      refine ⟨T1, hT1, fun CE1 CE2 Cm e1 e2 e3 => ?_⟩
      obtain ⟨T2, hT2, k2⟩ := k1 CE1 CE2 Cm e1 e2 e3
      refine ⟨T2, hT2, fun CH hCH => ?_⟩
      obtain ⟨CA, Ckap, Ct, Cs, a1, a2, a3, a4, hP⟩ := k2 CH hCH
      exact ⟨CA, Ckap, Ct, Cs, a1, a2, a3, a4, hP ε h0 h1 x i⟩
    obtain ⟨T0, hT0, k0⟩ := theorem_I_closed_form_holds ((Fm ε h0 h1).D x i) hD
    refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
    obtain ⟨T2, C, hT2, hC, k2⟩ := k0 C₀ hC₀
    refine ⟨T2, C, hT2, hC, fun CH hCH => ?_⟩
    intro ε' h0' h1' x' i'
    exact k2 CH hCH
  · refine ⟨1, one_pos, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun CH _ => ?_⟩⟩
    intro ε h0 h1 x i
    exact absurd ⟨ε, h0, h1, x, ⟨i⟩⟩ hne

end Formalism.MainNotions.flipOneThree.Pf
