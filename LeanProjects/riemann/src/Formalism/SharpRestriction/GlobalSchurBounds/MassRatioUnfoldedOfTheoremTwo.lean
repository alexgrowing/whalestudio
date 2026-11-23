import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def MassRatioUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D

def GenusMassUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.DefiniteVolumeEqMass D

theorem mass_ratio_unfolded_of_theorem_two (D : D7) (h : StandardLattice.Conclusion2 D) : StandardLattice.VolumeRatio₂ D := by
  let _ := D.host.cmStar
  intro W P Q hS hsig hr s hs
  obtain ⟨x, hx, W', ι, h1, h2, h3, h4, h5⟩ := h W P Q hS hsig hr s hs
  refine ⟨x, hx, W', ι, h1, h2, h3, h4, ?_⟩
  have key := Formalism.HermitianLattices.GenusMassVolumes.global_arithmetic_identity D.R.f W.rank D.host.v (Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)
    (by omega) (StandardLattice.host_v_pos D) (StandardLattice.lVal_pos D _ (by omega))
  rw [StandardLattice.mass_ratio_eq] at h5
  have e : D.vol W / D.vol W' =
      (((2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ)) ^ D.R.f *
        ((2 * D.host.v) ^ D.R.f) ^ ((1 : ℝ) / 2 - W.rank) / Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)⁻¹ :=
    h5.trans key.symm
  calc D.vol W' / D.vol W = (D.vol W / D.vol W')⁻¹ := (inv_div _ _).symm
    _ = _ := by rw [e, inv_inv]

theorem mass_ratio_unfolded_iff (D : D7) : StandardLattice.VolumeRatio₂ D ↔ StandardLattice.Conclusion2 D :=
  ⟨StandardLattice.volumeMass_of_unfolding D, mass_ratio_unfolded_of_theorem_two D⟩

theorem mass_ratio_of_true_volume_ratio (D : D7) (hV : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrue D) : MassRatioUnderVolume D := by
  intro hT
  refine mass_ratio_unfolded_of_theorem_two D ?_
  intro W P Q hW hs hr s hsP
  obtain ⟨x, hx, W', ι, hι, hrg, hW', hs', hrat⟩ := hV W P Q hW hs hr s hsP
  refine ⟨x, hx, W', ι, hι, hrg, hW', hs', ?_⟩
  have hs'' : ∀ τ, W'.sig τ = ((if s then P - 1 else P), (if s then Q else Q - 1)) := by
    intro τ
    rw [hs' τ]
    cases s <;> simp
  obtain ⟨⟨μ, hμ⟩, h1⟩ := hT W P Q hW hs
  obtain ⟨⟨𝓕, h𝓕⟩, h2⟩ := h1 μ hμ
  obtain ⟨⟨μ', hμ'⟩, h1'⟩ := hT W' _ _ hW' hs''
  obtain ⟨⟨𝓕', h𝓕'⟩, h2'⟩ := h1' μ' hμ'
  have e1 : μ 𝓕 = ENNReal.ofReal (D.vol W) := h2 𝓕 h𝓕
  have e2 : μ' 𝓕' = ENNReal.ofReal (D.vol W') := h2' 𝓕' h𝓕'
  have e := hrat μ 𝓕 μ' 𝓕' hμ h𝓕 hμ' h𝓕'
  rw [e1, e2, ENNReal.toReal_ofReal (D.vol_pos W).le, ENNReal.toReal_ofReal (D.vol_pos W').le] at e
  exact e

theorem genus_mass_of_class_decomposition (D : D7) (hG : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassStd D)
    (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.DefClassDecomp D) : GenusMassUnderVolume D :=
  fun hT => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT hG hC

theorem auxb_of_massRatio_of_genusMass_of_volTie (D : D7) (hU : MassRatioUnderVolume D) (hv : GenusMassUnderVolume D) (hT : StandardLattice.VolTie D) : StandardLattice.MassRatio₂ D :=
  StandardLattice.massRatio_of_definiteVolume D (StandardLattice.volumeMass_of_unfolding D (hU hT)) (hv hT)

theorem volumeY0EqualsMass_of_massRatio_of_genusMass (D : D7) (hU : MassRatioUnderVolume D) (hv : GenusMassUnderVolume D) (hT : StandardLattice.VolTie D) : StandardLattice.BaseVolumeEqualsMass D :=
  StandardLattice.volumeY0EqualsMass_of_aux2v D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU hT)) (hv hT))

theorem volTie_of_realTied (D : D7) (h : Formalism.L2.Theta.RealTied D) : StandardLattice.VolTie D := by
  intro W P Q hW hs
  have hv := h.vol W hW
  simp only [hs] at hv
  exact hv

variable {eps : ℝ}

theorem mass_ratio_family_of_volume (Fm : FamP eps) (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D)
    (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie) : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂ := by
  obtain ⟨x0, hx⟩ := tVol
  exact ⟨x0, fun x h1 h2 i => auxb_of_massRatio_of_genusMass_of_volTie _ (hU _) (hv _) (hx x h1 h2 i)⟩

theorem volume_mass_family_of_volume (Fm : FamP eps) (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D)
    (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie) : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass := by
  obtain ⟨x0, hx⟩ := tVol
  exact ⟨x0, fun x h1 h2 i => volumeY0EqualsMass_of_massRatio_of_genusMass _ (hU _) (hv _) (hx x h1 h2 i)⟩

theorem tVol_of_real (Fm : FamP eps) (h : flipTwoThree.fam0 Fm Formalism.L2.Theta.RealTied) : flipTwoThree.fam0 Fm StandardLattice.VolTie := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x h1 h2 i => volTie_of_realTied _ (hx x h1 h2 i)⟩

theorem linkGLOBAL7_tiedV (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D) (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie)
    (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  exact linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 (mass_ratio_family_of_volume Fm hU hv tVol) (volume_mass_family_of_volume Fm hU hv tVol) h3
    hZa hZb tCV hW hμ hI hR hB

end Formalism.MainNotions.RT

end
