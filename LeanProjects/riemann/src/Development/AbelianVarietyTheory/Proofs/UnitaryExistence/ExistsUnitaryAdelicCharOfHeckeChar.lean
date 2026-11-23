import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNearOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_det_matHom (D : D7) (V : HSp D) :
    Continuous fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have hm : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  exact Matrix.GeneralLinearGroup.continuous_det.comp hm

theorem exists_muVal : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  intro D V χ hχ hF
  obtain ⟨hex, huniq, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → χ (r g) = χ x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', χ (r (g * g')) = χ (r g) * χ (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => χ (r g)) hm
  have hcont : Continuous m := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    refine continuous_of_continuousAt_one m ?_
    intro U hU
    rw [map_one] at hU
    have hW : χ ⁻¹' U ∈ 𝓝 (1 : (AE D)ˣ) := hχ.1.continuousAt.preimage_mem_nhds (by rwa [map_one])
    obtain ⟨N, hN, hNW⟩ := GlobalTheory.Member.exists_root_near_one D _ hW
    have hN' : (fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g)) ⁻¹' N ∈ 𝓝 (1 : GA D V) :=
      (continuous_det_matHom D V).continuousAt.preimage_mem_nhds (by rwa [map_one, map_one])
    refine Filter.mem_map.2 (Filter.mem_of_superset hN' ?_)
    intro g hg
    obtain ⟨x, hxW, hx⟩ := hNW _ hg (GlobalTheory.Member.finHom_herm_det D V g).2.2
    have : m g = χ x := hval g x hx
    show m g ∈ U
    rw [this]
    exact hxW
  refine ⟨fun g => (m g : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun g => ⟨r g, hr g⟩, fun g x hx => congrArg (fun z : Circle => (z : ℂ)) (hval g x hx)⟩
  · intro g g'
    simp only [map_mul, Circle.coe_mul]
  · intro g
    exact Circle.norm_coe _
  · intro γ hγ
    obtain ⟨x, hx⟩ := hrat γ hγ
    have : m γ = 1 := (hval γ _ hx).trans (hχ.2 x)
    simp only [this, Circle.coe_one]
  · exact continuous_subtype_val.comp hcont

end GlobalTheory.Member
