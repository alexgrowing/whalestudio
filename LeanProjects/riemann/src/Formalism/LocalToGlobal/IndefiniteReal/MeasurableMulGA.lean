import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open Formalism.L2.Theta

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem countable_GQ (V : HSp D) : Countable (GQ V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem borel_GA (V : HSp D) : BorelSpace (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem petPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) : PetPos V μ 𝓕 := by
  intro F hc hinv hne hint
  have := countable_GQ V
  have := measurableMul_GA V
  have := borel_GA V
  have := hH
  set U : Set (GA D V) := {g | F g ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUne : U.Nonempty := by
    by_contra h
    apply hne
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  have hUpos : 0 < μ U := hUo.measure_pos μ hUne
  have hnn : 0 ≤ᵐ[μ.restrict 𝓕] fun g => ‖F g‖ ^ 2 := ae_of_all _ (fun g => by positivity)
  refine lt_of_le_of_ne (integral_nonneg fun g => by positivity) ?_
  intro h0
  have hz : (fun g => ‖F g‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have hset : {g : GA D V | ¬ (‖F g‖ ^ 2 = (0 : GA D V → ℝ) g)} = U := by
    ext g
    simp [hUdef]
  have hFU : μ (U ∩ 𝓕) = 0 := by
    have h1 := ae_iff.1 hz
    rw [hset, Measure.restrict_apply hUo.measurableSet] at h1
    exact h1
  have key : U ≤ᵐ[μ] (⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) : Set (GA D V)) := by
    filter_upwards [hF.ae_covers] with x hx hxU
    obtain ⟨γ, hγ⟩ := hx
    refine Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩
    · show F ((γ : GA D V) * x) ≠ 0
      rw [hinv _ γ.2 x]
      exact hxU
    · exact hγ
  have hU0 : μ U = 0 := by
    refine le_antisymm ((measure_mono_ae key).trans ?_) bot_le
    refine (measure_iUnion_le _).trans ?_
    simp only [measure_preimage_mul, hFU, tsum_zero, le_refl]
  exact hUpos.ne' hU0

end Formalism.IndefR.PeterssonHilbertSpace

end
