import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OtherPlaces

theorem conj_mem_of_comap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {w w' : HeightOneSpectrum (𝓞 E)}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
      w'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) (hne : w ≠ w') :
    ∀ c ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj E c ∈ w'.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ w'.asIdeal ∪
      (w'.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom : Ideal (𝓞 E)) := by
    intro y hy
    obtain ⟨x, hx⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E
      (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by simp [mul_comm])
    have hx' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x = y * IsCMField.ringOfIntegersComplexConj E y :=
      RingOfIntegers.ext hx
    have h1 : x ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
      rw [Ideal.mem_comap, hx']; exact Ideal.mul_mem_right _ _ hy
    rw [h, Ideal.mem_comap, hx'] at h1
    exact w'.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact absurd (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1)) hne
  · exact fun c hc => h1 hc

theorem over_ne : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) →
    ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t →
      (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  intro D T L μ0 hL hPg t s hs hsQ
  refine ⟨fun PP hPP => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => hs ?_⟩,
    fun PP hPP hne => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => ?_⟩⟩
  · obtain ⟨k, v, rfl⟩ := (hPg PP).1 hPP
    exact ⟨D.naut.plGw k v, congrArg HeightOneSpectrum.asIdeal e, k, D.naut.plGw_over k v⟩
  · letI := D.host.isCMField_hostE
    refine (hL.Q_pl t s.w hsQ).2 PP hPP fun c hc => ⟨_, conj_mem_of_comap_eq
      (s.w_under.trans (congrArg HeightOneSpectrum.asIdeal e).symm) hne.symm c hc, rfl⟩

end GlobalTheory.OtherPlaces
