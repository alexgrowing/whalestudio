import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory

theorem adicIntegers_red_eq_zero_iff {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : ℕ) (hg : g.Prime)
    (red : v.adicCompletionIntegers K →+* ZMod g) (y : v.adicCompletionIntegers K) :
    red y = 0 ↔ Valued.v (y : v.adicCompletion K) < 1 := by
  have : Fact g.Prime := ⟨hg⟩
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective red (ZMod.ringHom_surjective red))
  rw [← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne y.2 h, ne_of_lt⟩

theorem exists_ringHom_adicIntegers {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {R : Type} [CommRing R] (f : R →+* v.adicCompletion K)
    (hf : ∀ a, Valued.v (f a) ≤ 1) :
    ∃ j : R →+* v.adicCompletionIntegers K, ∀ a, (j a : v.adicCompletion K) = f a :=
  ⟨f.codRestrict (v.adicCompletionIntegers K) hf, fun _ => rfl⟩

theorem zmod_iso_comp_eq_mk {R : Type} [CommRing R] (I : Ideal R) (g : ℕ) (φ : R →+* ZMod g)
    (hφ : ∀ a ∈ I, φ a = 0) (iso : ZMod g ≃+* R ⧸ I) (u : R) :
    iso (φ u) = Ideal.Quotient.mk I u := by

  have hid : (Ideal.Quotient.lift I φ hφ).comp (iso : ZMod g →+* R ⧸ I) = RingHom.id (ZMod g) :=
    Subsingleton.elim _ _
  have h : φ u = iso.symm (Ideal.Quotient.mk I u) := by
    simpa using congrArg (fun F : ZMod g →+* ZMod g => F (iso.symm (Ideal.Quotient.mk I u))) hid
  rw [h, RingEquiv.apply_symm_apply]

theorem adicIntegers_red_eq_iff {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : ℕ) (hg : g.Prime)
    (red : v.adicCompletionIntegers K →+* ZMod g) (y x : v.adicCompletionIntegers K) :
    Valued.v ((y : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 ↔ red x = red y := by
  have h := adicIntegers_red_eq_zero_iff v g hg red (y - x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm.trans eq_comm

theorem splitPlace_red_eq_reduction : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ∀ (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod g) (iso : ZMod g ≃+* kP s.w) (x : s.v.adicCompletionIntegers (maximalRealSubfield L)) (u : 𝓞 L), Valued.v (s.i (u : L) - (x : s.v.adicCompletion (maximalRealSubfield L))) < 1 ↔ iso (red x) = Ideal.Quotient.mk s.w.asIdeal u := by
  intro L _ _ _ s g hg red iso x u

  obtain ⟨j, hj⟩ := exists_ringHom_adicIntegers s.v
    ((s.i : L →+* s.v.adicCompletion (maximalRealSubfield L)).comp (algebraMap (𝓞 L) L))
    (fun a => s.split_le_one a)
  have hj' : ∀ a : 𝓞 L, (j a : s.v.adicCompletion (maximalRealSubfield L)) = s.i (a : L) :=
    fun a => hj a

  have hφ : ∀ a ∈ s.w.asIdeal, (red.comp j) a = 0 := by
    intro a ha
    have hlt : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    exact (adicIntegers_red_eq_zero_iff s.v g hg red (j a)).2 (by rw [hj' a]; exact hlt)
  have key := zmod_iso_comp_eq_mk s.w.asIdeal g (red.comp j) hφ iso u
  have h4 := adicIntegers_red_eq_iff s.v g hg red (j u) x
  rw [hj' u] at h4
  rw [← key, iso.injective.eq_iff]
  exact h4

end GlobalTheory
