import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisCharacterAntiRamifiedExactlyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.GalTwist
theorem galoisRep_of_twist_properties_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  intro _ D l Q χ ψ₀ _ hψ hG
  classical
  obtain ⟨hker, art, ha, h⟩ := hG
  generalize hr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ₀ = r at h
  have hinj : ∀ g, r g = 1 ↔ ψ₀ g = 1 := fun g => by
    rw [← hr, MonoidHom.comp_apply]
    exact map_eq_one_iff _ (Units.map_injective (f := D.what₂.embLL.toMonoidHom) D.what₂.embLL.injective)
  have hrker : IsOpen (r.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    convert hker using 1
    ext g
    exact hinj g
  have hrc : Continuous r := GlobalTheory.HeckeGal.continuous_of_isOpen_ker' r hrker
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc1, hcm, hrr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
    obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
    have h1 : ∀ x : D.host.E, D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
      apply j.injective
      rw [hj, hc1]
      exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
    have h2 : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => j.injective (by rw [hj, hj, Complex.conj_conj])
    have hinv : ∀ x, c (c x) = x := fun x => (algebraMap D.host.E D.nd.Om).injective (by rw [← h1, ← h1, h2])
    have hc : ∀ x : D.host.E, ∃ y : D.host.E, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
      fun x => ⟨c x, by rw [RingEquiv.symm_apply_eq, h1, hinv]⟩
    choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv v).exists
    have hbb : ∀ v, bar (bar v) = v := fun v =>
      (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv (bar v)).unique (hbar _) (GlobalTheory.AntiLAdic.conjPl_symm hinv (hbar v))
    let T := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
    have key : r * r.comp (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc) = 1 := by
      refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha ℂˣ _
        (hrc.mul (hrc.comp (GlobalTheory.AntiLAdic.continuous_conjHom D.ntw.cc hc))) (T ∪ T.image bar) fun v hv A hA σ hσ => ?_
      rw [Finset.mem_union, not_or] at hv
      have a2 : χ.UnrAt v := by simpa [T] using hv.1
      have b2 : χ.UnrAt (bar v) := by
        by_contra hn
        exact hv.2 (Finset.mem_image.2 ⟨bar v, by simpa [T] using hn, hbb v⟩)
      have hA' := GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) h1 (hbar v) hA
      have hσ' := GlobalTheory.AntiLAdic.isFrob_conjHom D.ntw.cc hc hσ
      rw [← GlobalTheory.AntiLAdic.normV_conjPl (hbar v)] at hσ'
      have e3 := GlobalTheory.AntiLAdic.val_mul_val_conj c hcm.rank hcm.ne hrr χ hψ.triv (hbar v) a2 b2
      rw [h.val_eq ha a2 hA hσ, h.val_eq ha b2 hA' hσ', ← mul_inv, inv_eq_one] at e3
      show r σ * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc σ) = 1
      exact e3
    intro g g' hg
    have e : g' = GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g := AlgEquiv.ext hg
    have k : r g * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g) = 1 := DFunLike.congr_fun key g
    rw [← map_mul, hinj, map_mul, ← e] at k
    exact eq_inv_of_mul_eq_one_right k
  · intro v A hA
    rw [← not_iff_not, not_exists]
    simp only [not_and, not_not]
    rw [Finset.mem_coe, ← hψ.ram v, h.unr_iff ha hA]
    exact forall₂_congr fun σ _ => (hinj σ).symm
  · intro v hv A hA σ hσ
    rw [← hinj]
    have hcl : IsClosed ((GlobalTheory.HeckeGal.liftAb r hrc).ker : Set (Gab D.host.E D.nd.Om)) :=
      isClosed_singleton.preimage (GlobalTheory.HeckeGal.continuous_liftAb r hrc)
    have hle : (art.comp (Neutral.B1.localIdele D.host.E v)).range ≤ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (art (Neutral.B1.localIdele D.host.E v x))
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, GlobalTheory.HeckeGal.liftAb_toAb, ← h _ τ hτ.symm]
      exact hψ.atl v hv x
    have hm : GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ ∈ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      refine Subgroup.topologicalClosure_minimal _ hle hcl ?_
      rw [ha.dec v A hA]
      exact ⟨σ, hσ, rfl⟩
    rwa [MonoidHom.mem_ker, GlobalTheory.HeckeGal.liftAb_toAb] at hm
end GlobalTheory.GalTwist
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisRep_of_twist_of_prime : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  first | exact @_root_.GlobalTheory.GalTwist.galoisRep_of_twist_properties_alt | exact _root_.GlobalTheory.GalTwist.galoisRep_of_twist_properties_alt | (intros; apply _root_.GlobalTheory.GalTwist.galoisRep_of_twist_properties_alt <;> assumption)
end
end
