import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie

theorem charOf_psiAt_chrEq : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  intro D a i κ ι χ r b ha hr hg f hf ch Q
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r with hψdef
  have hker : ψ.ker = r.ker := by
    cases b
    · ext σ
      simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
    · simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hop : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := hker ▸ hr
  have hfi : ψ.ker.FiniteIndex := by
    let H : OpenNormalSubgroup (G D.host.E D.nd.Om) := { toSubgroup := ψ.ker, isOpen' := hop, isNormal' := inferInstance }
    exact inferInstanceAs (OpenNormalSubgroup.toFiniteIndexNormalSubgroup H).toSubgroup.FiniteIndex
  have hn : ψ.ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]
    exact ψ.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  have key : ∀ (x : (AE D)ˣ) (σ : G D.host.E D.nd.Om), a.sym x = toAb D.host.E D.nd.Om σ →
      ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := by
    intro x σ hx
    rw [charOf_eq a f hop hx hn (hpow σ)]
    have hint : IsIntegral ℤ ((ψ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
        rw [← Units.val_pow_eq_pow_val, hpow σ, Units.val_one]
        exact isIntegral_one)
    rw [hf _ hint]
    have h1 := hg.2.2 (Units.map a.κ.toMonoidHom x) σ hx
    simp [GlobalTheory.GalChar.inQ, GlobalTheory.GalChar.toQ, GlobalTheory.HeckeGal.infPow, GlobalTheory.HeckeGal.lPow, GlobalTheory.HeckeGal.locPow] at h1
    rw [h1]
    simp

  have hsymc : Continuous a.sym :=
    ha.artin.quot.continuous.comp (Continuous.units_map _ ha.cont)
  have hdesc : IsOpen (((descend ψ : Gab D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ).ker : Set (Gab D.host.E D.nd.Om))) := by
    have hpre : (toAb D.host.E D.nd.Om) ⁻¹' ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) = (ψ.ker : Set _) := by
      ext σ
      simp [descend_toAb hop]
    have hs : Function.Surjective (toAb D.host.E D.nd.Om) := QuotientGroup.mk'_surjective _
    rw [← Set.image_preimage_eq ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) hs, hpre]
    exact QuotientGroup.isOpenMap_coe _ hop
  have hpullo : IsOpen (((a.pull ψ).ker : Set (AE D)ˣ)) := by
    have : ((a.pull ψ).ker : Set (AE D)ˣ) = a.sym ⁻¹' ((descend ψ).ker : Set _) := by
      ext x
      simp [Recip.pull]
    rw [this]
    exact hdesc.preimage hsymc
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_of_continuousAt_one (charOf a f ψ) ?_
    refine ContinuousAt.congr (continuousAt_const (y := (1 : Circle))) (Filter.eventuallyEq_of_mem (hpullo.mem_nhds (map_one _)) fun x hx => ?_)
    change (1 : Circle) = charOf a f ψ x
    rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, (a.pull ψ).mem_ker.1 hx, map_one, map_one]
  · have hs : a.sym (Units.map (incA D).toMonoidHom k) = 1 := by
      change a.art (Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k)) = 1
      rw [← MonoidHom.mem_ker, ha.artin.ker]
      apply Subgroup.le_topologicalClosure
      apply Subgroup.mem_sup_left
      exact ⟨k, Units.ext (ha.rat k).symm⟩
    change unitPart (Units.map f.toMonoidHom (descend ψ (a.sym (Units.map (incA D).toMonoidHom k)))) = 1
    rw [hs, map_one, map_one, map_one]
  · obtain ⟨σ, hσ⟩ := a.exists_sym x
    have hy : Units.map a.κ.toMonoidHom x =
        Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) :=
      Units.ext ((congrArg a.κ hx).trans (ha.loc P e he k))
    change ((charOf a f ψ x : Circle) : ℂ) = _
    rw [key x σ hσ, hy]
    rfl
end GlobalTheory.SeriesTie

end
