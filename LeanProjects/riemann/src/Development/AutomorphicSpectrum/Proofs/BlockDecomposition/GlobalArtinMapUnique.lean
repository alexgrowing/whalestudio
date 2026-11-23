import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.ArtinMapUniq

open PositivityTheory.FamInh

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_ideal_ramificationIdx (L : Type) [Field L] [NumberField L] [Algebra E L] :
    ∃ 𝔡 : Ideal (𝓞 E), 𝔡 ≠ ⊥ ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 L)),
      ¬ v.asIdeal ∣ 𝔡 → w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  refine ⟨(differentIdeal (𝓞 E) (𝓞 L)).under (𝓞 E), ?_, fun v w hv hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 E) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

theorem res_unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (v : HeightOneSpectrum (𝓞 E)) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) (w : HeightOneSpectrum (𝓞 L)) (hw : IsPlaceOver A w)
    [w.asIdeal.LiesOver v.asIdeal] (hr : w.asIdeal.ramificationIdx (𝓞 E) = 1)
    {x : (v.adicCompletion E)ˣ} (hx : IsUnifAt v x) :
    res L (art (localIdele E v x)) = res L (art' (localIdele E v x)) := by
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨σ', hσ', e'⟩ := (ha'.frob v A hA _).mp ⟨x, hx, rfl⟩
  have h := (res_isArithFrobAt hw hσ).mul_inv_mem_inertia (res_isArithFrobAt hw hσ')
  rw [(inertia_eq_bot_iff v w).2 hr, Subgroup.mem_bot, mul_inv_eq_one] at h
  rw [← e, ← e', map_inv, map_inv, map_inv, map_inv, res_toAb, res_toAb, h]

theorem res_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (x : Ideles E) : res L (art x) = res L (art' x) := by
  have := isAlgClosure_top L
  letI : CommGroup (L ≃ₐ[E] L) :=
    { (inferInstance : Group (L ≃ₐ[E] L)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := L ≃ₐ[E] L)).comm a b }
  have : T2Space (L ≃ₐ[E] L) := krullTopology_t2
  have : IsTopologicalGroup (L ≃ₐ[E] L) := inferInstance
  let f : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art
  let f' : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art'
  have hf : Continuous f := (continuous_res L).comp ha.quot.continuous
  have hf' : Continuous f' := (continuous_res L).comp ha'.quot.continuous
  have hk : ∀ b : Ideles E →* Gab E Ω, IsGlobalArtin b → ∀ k, b (diagUnits E k) = 1 := fun b hb k => by
    have hk : diagUnits E k ∈ b.ker := by
      rw [hb.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact MonoidHom.mem_ker.mp hk
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_ramificationIdx (E := E) L
  have hψ := GlobalTheory.FrobDense.eq_one_of_away (f * f'⁻¹) (hf.mul hf'.inv) (fun k => by
      simp [f, f', hk _ ha k, hk _ ha' k]) (Ideal.finite_factors (I := 𝔡) h𝔡).toFinset fun v hv => by
    refine GlobalTheory.FrobDense.eq_one_of_unif ((f * f'⁻¹).comp (localIdele E v)) fun y hy => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
    have hv' : ¬ v.asIdeal ∣ 𝔡 := by simpa using hv
    have e := res_unif_eq ha ha' L v hA w hw (hun v w hv' hwv) hy
    simp [f, f', e]
  have := DFunLike.congr_fun hψ x
  simpa [f, f', mul_inv_eq_one] using this

theorem eq_inv_arithmetic_artin_map : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  intro E Ω _ _ _ _ _ art ha
  ext x
  have h : art x * ((art0 E Ω)⁻¹ x)⁻¹ ∈ (⊥ : Subgroup (Gab E Ω)) :=
    mem_of_forall_res (H := ⊥) isClosed_singleton fun L _ _ _ => by
      rw [map_mul, map_inv, res_eq ha isGlobalArtin_inv L x, mul_inv_cancel]
  rwa [Subgroup.mem_bot, mul_inv_eq_one] at h

end GlobalTheory.CompanionTheory.ArtinMapUniq
