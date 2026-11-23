import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.RpSmulLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnitaryChartEquiv.CEquivApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CovolUnique
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasTop
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.TW.Twp

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ratM_iff (d : SD σ) (X : Mx F E d.m d.n) :
    X ∈ d.ratM ↔ d.crd X ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F (Ix d) := by
  let c : Mx F E d.m d.n →+ (Ix d → AF F) :=
    { toFun := d.crd, map_zero' := by funext k; simp [SD.crd], map_add' := crd_add d }
  constructor
  · intro hX
    have hle : d.ratM ≤ (GroundTheory.Automorphic.FourierWhittaker.vecLattice F (Ix d)).comap c := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨M, rfl⟩
      refine ⟨fun k => d.bs.repr (M k.1 k.2.1) k.2.2, ?_⟩
      funext k
      exact (crd_incM d M k).symm
    exact hle hX
  · rintro ⟨ξ, hξ⟩
    let M : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => ∑ k, ξ (i, j, k) • d.bs k
    have e1 : d.crd (incM F M) = d.crd X := by
      funext k
      rw [crd_incM d _ k]
      have h2 := congrFun hξ k
      simp only [AddMonoidHom.compLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h2
      rw [← h2]
      show _ = algebraMap F (AF F) (ξ k)
      congr 1
      exact congrFun (d.bs.repr_sum_self fun k' => ξ (k.1, k.2.1, k')) k.2.2
    have e2 : incM F M = X := by
      rw [← cmb_crd d (incM F _), e1, cmb_crd]
    rw [← e2]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩

attribute [-instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.measAF in

theorem integral_cov_gen {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] {mG : MeasurableSpace G} [hBor : BorelSpace G] {ι : Type} [Fintype ι] (Γ : AddSubgroup G) [Countable Γ]
    (e : G ≃ₜ+ (ι → AdeleRing (𝓞 F) F)) (he : ∀ x, x ∈ Γ ↔ e x ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F ι)
    (ν : Measure G) [hνH : ν.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (h1 : ν 𝓕 = 1) (h : G → ℂ) :
    ∫ Z, h Z ∂ν = ∫ c, h (e.symm c) ∂(GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := ι)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  let m : (ι → AdeleRing (𝓞 F) F) ≃ᵐ G := e.symm.toHomeomorph.toMeasurableEquiv
  let μ₀ : Measure G := (GroundTheory.Automorphic.FourierWhittaker.vecMeasure F ι).map m
  have hμ₀ : μ₀.IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map (GroundTheory.Automorphic.FourierWhittaker.vecMeasure F ι) e.symm
  have hD : IsAddFundamentalDomain Γ (e ⁻¹' GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι) μ₀ := by
    refine IsAddFundamentalDomain.mk'
      ((GroundTheory.Automorphic.FourierWhittaker.measurableSet_vecDomain).preimage e.continuous.measurable).nullMeasurableSet
      fun x => ?_
    obtain ⟨g', hg', hu⟩ := GroundTheory.Automorphic.FourierWhittaker.existsUnique_vadd_mem_vecDomain (e x)
    have hg : e.symm (g' : ι → AdeleRing (𝓞 F) F) ∈ Γ := by
      rw [he, e.apply_symm_apply]
      exact g'.2
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · show e.symm (g' : ι → AdeleRing (𝓞 F) F) + x ∈ e ⁻¹' GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι
      rw [Set.mem_preimage, map_add, e.apply_symm_apply]
      exact hg'
    · rintro ⟨y, hy⟩ hyx
      have hy' : e y ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F ι := (he y).1 hy
      have hyx' : e y + e x ∈ GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι := by
        rw [← map_add]
        exact hyx
      have := hu ⟨e y, hy'⟩ hyx'
      apply Subtype.ext
      show y = e.symm (g' : ι → AdeleRing (𝓞 F) F)
      rw [← this]
      exact (e.symm_apply_apply y).symm
  have hD1 : μ₀ (e ⁻¹' GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι) = 1 := by
    show (Measure.map m _) _ = 1
    rw [MeasurableEquiv.map_apply]
    have : m ⁻¹' (e ⁻¹' GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι) =
        GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι := by
      ext c
      show e (e.symm c) ∈ GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι ↔ c ∈ GroundTheory.Automorphic.FourierWhittaker.vecDomain F ι
      rw [e.apply_symm_apply]
    rw [this]
    exact GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain
  have hνμ : ν = μ₀ := KWhit.MeasG.covol_unique (μ := μ₀) (μ' := ν) Γ hD h𝓕 hD1 h1
  rw [hνμ]
  show ∫ Z, h Z ∂(Measure.map m _) = _
  rw [integral_map_equiv]
  rfl

theorem integral_cov (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (h : Mx F E d.m d.n → ℂ) :
    ∫ Z, h Z ∂ν = ∫ c, h (d.cmb c) ∂(GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := Ix d)) := by
  obtain ⟨hT, hLC, hSC, hB, hC⟩ := KWhit.meas_mx_top' d
  haveI := hT; haveI := hLC; haveI := hSC; haveI := hB; haveI := hC
  obtain ⟨hH, 𝓕, h𝓕, h1⟩ := hν
  haveI := hH
  exact integral_cov_gen (hBor := hB) (hνH := hH) d.ratM (KTunit.cEquiv d (Equiv.refl (Ix d))) (fun X => ratM_iff d X) ν 𝓕 h𝓕 h1 h

end PositivityTheory.SiegelWeilFormula.TW.Twp

end
