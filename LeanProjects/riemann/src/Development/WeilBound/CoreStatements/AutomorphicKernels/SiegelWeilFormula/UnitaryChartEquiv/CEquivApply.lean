import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLatticeTheta

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KTunit

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp

local instance (priority := high) measTup {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _

local instance borelTup {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def cmap (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) (X : Mx F E d.m d.n) : κ → AF F := fun k => d.crd X (τ k)

def cinv (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) (c : κ → AF F) : Mx F E d.m d.n := d.cmb fun k => c (τ.symm k)

theorem cinv_cmap (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) (X : Mx F E d.m d.n) : cinv d τ (cmap d τ X) = X := by
  have : (fun k => cmap d τ X (τ.symm k)) = d.crd X := funext fun k => by simp [cmap]
  rw [cinv, this, cmb_crd]

theorem cmap_cinv (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) (c : κ → AF F) : cmap d τ (cinv d τ c) = c := by
  funext k
  simp [cmap, cinv, crd_cmb]

theorem cmap_add (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) (X Y : Mx F E d.m d.n) :
    cmap d τ (X + Y) = cmap d τ X + cmap d τ Y := by
  funext k
  simp [cmap, SD.crd, map_add]

theorem cont_cmap (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) : Continuous (cmap d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  refine continuous_pi fun k => ?_
  exact (continuous_apply (τ k).2.2).comp (hr.continuous.comp (continuous_id.matrix_elem (τ k).1 (τ k).2.1))

theorem cont_cinv (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) : Continuous (cinv d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  set h := hr.homeomorph with hh
  have e : ∀ c i j, cinv d τ c i j = h.symm (fun l => c (τ.symm (i, j, l))) := fun c i j => by
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    funext l
    exact congrFun (crd_cmb d (fun k => c (τ.symm k))) (i, j, l)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [e]
  exact h.symm.continuous.comp (continuous_pi fun l => continuous_apply _)

def cEquiv (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) : Mx F E d.m d.n ≃ₜ+ (κ → AF F) where
  toFun := cmap d τ
  invFun := cinv d τ
  left_inv := cinv_cmap d τ
  right_inv := cmap_cinv d τ
  map_add' := cmap_add d τ
  continuous_toFun := cont_cmap d τ
  continuous_invFun := cont_cinv d τ

theorem cEquiv_apply (d : SD σ) {κ : Type} (τ : κ ≃ Ix d) (X : Mx F E d.m d.n) : cEquiv d τ X = cmap d τ X := rfl

theorem map_haar (d : SD σ) {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (ν : Measure (Mx F E d.m d.n))
    (hν : ν.IsAddHaarMeasure) :
    (ν.map (cmap d τ)).IsAddHaarMeasure ∧
      ∀ f : (κ → AF F) → ℂ, ∫ X, f (cmap d τ X) ∂ν = ∫ y, f y ∂(ν.map (cmap d τ)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have P := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)
  haveI : IsTopologicalRing (AE F E) := P.1
  haveI : BorelSpace (Mx F E d.m d.n) := P.2.2.2.2.2.2.2.1 d.m d.n
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstance
  refine ⟨?_, fun f => ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map ν (cEquiv d τ)
  · have h := integral_map_equiv (μ := ν) (cEquiv d τ).toHomeomorph.toMeasurableEquiv f
    exact h.symm

end PositivityTheory.SiegelWeilFormula.KTunit

end
