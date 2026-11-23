import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralSelfDualEqAdelicFourier
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecompositionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord

section Coords

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def tupCrd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n × Fin M × Fin d → R) where
  toFun X p := (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm_apply_apply (X a i)
  right_inv Y := by
    funext p
    obtain ⟨a, i, k⟩ := p
    exact congrFun ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).apply_symm_apply fun k => Y (a, i, k)) k
  map_add' X Y := by
    funext p
    simp
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2.2).comp ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).continuous.comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.continuous.comp
      (continuous_pi fun k => continuous_apply (a, i, k))

theorem tupCrd_apply (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E)
    (p : Fin n × Fin M × Fin d) :
    tupCrd R b n M X p = (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2 := rfl

end Coords

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem tupCrd_projInf {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    tupCrd (Ainf F) b n M (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projInf X) = fun p => (tupCrd (AF F) b n M X p).1 := by
  funext p
  rw [tupCrd_apply, tupCrd_apply]
  exact repr_map (fstA F) b (X p.1 p.2.1) p.2.2

theorem tupCrd_projFin {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    tupCrd (Af F) b n M (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projFin X) = fun p => (tupCrd (AF F) b n M X p).2 := by
  funext p
  rw [tupCrd_apply, tupCrd_apply]
  exact repr_map (sndA F) b (X p.1 p.2.1) p.2.2

def splitHomeo (F : Type) [Field F] [NumberField F] (ι : Type) :
    (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun y := (fun i => (y i).1, fun i => (y i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv y := rfl
  right_inv p := rfl
  continuous_toFun :=
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun :=
    continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)

end Split

theorem map_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasis F E
  obtain ⟨tA, -, sA, -, -, -, -, hBA, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  obtain ⟨tI, -, sI, -, -, -, -, hBI, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  obtain ⟨tF, -, sF, -, -, -, -, hBF, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI := hBA n M
  haveI := hBI n M
  haveI := hBF n M
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ι := Fin n × Fin M × Fin (Module.finrank F E)
  let e := tupCrd (AF F) b n M
  let eI := tupCrd (Ainf F) b n M
  let eF := tupCrd (Af F) b n M
  let eA : (Fin n → Fin M → AF F ⊗[F] E) ≃+ (ι → AF F) := e
  have hm : (dx.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map dx eA e.continuous e.symm.continuous
  let m₁ : Measure (ι → Ainf F) := Measure.addHaar
  let m₂ : Measure (ι → Af F) := Measure.addHaar
  haveI : m₁.IsAddHaarMeasure := by dsimp only [m₁]; infer_instance
  haveI : m₂.IsAddHaarMeasure := by dsimp only [m₂]; infer_instance
  haveI : SFinite m₁ := by dsimp only [m₁]; infer_instance
  haveI : SFinite m₂ := by dsimp only [m₂]; infer_instance
  obtain ⟨c, -, hcT, hc⟩ := GlobalTheory.T.adele_haar_product_decomposition F ι (dx.map e) m₁ m₂ hm inferInstance inferInstance
  let S := splitHomeo F ι
  let H : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ
      (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) :=
    e.toHomeomorph.trans (S.trans (eI.symm.toHomeomorph.prodCongr eF.symm.toHomeomorph))
  have hH : (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) = H := by
    funext X
    refine Prod.ext ?_ ?_
    · show _ = eI.symm (fun i => (e X i).1)
      rw [show (fun i => (e X i).1) = eI (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projInf X) from (tupCrd_projInf b X).symm]
      exact (eI.symm_apply_apply _).symm
    · show _ = eF.symm (fun i => (e X i).2)
      rw [show (fun i => (e X i).2) = eF (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projFin X) from (tupCrd_projFin b X).symm]
      exact (eF.symm_apply_apply _).symm
  have hc' : (dx.map e).map S = c • m₁.prod m₂ := hc
  have he : Measurable e := e.continuous.measurable
  have hPI : Measurable eI.symm := eI.symm.continuous.measurable
  have hPF : Measurable eF.symm := eF.symm.continuous.measurable
  refine ⟨m₁.map eI.symm, m₂.map eF.symm, c, ?_, ?_, inferInstance, inferInstance, hcT, ?_, ?_⟩
  · let eIA : (ι → Ainf F) ≃+ (Fin n → Fin M → Ainf F ⊗[F] E) := eI.symm
    exact AddEquiv.isAddHaarMeasure_map m₁ eIA eI.symm.continuous eI.continuous
  · let eFA : (ι → Af F) ≃+ (Fin n → Fin M → Af F ⊗[F] E) := eF.symm
    exact AddEquiv.isAddHaarMeasure_map m₂ eFA eF.symm.continuous eF.continuous
  · rw [hH]
    exact H.measurableEmbedding
  · rw [hH, Measure.map_prod_map m₁ m₂ hPI hPF, ← Measure.map_smul, ← hc',
      Measure.map_map (hPI.prodMap hPF) S.continuous.measurable,
      Measure.map_map ((hPI.prodMap hPF).comp S.continuous.measurable) he]
    rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup
