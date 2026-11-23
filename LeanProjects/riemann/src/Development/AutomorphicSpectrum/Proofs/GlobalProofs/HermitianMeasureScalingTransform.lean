import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

section U
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPiU (ι : Type) (u : Rˣ) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := Units.mulLeft u
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem mulPiU_apply (ι : Type) (u : Rˣ) (x : ι → R) (i : ι) :
    mulPiU R ι u x i = (u : R) * x i := rfl

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι u) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => (u : R) * y) (continuous_const.mul continuous_id).measurable c h

theorem coordK_map_unit (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (GlobalTheory.CompanionTheory.SW.coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) (u : R) * y) =
      (c ^ d) • GlobalTheory.CompanionTheory.SW.coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPiU (ι := Fin d) R lam u c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPiU R (Fin d) u) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPiU_apply, ← Algebra.smul_def, map_smul]
    rfl

end U

theorem coordW_map_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  intro F E _ _ _ _ _ σ hσ M d b lam hlam t ht c h
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  obtain ⟨u, rfl⟩ := ht
  set f : Ainf F ⊗[F] E → Ainf F ⊗[F] E := fun y => algebraMap (Ainf F) (Ainf F ⊗[F] E) (u : Ainf F) * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map_unit (Ainf F) σ hσ b lam u c h
  have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one, ← pow_mul] at hk2
  exact hk2

end GlobalTheory.CompanionTheory.SW.Dil
