import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DiagScale

section Gen

theorem pi_map_scale_family {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : ι → X → X) (hf : ∀ i, Measurable (f i)) (c : ι → ℝ≥0) (h : ∀ i, μ.map (f i) = c i • μ) :
    (Measure.pi fun _ : ι => μ).map (fun x i => f i (x i)) =
      (∏ i, c i) • Measure.pi fun _ : ι => μ := by
  haveI : ∀ i, SigmaFinite (μ.map (f i)) := fun i => by rw [h i]; infer_instance
  rw [Measure.pi_map_pi (f := f) (fun i => (hf i).aemeasurable)]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem map_mul_scale {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (lam : Measure A) (u v : A) (c c' : ℝ≥0)
    (hu : lam.map (fun y => u * y) = c • lam) (hv : lam.map (fun y => v * y) = c' • lam) :
    lam.map (fun y => u * v * y) = (c * c') • lam := by
  have hm : ∀ x : A, Measurable (fun y : A => x * y) :=
    fun x => (continuous_const.mul continuous_id).measurable
  have e : (fun y => u * v * y) = (fun y => u * y) ∘ (fun y => v * y) := by
    funext y
    simp [mul_assoc]
  rw [e, ← Measure.map_map (hm u) (hm v), hv, Measure.map_smul, hu, smul_smul, mul_comm]

def mulU (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace A] [BorelSpace A] (u : Aˣ) : A ≃ᵐ A :=
  { toEquiv := Units.mulLeft u
    measurable_toFun := (continuous_const.mul continuous_id).measurable
    measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem prod_pairs {n : ℕ} (c : Fin n → ℝ≥0) :
    (∏ i, c i * c i) * ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      ∏ a, c a ^ (2 * n) := by
  classical
  set g : Fin n × Fin n → ℝ≥0 := fun x => c x.1 * c x.2 with hg
  have h1 : ∏ x : Fin n × Fin n, g x = (∏ a, c a) ^ (2 * n) := by
    rw [Fintype.prod_prod_type]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow]
    ring
  have hU : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p :=
    Finset.prod_subtype _ (by simp) _
  have hL : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x =
      ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x :=
    Finset.prod_equiv (Equiv.prodComm _ _) (by simp) (by simp [hg, mul_comm])
  have hD : ∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x =
      ∏ i, c i * c i := by
    symm
    refine Finset.prod_nbij' (fun i => (i, i)) Prod.fst (by simp) (by simp) (by simp) ?_ (by simp [hg])
    rintro ⟨a, b⟩ h
    simpa using (Finset.mem_filter.1 h).2
  have hS : ∏ x : Fin n × Fin n, g x =
      (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2), g x) *
      ((∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.1 = x.2), g x) *
       (∏ x ∈ Finset.univ.filter (fun x : Fin n × Fin n => x.2 < x.1), g x)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : Fin n × Fin n => x.1 < x.2) g]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter (fun x : Fin n × Fin n => ¬ x.1 < x.2)) (fun x => x.1 = x.2) g,
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by simp [h], h⟩
    · refine Finset.prod_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
      constructor
      · intro h
        exact lt_of_le_of_ne (not_lt.1 h.1) (fun e => h.2 e.symm)
      · intro h
        exact ⟨not_lt.2 h.le, h.ne'⟩
  have hP : ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2 =
      (∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p) ^ 2 := by
    rw [Finset.prod_pow]
  have hT : ∏ a, c a ^ (2 * n) = (∏ a, c a) ^ (2 * n) := Finset.prod_pow _ _ _
  rw [hT, ← h1, hS, hL, hD, hU, hP]
  ring

end Gen

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem coordHerm_map_diag (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) [lam.IsAddHaarMeasure] {n : ℕ}
    (u : Fin n → Rˣ) (c : Fin n → ℝ≥0) (h : ∀ a, lam.map (fun y => (u a : R) * y) = c a • lam)
    (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j *
        algebraMap R (R ⊗[F] E) (u j)) :
    (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map τ =
      (∏ a, c a ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hσ
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  obtain ⟨hK, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R 2 b lam ‹_›
  haveI := hK
  haveI := hH n
  have hhom := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6
  let φ := GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n
  let Q : Measure ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    Measure.pi fun _ => GlobalTheory.CompanionTheory.SW.coordK R b lam
  let P := (Measure.pi fun _ : Fin n => lam).prod Q
  have hν : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = Measure.comap φ P := rfl
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n = 0 := by
      rw [hν, Measure.comap, dif_neg hc]
    have := isOpen_univ.measure_pos (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n) Set.univ_nonempty
    simp [h0] at this
  let D1 : (Fin n → R) ≃ᵐ (Fin n → R) :=
    MeasurableEquiv.piCongrRight fun i => mulU R (u i * u i)
  let D2 : ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) ≃ᵐ
      ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    MeasurableEquiv.piCongrRight fun p =>
      mulU (R ⊗[F] E) (Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom (u p.1.1 * u p.1.2))
  have hsc : ∀ a a', lam.map (fun y => ((u a * u a' : Rˣ) : R) * y) = (c a * c a') • lam := by
    intro a a'
    rw [Units.val_mul]
    exact map_mul_scale lam _ _ _ _ (h a) (h a')
  have m1 : (Measure.pi fun _ : Fin n => lam).map D1 =
      (∏ i, c i * c i) • Measure.pi fun _ : Fin n => lam :=
    pi_map_scale_family lam (fun i y => ((u i * u i : Rˣ) : R) * y)
      (fun i => (continuous_const.mul continuous_id).measurable) _ (fun i => hsc i i)
  have m2 : Q.map D2 = (∏ p : {p : Fin n × Fin n // p.1 < p.2}, (c p.1.1 * c p.1.2) ^ 2) • Q :=
    pi_map_scale_family (GlobalTheory.CompanionTheory.SW.coordK R b lam)
      (fun (p : {p : Fin n × Fin n // p.1 < p.2}) y => algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) * y)
      (fun p => (continuous_const.mul continuous_id).measurable) _
      (fun p => GlobalTheory.CompanionTheory.SW.Dil.coordK_map_unit R σ hσ b lam _ _ (hsc p.1.1 p.1.2))
  have hD : P.map (D1.prodCongr D2) = (∏ a, c a ^ (2 * n)) • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin n => lam) Q D1.measurable D2.measurable
    rw [m1, m2, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, prod_pairs] at e
    exact e.symm
  rw [hν]
  refine GlobalTheory.CompanionTheory.SW.Dil.map_comap_scale φ P τ hτm (D1.prodCongr D2) _ hhom.surjective hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) =
      ((u i * u i : Rˣ) : R) * (algebraMap F R (1 / 2) *
        Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    have e : algebraMap R (R ⊗[F] E) (u i) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i *
        algebraMap R (R ⊗[F] E) (u i) =
        ((u i * u i : Rˣ) : R) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i := by
      rw [Algebra.smul_def, Units.val_mul, map_mul]
      ring
    rw [hτ, e, map_smul, smul_eq_mul]
    ring
  · funext p
    change (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2 =
      algebraMap R (R ⊗[F] E) ((u p.1.1 * u p.1.2 : Rˣ) : R) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2
    rw [hτ, Units.val_mul, map_mul]
    ring

end H

theorem coordHerm_map_diag_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam e he t ht τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_diag (Ainf F) σ hσ b lam (fun a => (ht a).unit)
    (fun a => (∏ w, ‖e (t a) w‖₊)⁻¹)
    (fun a => GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)) τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DiagScale
