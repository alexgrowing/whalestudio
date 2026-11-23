import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem measurable_fin_cons {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    {f : Ω → A} {g : Ω → Fin n → A} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => (Fin.cons (f p) (g p) : Fin (n + 1) → A) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa using measurable_pi_iff.1 hg j

theorem measurable_scl {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {N m : ℕ} :
    Measurable fun p : K × (Fin m → Fin N → K) => scl p.1 p.2 := by
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (measurable_pi_iff.1 (measurable_pi_iff.1 (measurable_snd (α := K) (β := Fin m → Fin N → K)) a) i).mul measurable_fst

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem corner_half_trace_gram_cons (σ : E →ₐ[F] E) {N n : ℕ} (J₂ : Matrix (Fin N) (Fin N) E)
    (y : Fin 1 → Fin N → R ⊗[F] E) (Z : Fin n → Fin N → R ⊗[F] E) :
    s0 R (gramR R σ J₂ (Fin.cons (y 0) Z : Fin (n + 1) → Fin N → R ⊗[F] E)) =
      s0 R (gramR R σ J₂ y) := by
  simp [s0, gramR]

theorem isUnit_tmul_one {x : R} (hx : IsUnit x) : IsUnit (x ⊗ₜ[F] (1 : E)) := by
  simpa using hx.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)

theorem tmul_one_eq_smul (x : R) : x ⊗ₜ[F] (1 : E) = x • (1 : R ⊗[F] E) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem continuous_tmul_one [TopologicalSpace R] :
    Continuous fun x : R => x ⊗ₜ[F] (1 : E) := by
  haveI : ContinuousSMul R (R ⊗[F] E) := ModuleTopology.continuousSMul R (R ⊗[F] E)
  have h : Continuous fun x : R => x • (1 : R ⊗[F] E) := by fun_prop
  simpa only [tmul_one_eq_smul] using h

end

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}

include R in
theorem measurable_inv_a (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    Measurable fun x : R => ((((a x)⁻¹ : Rˣ) : R)) := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := D.hR
  classical
  have h1 : ContinuousOn (fun x : R => ((((a x)⁻¹ : Rˣ) : R))) B₀ :=
    Units.continuous_val.comp_continuousOn (continuous_inv.comp_continuousOn D.hac)
  have h2 : ContinuousOn (fun _ : R => (1 : R)) B₀ᶜ := continuousOn_const
  have h3 := h1.measurable_piecewise h2 D.hB₀.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ B₀
  · simp [hx]
  · simp [hx, D.hoff x hx]

theorem measurable_sTil (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    Measurable (sTil σ J t s a) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, hsigc, htrc, -, hbw, -, hgramc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hq : Continuous fun y : Fin 1 → Fin (M + 1) → R ⊗[F] E =>
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) := by
    unfold s0
    exact continuous_const.mul (htrc.comp ((hgramc 1 (M + 1) _).matrix_elem 0 0))
  have hw : Measurable fun y : Fin 1 → Fin (M + 1) → R ⊗[F] E =>
      (((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) :=
    (continuous_tmul_one R (F := F) (E := E)).measurable.comp ((measurable_inv_a D).comp hq.measurable)
  exact D.hs.comp (measurable_scl.comp (hw.prodMk measurable_id))

theorem measurable_chi (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (chi σ J t s a b lam φ) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨h1, h2, h3, h4, h5, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  have hact' := (hact n).1.measurable
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := by unfold coordW; infer_instance
  have hG : Measurable fun q : ((Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E)) ×
      (Fin n → Fin M → R ⊗[F] E) =>
      φ (Fin.cons (q.1.1 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a q.1.1)
        (fun j => Fin.cons (q.1.2 j) (q.2 j)))) := by
    refine hφ.comp (measurable_fin_cons ?_ ?_)
    · exact measurable_pi_iff.1 (measurable_fst.comp measurable_fst) 0
    · refine hact'.comp (((measurable_sTil D).comp (measurable_fst.comp measurable_fst)).prodMk ?_)
      refine measurable_pi_iff.2 fun j => measurable_fin_cons ?_ ?_
      · exact measurable_pi_iff.1 (measurable_snd.comp measurable_fst) j
      · exact measurable_pi_iff.1 measurable_snd j
  exact (hG.lintegral_prod_right' (ν := coordW R b lam n M)).lintegral_prod_right'
    (ν := Measure.pi fun _ : Fin n => coordK R b lam)

theorem chi_eq_zero (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀) :
    chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) y = 0 := by
  unfold chi
  have hz : ∀ Z : Fin n → Fin (M + 1) → R ⊗[F] E,
      (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ (Fin.cons (y 0) Z) = 0 := by
    intro Z
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨S, hS, hSe⟩
    apply hy
    rw [← corner_half_trace_gram_cons R σ _ y Z, ← hSe]
    exact hS.1
  simp [hz]

theorem isUnit_gram (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∈ B₀) :
    IsUnit (gramR R σ (blockOne (algebraMap F E t) J) y).det := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g, -, hg⟩ := hg (M + 1) _ hJ'
  obtain ⟨-, hh, -⟩ := hermScal_main F E σ D.hCM R d b
  have hS := hh (g y)
  rw [← hg y] at hS
  have hx : IsUnit (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)) := by
    rw [D.hsq _ hy]
    exact ((Units.isUnit _).pow 2).mul ((IsUnit.mk0 t D.ht).map (algebraMap F R))
  have h00 : gramR R σ (blockOne (algebraMap F E t) J) y 0 0 =
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ⊗ₜ[F] (1 : E) := by
    have := congrArg (fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) hS
    simp only [← hg y] at this
    simpa [hermScal, s0] using this.symm
  rw [Matrix.det_fin_one, h00]
  exact isUnit_tmul_one R hx

end Main

theorem first_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht

  have hUm : MeasurableSet (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) := by
    obtain ⟨-, -, -, hbor, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
    obtain ⟨g, hgc, hg⟩ := hg (M + 1) _ hJ'
    have hBo := (GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2.2.2.2
    have : (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) = g ⁻¹' Bset R σ t a B₀ := by
      ext v
      constructor
      · rintro ⟨S, hS, hSe⟩
        have : S = g v := Subtype.ext (hSe.trans (hg v))
        simpa [this] using hS
      · intro hv
        exact ⟨g v, hv, (hg v).symm⟩
    rw [this]
    exact (hBo.preimage hgc).measurableSet
  have hφ' := hφ.indicator hUm
  have hchi := measurable_chi D hφ'

  obtain ⟨-, -, -, hbor1, hg1⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g₁, hg₁c, hg₁⟩ := hg1 (M + 1) _ hJ'
  obtain ⟨hUo, -, -, -, -, hae⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  have hU₁ : MeasurableSet {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
      IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} := by
    have : {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} = g₁ ⁻¹' Unt σ R 1 := by
      ext X
      simp [Unt, hg₁ X]
    rw [this]
    exact (hUo.preimage hg₁c).measurableSet
  obtain ⟨hh, hh2, hh3⟩ := hermScal_main F E σ D.hCM R d b
  have hemb : MeasurableEmbedding (hermScal R σ) := (hh.homeomorph _).measurableEmbedding
  have hs0 : ∀ x : R, s0 R ((hermScal R σ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = x :=
    fun x => hh.injective (hh2 (hermScal R σ x))
  set χ := chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) with hχ
  have hzero : ∀ y, s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀ → χ y = 0 :=
    fun y hy => chi_eq_zero D φ hy

  have e1 : ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hUm]
    exact GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section F E σ D.hCM M _ hJ' R D.hR d b lam D.hlam n (sTil σ J t s a) (measurable_sTil D) _ hφ'
  have e2 : ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) =
      ∫⁻ y in {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hU₁]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}
    · exact (Set.indicator_of_mem hy χ).symm
    · rw [Set.indicator_of_notMem hy, hzero y fun h => hy (isUnit_gram D h)]
  have e3 := D.hm₁.2.1 χ hchi
  rw [← hh3 lam D.hlam, hemb.lintegral_map] at e3
  have e4 : ∫⁻ x, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam = ∫⁻ x in B₀, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam := by
    rw [← lintegral_indicator D.hB₀.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B₀
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hae (hermScal R σ x)] with y hy
      refine hzero y ?_
      rw [hy, hs0]
      exact hx
  rw [e1, e2, e3, e4]
  refine setLIntegral_congr_fun D.hB₀.measurableSet fun x hx => ?_
  have hm : m₁ (hermScal R σ x) =
      κ₁ (a x) • (m₁ (hermScal R σ (algebraMap F R t))).map (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) := by
    have := D.hscale (a x)
    rwa [← D.hsq x hx] at this
  have hsm : Measurable (scl (N := M + 1) (n := 1) (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) :=
    measurable_scl.comp (measurable_const.prodMk measurable_id)
  simp only [hm]
  rw [lintegral_smul_measure, lintegral_map hchi hsm]
  rfl

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
