import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

variable {V P : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace P] [LocallyCompactSpace P]

def addEquivOf (T Ti : V → V) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) : V ≃+ V where
  toFun := T
  invFun := Ti
  left_inv := hl
  right_inv := hr
  map_add' := hadd

theorem map_eq_smul (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : V → V) (hT : Continuous T)
    (hTi : Continuous Ti) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) :
    ∃ c : ℝ≥0, μ.map T = c • μ := by
  haveI : (μ.map T).IsAddHaarMeasure :=
    (addEquivOf T Ti hadd hl hr).isAddHaarMeasure_map μ hT hTi
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem exists_continuous_scale (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : P → V → V)
    (hT : Continuous (Function.uncurry T)) (hTi : Continuous (Function.uncurry Ti))
    (hadd : ∀ p x y, T p (x + y) = T p x + T p y)
    (hl : ∀ p x, Ti p (T p x) = x) (hr : ∀ p x, T p (Ti p x) = x) :
    ∃ A : P → ℝ≥0, Continuous A ∧ ∀ p, μ.map (T p) = A p • μ := by
  have hTp : ∀ p, Continuous (T p) := fun p => hT.comp (Continuous.prodMk_right p)
  have hTip : ∀ p, Continuous (Ti p) := fun p => hTi.comp (Continuous.prodMk_right p)
  choose A hform using fun p =>
    map_eq_smul μ (T p) (Ti p) (hTp p) (hTip p) (hadd p) (hl p) (hr p)
  refine ⟨A, ?_, hform⟩
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (X := V)
    (s := {0}) (t := ∅) isCompact_singleton isClosed_empty (by simp)
  have hf0 : (0 : V → ℝ) ≤ f := fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂μ := by
    refine f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 (x := 0) ?_
    rw [hf1 (Set.mem_singleton 0)]; exact one_ne_zero
  have hval : ∀ p, (A p : ℝ) = (∫ x, f (T p x) ∂μ) / ∫ x, f x ∂μ := by
    intro p
    have h1 : ∫ x, f x ∂(μ.map (T p)) = ∫ x, f (T p x) ∂μ :=
      integral_map (hTp p).aemeasurable f.continuous.aestronglyMeasurable
    have h2 : ∫ x, f x ∂(μ.map (T p)) = (A p : ℝ) * ∫ x, f x ∂μ := by
      conv_lhs => rw [hform p]
      rw [integral_smul_nnreal_measure]
      simp [NNReal.smul_def]
    rw [eq_div_iff hpos.ne', ← h2, h1]
  refine continuous_induced_rng.2 ?_
  have hI : Continuous fun p => ∫ x, f (T p x) ∂μ := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds p₀
    have hk : IsCompact (Function.uncurry Ti '' (C ×ˢ tsupport f)) :=
      (hCc.prod hfc).image hTi
    have hcont : ContinuousOn (fun p x => f (T p x)).uncurry (C ×ˢ Set.univ) :=
      (f.continuous.comp hT).continuousOn
    refine (continuousOn_integral_of_compact_support hk hcont ?_).continuousAt hCn
    intro p x hp hx
    by_contra hne
    exact hx ⟨(p, T p x), ⟨hp, subset_tsupport _ hne⟩, hl p x⟩
  exact (hI.div_const _).congr fun p => (hval p).symm

end GlobalTheory.CompanionTheory.SW.HaarScale

namespace GlobalTheory.CompanionTheory.SW.HaarScale

section Mat

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

theorem continuous_inv_unitMat (hu : IsOpenEmbedding (Units.val : Kˣ → K)) :
    Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => (g.1)⁻¹ := by
  have hdet : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.1.det :=
    Continuous.matrix_det continuous_subtype_val
  have hunit : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.2.unit :=
    hu.isEmbedding.continuous_iff.2 (by simpa [Function.comp_def] using hdet)
  have hinv : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} =>
      ((g.2.unit⁻¹ : Kˣ) : K) := Units.continuous_val.comp hunit.inv
  have hadj : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.1.adjugate :=
    Continuous.matrix_adjugate continuous_subtype_val
  refine (hinv.smul hadj).congr fun g => ?_
  have hr : Ring.inverse g.1.det = ((g.2.unit⁻¹ : Kˣ) : K) := by
    have h := Ring.inverse_unit g.2.unit
    rwa [IsUnit.unit_spec] at h
  rw [Matrix.inv_def, hr]
  rfl

theorem locallyCompact_unitMat [LocallyCompactSpace K] (hu : IsOpenEmbedding (Units.val : Kˣ → K)) :
    LocallyCompactSpace {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → K))
  have hset : {g : Matrix (Fin n) (Fin n) K | IsUnit g.det} =
      (fun g : Matrix (Fin n) (Fin n) K => g.det) ⁻¹' Set.range (Units.val : Kˣ → K) := by
    ext g; simp [IsUnit]
  have hopen : IsOpen {g : Matrix (Fin n) (Fin n) K | IsUnit g.det} := by
    rw [hset]
    exact hu.isOpen_range.preimage (Continuous.matrix_det continuous_id)
  exact hopen.isOpenEmbedding_subtypeVal.locallyCompactSpace

theorem continuousOn_extend (A : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} → ℝ≥0)
    (hA : Continuous A) [∀ g : Matrix (Fin n) (Fin n) K, Decidable (IsUnit g.det)] :
    ContinuousOn (fun g : Matrix (Fin n) (Fin n) K => if h : IsUnit g.det then A ⟨g, h⟩ else 0)
      {g | IsUnit g.det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine hA.congr fun g => ?_
  simp [Set.restrict, g.2]

end Mat

section Tup

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) h = rmul R X (g * h) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

theorem rmul_add {M n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (X + Y) g = rmul R X g + rmul R Y g := by
  funext a i
  simp [rmul, add_mul, Finset.sum_add_distrib]

end Tup

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def conjT (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ

theorem conjT_mul (σ : E →ₐ[F] E) {n : ℕ} (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (g * h) = conjT R σ h * conjT R σ g := by
  simp only [conjT, Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_one (σ : E →ₐ[F] E) {n : ℕ} :
    conjT R σ (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [conjT]
  · simp [conjT, Matrix.one_apply, h, Ne.symm h]

theorem mem_hermR_iff (σ : E →ₐ[F] E) {n : ℕ} (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    S ∈ HermR R σ n ↔ conjT R σ S = S := by
  constructor
  · intro h; ext a b; exact h a b
  · intro h a b
    exact congrFun (congrFun h a) b

theorem conjT_conjT {σ : E →ₐ[F] E} (hs : ∀ x, σ (σ x) = x) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : conjT R σ (conjT R σ g) = g := by
  ext a b
  simp [conjT, GlobalTheory.CompanionTheory.SW.HermTop.sigR_sigR R hs]

theorem conj_mem {σ : E →ₐ[F] E} (hs : ∀ x, σ (σ x) = x) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) :
    conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n := by
  rw [mem_hermR_iff, conjT_mul, conjT_mul, conjT_conjT R hs, (mem_hermR_iff R σ _).1 S.2, Matrix.mul_assoc]

end Herm

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_scale_tuples (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n M : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    ∃ A : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn A {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → μ.map (fun X => rmul R X g) = A g • μ := by
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hu : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := locallyCompact_unitMat (n := n) hu
  have hcont : ∀ {Q : Type} [TopologicalSpace Q] (G : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E)),
      Continuous G → Continuous (Function.uncurry fun (q : Q) (X : Fin n → Fin M → R ⊗[F] E) => rmul R X (G q)) := by
    intro Q _ G hG
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [Function.uncurry_def, rmul]
    refine continuous_finset_sum _ fun c _ => ?_
    have h1 : Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => p.2 c i :=
      (continuous_apply_apply c i).comp continuous_snd
    have h2 : Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => G p.1 c a :=
      (hG.comp continuous_fst).matrix_elem c a
    exact h1.mul h2
  obtain ⟨A, hA, hform⟩ := exists_continuous_scale μ
    (P := {g : Matrix (Fin n) (Fin n) (R ⊗[F] E) // IsUnit g.det})
    (fun g X => rmul R X g.1) (fun g X => rmul R X (g.1)⁻¹)
    (hcont _ continuous_subtype_val) (hcont _ (continuous_inv_unitMat hu))
    (fun g X Y => rmul_add R X Y g.1)
    (fun g X => by rw [rmul_rmul, Matrix.mul_nonsing_inv _ g.2, rmul_one])
    (fun g X => by rw [rmul_rmul, Matrix.nonsing_inv_mul _ g.2, rmul_one])
  refine ⟨_, continuousOn_extend A hA, fun g hg => ?_⟩
  simpa [hg] using hform ⟨g, hg⟩

theorem exists_scale_herm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n : ℕ)
    (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure) :
    ∃ B : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn B {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n,
        (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
          conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g) → ν.map τ = B g • ν := by
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hu : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI := locallyCompact_unitMat (n := n) hu
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  have hcont : ∀ {Q : Type} [TopologicalSpace Q] (G : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E)),
      Continuous G → Continuous (Function.uncurry fun (q : Q) (S : HermR R σ n) =>
        (⟨conjT R σ (G q) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * G q, conj_mem R hs _ S⟩ : HermR R σ n)) := by
    intro Q _ G hG
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => conjT R σ (G p.1) :=
      ((hG.comp continuous_fst).matrix_map hsig).matrix_transpose
    have h2 : Continuous fun p : Q × HermR R σ n => (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val.comp continuous_snd
    exact (h1.matrix_mul h2).matrix_mul (hG.comp continuous_fst)
  have hinvl : ∀ g h : Matrix (Fin n) (Fin n) (R ⊗[F] E), g * h = 1 → ∀ S : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      conjT R σ h * (conjT R σ g * S * g) * h = S := by
    intro g h hgh S
    have h1 : conjT R σ h * conjT R σ g = 1 := by rw [← conjT_mul, hgh, conjT_one]
    calc conjT R σ h * (conjT R σ g * S * g) * h
        = (conjT R σ h * conjT R σ g) * S * (g * h) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [h1, hgh, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨B, hB, hform⟩ := exists_continuous_scale ν
    (P := {g : Matrix (Fin n) (Fin n) (R ⊗[F] E) // IsUnit g.det})
    (fun g S => ⟨conjT R σ g.1 * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g.1, conj_mem R hs _ S⟩)
    (fun g S => ⟨conjT R σ (g.1)⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g.1)⁻¹, conj_mem R hs _ S⟩)
    (hcont _ continuous_subtype_val) (hcont _ (continuous_inv_unitMat hu))
    (fun g S T => Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul]))
    (fun g S => Subtype.ext (hinvl _ _ (Matrix.mul_nonsing_inv _ g.2) _))
    (fun g S => Subtype.ext (hinvl _ _ (Matrix.nonsing_inv_mul _ g.2) _))
  refine ⟨_, continuousOn_extend B hB, fun g hg τ hτ => ?_⟩
  have hτ' : τ = fun S => ⟨conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g, conj_mem R hs _ S⟩ :=
    funext fun S => Subtype.ext (hτ S)
  rw [hτ']
  simpa [hg] using hform ⟨g, hg⟩

end Main

end GlobalTheory.CompanionTheory.SW.HaarScale
