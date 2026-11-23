import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeightStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquivStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HermSd

theorem sum_square {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a +
      ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
  have h1 : ∀ g : Fin n × Fin n → M, ∑ p : {p : Fin n × Fin n // p.1 < p.2}, g p.1 =
      ∑ x : Fin n × Fin n, if x.1 < x.2 then g x else 0 := by
    intro g
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) g).symm
  have h2 : ∑ p : {p : Fin n × Fin n // p.1 < p.2}, f p.1.2 p.1.1 =
      ∑ x : Fin n × Fin n, if x.2 < x.1 then f x.1 x.2 else 0 := by
    rw [h1 (fun x => f x.2 x.1), ← Equiv.sum_comp (Equiv.prodComm (Fin n) (Fin n))]
    rfl
  have h3 : ∑ a, f a a = ∑ x : Fin n × Fin n, if x.1 = x.2 then f x.1 x.2 else 0 := by
    rw [Fintype.sum_prod_type]
    simp
  rw [Finset.sum_add_distrib, h1 (fun x => f x.1 x.2), h2, h3, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases lt_trichotomy x.1 x.2 with h | h | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp [h]
  · simp [h, h.ne', not_lt_of_gt h]

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have : r ⊗ₜ[F] x = r • ((1 : R) ⊗ₜ[F] x) := by simp [TensorProduct.smul_tmul']
  rw [this, map_smul, smul_eq_mul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

theorem trace_sigma {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (x : E) :
    Algebra.trace F E (σ x) = Algebra.trace F E x :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hinv) (AlgHom.ext hinv)) x

theorem trace_sigR [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] {σ : E →ₐ[F] E}
    (hinv : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ y) = Algebra.trace R (R ⊗[F] E) y := by
  induction y with
  | zero => simp
  | tmul r e => rw [HaarCoord.sigR_tmul, trace_tmul, trace_tmul, trace_sigma hinv]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

def gramB (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) : Matrix (Fin d) (Fin d) F :=
  fun k l => Algebra.trace F E (b k * σ (b l))

theorem gramB_isSymm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ}
    (b : Module.Basis (Fin d) F E) : (gramB σ b).IsSymm := by
  ext k l
  simp only [Matrix.transpose_apply, gramB]
  rw [← trace_sigma hinv, map_mul, hinv, mul_comm]

theorem gramB_det [FiniteDimensional F E] [Algebra.IsSeparable F E] {σ : E →ₐ[F] E}
    (hinv : ∀ x, σ (σ x) = x) {d : ℕ}
    (b : Module.Basis (Fin d) F E) : (gramB σ b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  set w : E := ∑ l, v l • b l with hw
  have hz : ∀ x : E, Algebra.trace F E (x * σ w) = 0 := by
    intro x
    have hk : ∀ k, Algebra.trace F E (b k * σ w) = 0 := by
      intro k
      have := congrFun hv0 k
      simp only [Matrix.mulVec, dotProduct, gramB, Pi.zero_apply] at this
      rw [hw, map_sum, Finset.mul_sum, map_sum, ← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
    have hx := b.sum_repr x
    rw [← hx, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, map_smul, hk, smul_zero]
  have hs : σ w = 0 := (traceForm_nondegenerate F E).2 _ fun x => by
    simpa [Algebra.traceForm_apply] using hz x
  have hw0 : w = 0 := by rw [← hinv w, hs, map_zero]
  funext l
  have := b.linearIndependent
  exact (Fintype.linearIndependent_iff.mp this) v hw0 l

end Alg

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev Idx (n d : ℕ) : Type := Fin n ⊕ ({p : Fin n × Fin n // p.1 < p.2} × Fin d)

def formB (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    Matrix (Idx n d) (Idx n d) F :=
  Matrix.fromBlocks 1 0 0 ((1 : Matrix {p : Fin n × Fin n // p.1 < p.2} _ F) ⊗ₖ gramB σ b)

theorem formB_isSymm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (n : ℕ) : (formB σ b n).IsSymm := by
  refine Matrix.IsSymm.fromBlocks Matrix.isSymm_one (by simp) ?_
  ext ⟨p, k⟩ ⟨q, l⟩
  have := congrFun (congrFun (gramB_isSymm hinv b) k) l
  simp only [Matrix.transpose_apply] at this
  simp only [Matrix.transpose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, this, eq_comm]

theorem formB_det [FiniteDimensional F E] [Algebra.IsSeparable F E] {σ : E →ₐ[F] E}
    (hinv : ∀ x, σ (σ x) = x) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (n : ℕ) : (formB σ b n).det ≠ 0 := by
  unfold formB
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_kronecker, Matrix.det_one,
    one_pow, one_mul]
  exact pow_ne_zero _ (gramB_det hinv b)

variable (R : Type) [CommRing R] [Algebra F R]

theorem formB_mulVec_inl (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (y : Idx n d → R) (i : Fin n) :
    (((formB σ b n).map (algebraMap F R)) *ᵥ y) (Sum.inl i) = y (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, formB, Fintype.sum_sum_type, Matrix.one_apply]

theorem formB_mulVec_inr (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (y : Idx n d → R) (p : {p : Fin n × Fin n // p.1 < p.2}) (k : Fin d) :
    (((formB σ b n).map (algebraMap F R)) *ᵥ y) (Sum.inr (p, k)) =
      ∑ l, algebraMap F R (gramB σ b k l) * y (Sum.inr (p, l)) := by
  simp only [Matrix.mulVec, dotProduct, formB, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Matrix.map_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    map_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [Ne.symm hq]
  · simp

variable [TopologicalSpace R]

def toVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) : Idx n d → R :=
  Sum.elim x.1 fun q => (Algebra.TensorProduct.basis R b).repr (x.2 q.1) q.2

def hermVec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) :
    Idx n d → R :=
  toVec R b n (HaarCoord.hermCoord R σ n S)

omit [TopologicalSpace R] in
theorem off_diag [FiniteDimensional F E] [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (x y : R ⊗[F] E) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (x * sigR R σ y + sigR R σ x * y) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k *
        ∑ l, algebraMap F R (gramB σ b k l) * (Algebra.TensorProduct.basis R b).repr y l := by
  set C := Algebra.TensorProduct.basis R b with hC
  have h1 : sigR R σ x * y = sigR R σ (x * sigR R σ y) := by
    rw [map_mul, HaarCoord.sigR_sigR R hinv]
  rw [h1, map_add, trace_sigR R hinv, HaarCoord.half_add_self (F := F) R]
  have hx : x = ∑ k, C.repr x k • ((1 : R) ⊗ₜ[F] b k) := by
    conv_lhs => rw [← C.sum_repr x]
    simp [hC, Algebra.TensorProduct.basis_apply]
  have hy : sigR R σ y = ∑ l, C.repr y l • ((1 : R) ⊗ₜ[F] σ (b l)) := by
    conv_lhs => rw [← C.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hC, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      HaarCoord.sigR_tmul]
  rw [hy]
  conv_lhs => rw [hx]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul, Finset.mul_sum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_smul_comm, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul, one_mul,
    smul_eq_mul, mul_comm]
  rfl

theorem pair_eq [FiniteDimensional F E] [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n) :
    pairHerm R σ n S T = hermVec R σ b n S ⬝ᵥ
      (((formB σ b n).map (algebraMap F R)) *ᵥ hermVec R σ b n T) := by
  have hS : ∀ a c, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a =
      sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c) := fun a c => (S.2 c a).symm
  have hT : ∀ a c, (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a =
      sigR R σ ((T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c) := fun a c => (T.2 c a).symm
  unfold pairHerm
  rw [sum_square, map_add, mul_add, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, formB_mulVec_inl,
    formB_mulVec_inr]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    obtain ⟨r, hr⟩ := HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ _ (S.2 a a)
    obtain ⟨s, hs⟩ := HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ _ (T.2 a a)
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inl]
    rw [hr, hs, Algebra.TensorProduct.tmul_mul_tmul, one_mul, HaarCoord.half_trace_tmul R h2,
      HaarCoord.half_trace_tmul R h2, HaarCoord.half_trace_tmul R h2]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [hT p.1.1 p.1.2, hS p.1.1 p.1.2, off_diag R hinv b]
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inr]

end Form

section Meas

theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A)
    [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h : (Measure.pi fun _ : ι × κ => μ) =
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map (MeasurableEquiv.curry ι κ A).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ A).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

theorem mp_comap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (h : X ≃ᵐ Y) (ρ : Measure Y) :
    MeasurePreserving h (Measure.comap h ρ) ρ :=
  ⟨h.measurable, by rw [h.measurableEmbedding.map_comap, h.surjective.range_eq, Measure.restrict_univ]⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ)
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]

include hcm in
theorem toVec_isHomeomorph {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    IsHomeomorph (toVec R b n) := by
  obtain ⟨-, -, -, -, -, -, t7, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  let cK : R ⊗[F] E ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  let A2 : ({p : Fin n × Fin n // p.1 < p.2} → Fin d → R) ≃ₜ
      ({p : Fin n × Fin n // p.1 < p.2} × Fin d → R) :=
    { (Equiv.curry {p : Fin n × Fin n // p.1 < p.2} (Fin d) R).symm with
      continuous_toFun := continuous_pi fun q => (continuous_apply q.2).comp (continuous_apply q.1)
      continuous_invFun := continuous_pi fun p => continuous_pi fun k => continuous_apply (p, k) }
  let A := ((Homeomorph.refl (Fin n → R)).prodCongr (Homeomorph.piCongrRight fun _ => cK)).trans
    (((Homeomorph.refl (Fin n → R)).prodCongr A2).trans
      (Homeomorph.sumArrowHomeomorphProdArrow).symm)
  have : toVec R b n = A := by
    funext x i
    cases i with
    | inl i => rfl
    | inr q => rfl
  rw [this]
  exact A.isHomeomorph

variable [MeasurableSpace R] [BorelSpace R]

include hcm in
theorem mp_toVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (lam : Measure R)
    [lam.IsAddHaarMeasure] :
    MeasurePreserving (toVec R b n)
      ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam))
      (Measure.pi fun _ : Idx n d => lam) := by
  obtain ⟨t1, t2, t3, t4, -, -, t7, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  let cK : R ⊗[F] E ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  have hH := (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam inferInstance).1
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  have hcK : MeasurePreserving cK (coordK R b lam) (Measure.pi fun _ => lam) :=
    mp_comap cK.toMeasurableEquiv _
  have mp1 := (MeasurePreserving.id (Measure.pi fun _ : Fin n => lam)).prod
    (measurePreserving_pi (fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)
      (fun _ => Measure.pi fun _ => lam) fun _ => hcK)
  have mp2 := (MeasurePreserving.id (Measure.pi fun _ : Fin n => lam)).prod
    (curry_mp {p : Fin n × Fin n // p.1 < p.2} (Fin d) R lam).symm
  have mp3 := (measurePreserving_sumPiEquivProdPi (fun _ : Idx n d => lam)).symm
  have h := mp3.comp (mp2.comp mp1)
  convert h using 1
  funext x i
  cases i with
  | inl i => rfl
  | inr q => rfl

include hcm in
theorem mp_hermVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (lam : Measure R)
    [lam.IsAddHaarMeasure] :
    MeasurePreserving (hermVec R σ b n) (coordHerm R σ b lam n)
      (Measure.pi fun _ : Idx n d => lam) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  let hc := (HaarCoord.hermCoord_isHomeomorph R hinv hcm.2.2.1 hδ hσδ n t5 t6).homeomorph _
  have := (mp_toVec hcm R b n lam).comp (mp_comap hc.toMeasurableEquiv
    ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)))
  exact this

theorem hermVec_add {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n) :
    hermVec R σ b n (S + T) = hermVec R σ b n S + hermVec R σ b n T := by
  funext i
  cases i with
  | inl i => simp [hermVec, toVec, HaarCoord.hermCoord_add]
  | inr q => simp [hermVec, toVec, HaarCoord.hermCoord_add]

include hcm in
theorem hermVec_isHomeomorph {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    IsHomeomorph (hermVec R σ b n) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  have h1 := HaarCoord.hermCoord_isHomeomorph R hinv hcm.2.2.1 hδ hσδ n t5 t6
  have h2 := toVec_isHomeomorph hcm R b n
  exact ((h1.homeomorph _).trans (h2.homeomorph _)).isHomeomorph

include hcm in

theorem sd_core {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (lam : Measure R)
    [lam.IsAddHaarMeasure] (ψR : R → ℂ) (c : ℝ≥0)
    (h : ∀ μ : Measure (Idx n d → R),
      SelfDual μ (fun x y => ψR (x ⬝ᵥ ((formB σ b n).map (algebraMap F R) *ᵥ y))) ↔
        μ = c • Measure.pi fun _ => lam)
    (ν : Measure (HermR R σ n)) :
    SdHerm F E σ R ψR n ν ↔ ν = c • coordHerm R σ b lam n := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; omega)
  let hh := (hermVec_isHomeomorph hcm R b n).homeomorph _
  let e : HermR R σ n ≃ₜ+ (Idx n d → R) :=
    { AddEquiv.mk' hh.toEquiv (hermVec_add R b n) with
      continuous_toFun := hh.continuous
      continuous_invFun := hh.symm.continuous }
  have hT := GlobalTheory.T.selfdual_measure_transport_equiv (HermR R σ n) (Idx n d → R) e ν
    (fun x y => ψR (x ⬝ᵥ ((formB σ b n).map (algebraMap F R) *ᵥ y)))
  have hp : (fun S T : HermR R σ n => ψR (pairHerm R σ n S T)) =
      fun S T => ψR (e S ⬝ᵥ ((formB σ b n).map (algebraMap F R) *ᵥ e T)) := by
    funext S T
    rw [pair_eq R hinv hcm.2.2.1 hδ hσδ b n S T]
    rfl
  have hmp := mp_hermVec hcm R b n lam
  unfold SdHerm
  rw [hp, hT, h, ← hmp.map_eq]
  have hinj := hh.toMeasurableEquiv.map_measurableEquiv_injective
  have hsm : c • Measure.map (hermVec R σ b n) (coordHerm R σ b lam n) =
      Measure.map hh.toMeasurableEquiv (c • coordHerm R σ b lam n) := by
    rw [Measure.map_smul]
    rfl
  rw [hsm]
  exact hinj.eq_iff

end Meas

end GlobalTheory.CompanionTheory.SW.HermSd

namespace GlobalTheory.CompanionTheory.SW

theorem sdHerm_eq_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) n ν ↔ ν = cinf • coordHerm (Ainf F) σ b laminf n) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) n ν ↔ ν = c v • coordHerm (Fv F v) σ b (lam v) n) := by
  intro F E _ _ _ _ _ σ hcm d b laminf lam hinf hv ψ hψ n
  obtain ⟨hinv, -⟩ := HaarCoord.conj_facts hcm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; omega)
  obtain ⟨cinf, c, hu, h1, h2⟩ := GlobalTheory.T.exists_unipotentInvariant_compactlySupported_weight F hcm.1 laminf lam hinf hv ψ hψ
    (HermSd.Idx n d) (HermSd.formB σ b n) (HermSd.formB_isSymm hinv b n)
    (HermSd.formB_det hinv b n)
  refine ⟨cinf, c, hu, ?_, fun v => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI := hinf.1
    exact HermSd.sd_core hcm (Ainf F) b n laminf (psiInf F ψ) cinf h1
  · obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hv v).1
    exact HermSd.sd_core hcm (Fv F v) b n (lam v) (psiV F ψ v) (c v) (h2 v)

end GlobalTheory.CompanionTheory.SW
