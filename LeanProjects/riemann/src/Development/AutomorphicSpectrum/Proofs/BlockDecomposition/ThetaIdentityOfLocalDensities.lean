import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgBase.Theta

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem aniso_one {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J) (x : Fin 1 → E) (h : hE σ J x x = 0) : x = 0 := by
  have hd : J 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hJ.2
  simp only [hE, hform, Finset.univ_unique, Finset.sum_singleton] at h
  have h0 : x 0 = 0 := by
    rcases mul_eq_zero.1 h with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · simpa using h2
      · exact absurd h2 hd
    · exact h1
  funext i
  rw [Subsingleton.elim i 0]
  exact h0

theorem exists_len (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    {X : Fin 1 → Fin 1 → E} (hX : X ≠ 0) : ∃ β : F, β ≠ 0 ∧ X ∈ sph σ J β := by
  have hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b := fun a b => by
    rw [Subsingleton.elim a b]
    exact GlobalTheory.CompanionTheory.RgMass.hE_self_fixed hcm hJ _
  obtain ⟨β, e, h, -⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm _ hT
  refine ⟨β, h ?_, e⟩
  rw [Matrix.det_unique]
  intro h0
  exact hX (funext fun a => by rw [Subsingleton.elim a default]; exact aniso_one hJ _ h0)

theorem sph_unique {J : Matrix (Fin 1) (Fin 1) E} {X : Fin 1 → Fin 1 → E} {β β' : F} (h : X ∈ sph σ J β)
    (h' : X ∈ sph σ J β') : β = β' := by
  have e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β' := h.symm.trans h'
  exact (algebraMap F E).injective (congrFun (congrFun e 0) 0)

theorem ne_zero_of_mem_sph {J : Matrix (Fin 1) (Fin 1) E} {X : Fin 1 → Fin 1 → E} {β : F} (hβ : β ≠ 0)
    (h : X ∈ sph σ J β) : X ≠ 0 := by
  rintro rfl
  refine hβ (sph_unique h ?_)
  funext a c
  simp [gramE, hE, hform]

def sphEquiv (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J) :
    (Σ β : {β : F // β ≠ 0}, sph σ J β.1) ≃ {X : Fin 1 → Fin 1 → E | X ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1, ne_zero_of_mem_sph p.1.2 p.2.2⟩) (by
    constructor
    · rintro ⟨β, X⟩ ⟨β', X'⟩ h
      have hX : X.1 = X'.1 := congrArg Subtype.val h
      have hb : β = β' := Subtype.ext (sph_unique X.2 (hX ▸ X'.2))
      subst hb
      obtain rfl : X = X' := Subtype.ext hX
      rfl
    · rintro ⟨X, hX⟩
      obtain ⟨β, h0, hβ⟩ := exists_len hcm hJ hX
      exact ⟨⟨⟨β, h0⟩, ⟨X, hβ⟩⟩, rfl⟩)

theorem thetaMeas_ne (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) :
    thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 1 → E | X ≠ 0} =
      Measure.sum fun β : {β : F // β ≠ 0} => thetaMeas σ J μ 𝓕 (sph σ J β.1) := by
  ext s hs
  simp only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
  congr 1
  rw [← (sphEquiv hcm hJ).tsum_eq, ENNReal.tsum_sigma']
  rfl

end Alg

section Maps

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_sigR {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R'] (g : R →ₐ[F] R') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (sigR R σ y) =
      sigR R' σ (Algebra.TensorProduct.map g (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR]
  | add a b ha hb => simp only [map_add, ha, hb]

def pI : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

def pV (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E)

theorem projInf_apply {n M : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) :
    projInf X a i = pI (X a i) := rfl

theorem projV_projFin_apply (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) :
    projV v (projFin X) a i = pV v (X a i) := by
  simp only [projV, projFin, pV]
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  simp

end Maps

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

theorem repr_one_tmul (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] e) k = algebraMap F R (b.repr e k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ev_int (c : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := (algebraMap F (Af F) c).2

def GoodV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F

theorem eventually_goodV (b : Module.Basis (Fin d) F E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, GoodV b v := by
  simp only [GoodV, eventually_all]
  exact fun k l m => ev_int _

def IntE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F

theorem IntE.mul {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} (hv : GoodV b v) {y z : Fv F v ⊗[F] E}
    (hy : IntE b v y) (hz : IntE b v z) : IntE b v (y * z) := by
  intro m
  set c := Algebra.TensorProduct.basis (Fv F v) b with hc
  have e : y * z = ∑ k, ∑ l, (c.repr y k * c.repr z l) • ((1 : Fv F v) ⊗ₜ[F] (b k * b l)) := by
    conv_lhs => rw [← c.sum_repr y, ← c.sum_repr z]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hc, Algebra.TensorProduct.basis_apply, smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [e]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hy k) (hz l)) ?_
  rw [hc, repr_one_tmul]
  exact hv k l m

theorem mem_latV_iff {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E} :
    Y ∈ latV b v ↔ ∀ a i, IntE b v (Y a i) := Iff.rfl

theorem eventually_int (hcm : IsCMExt F E σ) (b : Module.Basis (Fin d) F E) (x : AF F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntE b v (pV v x) := by
  have h := (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1).2.2.2.2.2.1 (projFin fun _ _ => x)
  refine h.mono fun v hv => ?_
  have := hv 0 0
  intro k
  have h2 := this k
  rwa [projV_projFin_apply] at h2

end Lat

section Local

variable {F : Type} [Field F] [NumberField F]

theorem idele_val (a : (AF F)ˣ) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v ((a : AF F).2 v) = 1 := by
  have h1 := (a : AF F).2.2
  have h2 := ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  filter_upwards [h1, h2] with v e1 e2
  have e1' : Valued.v ((a : AF F).2 v) ≤ 1 := e1
  have e2' : Valued.v (((a⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ 1 := e2
  have e3 : (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    have := congrArg (fun z : AF F => z.2 v) (Units.mul_inv a)
    exact this
  have e4 := congrArg Valued.v e3
  rw [map_mul, map_one] at e4
  refine le_antisymm e1' ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := e4.symm
    _ ≤ Valued.v ((a : AF F).2 v) * 1 := mul_le_mul_right e2' _
    _ = _ := mul_one _

theorem rv_unit (v : HeightOneSpectrum (𝓞 F)) (e : ℝ) {s : Fv F v} (hs : Valued.v s = 1) : rv v e s = 1 := by
  have h0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  unfold rv
  rw [tsum_eq_single 0]
  · simp [h0, hs]
  · intro i hi
    rw [if_neg]
    rintro ⟨-, h⟩
    rw [hs] at h
    have h3 : (1 : WithZero (Multiplicative ℤ)) = ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := rfl
    rw [h3, WithZero.coe_le_coe, Multiplicative.ofAdd_le] at h
    omega

end Local

theorem tprod_split {ι : Type} (S : Finset ι) (f : ι → ℝ) (hf : (Function.mulSupport f).Finite) :
    ∏' v, f v = (∏ v ∈ S, f v) * ∏ᶠ v : {v // v ∉ S}, f v.1 := by
  rw [tprod_eq_finprod hf, finprod_subtype_eq_finprod_cond, ← finprod_mem_univ f,
    ← finprod_mem_mul_diff' (Set.subset_univ (S : Set ι)) (by simpa using hf), finprod_mem_coe_finset]
  congr 1
  refine finprod_congr fun v => ?_
  simp [Set.mem_diff]

theorem ne_zero_of_finprod {ι : Type} (f : ι → ℝ) (hf : (Function.mulSupport f).Finite) (h : ∏ᶠ v, f v ≠ 0) (i : ι) :
    f i ≠ 0 := by
  intro h0
  refine h ?_
  rw [finprod_eq_prod f hf]
  refine Finset.prod_eq_zero (i := i) ?_ h0
  simp [h0]

section Fibre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Matrix (Fin 1) (Fin 1) E}

theorem isUnit_hermScal (R : Type) [CommRing R] [Algebra F R] {s : R} (hs : IsUnit s) :
    IsUnit ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det := by
  rw [Matrix.det_unique]
  exact hs.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E)

theorem exists_of_fib_ne {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {μ : Measure (Fin 1 → Fin 1 → R ⊗[F] E)} {ν : Measure (HermR R σ 1)}
    {m : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)} (h : IsGramFib R σ J 1 μ ν m) (s : HermR R σ 1)
    {U : Set (Fin 1 → Fin 1 → R ⊗[F] E)} (hU : m s U ≠ 0) :
    ∃ X ∈ U, gramR R σ J X = (s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := by
  by_contra hc
  push_neg at hc
  refine hU (measure_mono_null (fun X hX => ?_) (h.1 s))
  intro h2
  exact hc X hX h2.1

theorem meas_mul (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hR : IsLocR R) (y : R ⊗[F] E) :
    Measurable (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) (a : Fin 1) (i : Fin 1) => y * X a i) := by
  obtain ⟨_, _, _, _, -⟩ := hR
  obtain ⟨_, -, -, -, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB 1 1
  refine Continuous.measurable ?_
  exact continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))

theorem map_scal (hS : Scal) (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    {μ : Measure (Fin 1 → Fin 1 → R ⊗[F] E)} {ν : Measure (HermR R σ 1)}
    {m : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)} (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hfib : IsGramFib R σ J 1 μ ν m) (x : (R ⊗[F] E)ˣ) {n s : R} (hn : n ⊗ₜ[F] (1 : E) = sigR R σ x * x) (hs : IsUnit s)
    {B : Set (Fin 1 → Fin 1 → R ⊗[F] E)} (hB : MeasurableSet B) :
    m (hermScal R σ s) ((fun X a i => (x : R ⊗[F] E) * X a i) ⁻¹' B) = m (hermScal R σ (n * s)) B := by
  rw [← hS F E σ hcm J hJ R hR μ ν m hμ hν hfib x n s hn hs, Measure.map_apply (meas_mul hcm R hR _) hB]

def xI (x : (AF F ⊗[F] E)ˣ) : (Ainf F ⊗[F] E)ˣ := Units.map (pI : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E).toMonoidHom x

def xV (v : HeightOneSpectrum (𝓞 F)) (x : (AF F ⊗[F] E)ˣ) : (Fv F v ⊗[F] E)ˣ :=
  Units.map (pV v : AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E).toMonoidHom x

theorem isNm_inf {x : (AF F ⊗[F] E)ˣ} {n : (AF F)ˣ} (h : IsNm σ x n) :
    (n : AF F).1 ⊗ₜ[F] (1 : E) = sigR (Ainf F) σ (xI x) * xI x := by
  have h1 := congrArg (pI (F := F) (E := E)) h
  rw [map_mul] at h1
  have h2 : pI (sigR (AF F) σ (x : AF F ⊗[F] E)) = sigR (Ainf F) σ (pI (x : AF F ⊗[F] E)) := map_sigR (fstA F) _
  rw [h2] at h1
  exact h1

theorem isNm_v (v : HeightOneSpectrum (𝓞 F)) {x : (AF F ⊗[F] E)ˣ} {n : (AF F)ˣ} (h : IsNm σ x n) :
    (n : AF F).2 v ⊗ₜ[F] (1 : E) = sigR (Fv F v) σ (xV v x) * xV v x := by
  have h1 := congrArg (pV (F := F) (E := E) v) h
  rw [map_mul] at h1
  have h2 : pV v (sigR (AF F) σ (x : AF F ⊗[F] E)) = sigR (Fv F v) σ (pV v (x : AF F ⊗[F] E)) :=
    map_sigR ((evalV F v).comp (sndA F)) _
  rw [h2] at h1
  exact h1

theorem projInf_mul (x : (AF F ⊗[F] E)ˣ) (X : Fin 1 → Fin 1 → AF F ⊗[F] E) :
    projInf (fun a i => (x : AF F ⊗[F] E) * X a i) = fun a i => (xI x : Ainf F ⊗[F] E) * projInf X a i := by
  funext a i
  simp only [projInf_apply, map_mul]
  rfl

theorem projV_mul (v : HeightOneSpectrum (𝓞 F)) (x : (AF F ⊗[F] E)ˣ) (X : Fin 1 → Fin 1 → AF F ⊗[F] E) :
    projV v (projFin (fun a i => (x : AF F ⊗[F] E) * X a i)) =
      fun a i => (xV v x : Fv F v ⊗[F] E) * projV v (projFin X) a i := by
  funext a i
  simp only [projV_projFin_apply, map_mul]
  rfl

variable {d : ℕ} {b : Module.Basis (Fin d) F E}

theorem inf_factor (hS : Scal) (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) {li : Measure (Ainf F)} (hli : IsStdInf li)
    {mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E)}
    (hmi : IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 1) (coordHerm (Ainf F) σ b li 1) mi)
    {φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ} (hc : Continuous φ) (hcs : HasCompactSupport φ) (h0 : ∀ X, 0 ≤ φ X)
    (hsu : tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det}) {x : (AF F ⊗[F] E)ˣ} {n : (AF F)ˣ} (hxn : IsNm σ x n)
    {s : Ainf F} (hs : IsUnit s) :
    ∫⁻ Y, ENNReal.ofReal (φ (fun a i => (xI x : Ainf F ⊗[F] E) * Y a i)) ∂(mi (hermScal (Ainf F) σ s)) =
      ENNReal.ofReal (Gi mi φ ((n : AF F).1 * s)) := by
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have hR := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have hR' := hR
  obtain ⟨_, _, _, _, -⟩ := hR'
  obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) d b li hli.1
  obtain ⟨_, -, -, -, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := hB 1 1
  have e := hS F E σ hcm J hJ (Ainf F) hR _ _ mi (k1 1 1) (k2 1) hmi (xI x) (n : AF F).1 s (isNm_inf hxn) hs
  have hmeas := meas_mul hcm (Ainf F) hR (xI x : Ainf F ⊗[F] E)
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := hc.measurable.ennreal_ofReal
  have hu : IsUnit ((n : AF F).1 * s) := (IsUnit.map (fstA F) n.isUnit).mul hs
  have hint := (hmi.2.2 φ hc hcs hsu).1 _ (isUnit_hermScal (σ := σ) (E := E) (Ainf F) hu)
  rw [Gi, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0), ← e, lintegral_map hφm hmeas]

end Fibre

section Term

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Matrix (Fin 1) (Fin 1) E} {d : ℕ} {b : Module.Basis (Fin d) F E}

theorem smul_apply' {α : Type} [MeasurableSpace α] (c : ℝ≥0) (ν : Measure α) (B : Set α) :
    (c • ν) B = (c : ℝ≥0∞) * ν B := by
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem idele_ne (a : (AF F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : (a : AF F).2 v ≠ 0 :=
  (IsUnit.map ((evalV F v).comp (sndA F)) a.isUnit).ne_zero

theorem pr_fst (t : Fˣ) (n : (AF F)ˣ) : ((pr t * n : (AF F)ˣ) : AF F).1 = (n : AF F).1 * algebraMap F (Ainf F) t :=
  mul_comm _ _

theorem pr_snd (t : Fˣ) (n : (AF F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((pr t * n : (AF F)ˣ) : AF F).2 v = (n : AF F).2 v * algebraMap F (Fv F v) t :=
  mul_comm _ _

theorem eventually_preimage (hcm : IsCMExt F E σ) (x : (AF F ⊗[F] E)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      (fun (Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E) a i => (xV v x : Fv F v ⊗[F] E) * Y a i) ⁻¹' latV b v = latV b v := by
  filter_upwards [eventually_goodV b, eventually_int hcm b (x : AF F ⊗[F] E),
    eventually_int hcm b ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)] with v g1 g2 g3
  ext Y
  simp only [Set.mem_preimage, mem_latV_iff]
  constructor
  · intro h a i
    have e : Y a i = pV v ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((xV v x : Fv F v ⊗[F] E) * Y a i) := by
      have e1 : (xV v x : Fv F v ⊗[F] E) = pV v (x : AF F ⊗[F] E) := rfl
      rw [e1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    rw [e]
    exact IntE.mul g1 g3 (h a i)
  · intro h a i
    exact IntE.mul g1 g2 (h a i)

theorem term_eq (hS : Scal) (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) {li : Measure (Ainf F)} (hli : IsStdInf li)
    {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)} (hlam : ∀ v, IsStdV v (lam v))
    {μ : Measure (HA (AF F) σ J)} {𝓕 : Set (HA (AF F) σ J)}
    {mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 1 → Fv F v ⊗[F] E)}
    (hmi : IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 1) (coordHerm (Ainf F) σ b li 1) mi)
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 1) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    {κ : ℝ≥0} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hL : ∀ v, v ∉ S → ∀ s : Fv F v, s ≠ 0 →
      (cfac E v : ℝ) * (m v (hermScal (Fv F v) σ s) (latV b v)).toReal = rv v (eR E v) s)
    {φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ} {A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)}
    (ht : IsTest σ J b S φ A) {x : (AF F ⊗[F] E)ˣ} {n : (AF F)ˣ} (hxn : IsNm σ x n) (t : Fˣ)
    (hEP : EP b μ 𝓕 mi m (t : F) κ) :
    ∫⁻ X in {X | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v},
      ENNReal.ofReal (φ (projInf fun a i => (x : AF F ⊗[F] E) * X a i)) ∂(thetaMeas σ J μ 𝓕 (sph σ J (t : F))) =
    (κ : ℝ≥0∞) * PositivityTheory.Rg.Base1.pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) (pr t * n) := by
  obtain ⟨hφc, hφs, hφ0, hφu, hAS, hAo⟩ := ht
  set a : (AF F)ˣ := pr t * n with ha
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E) := fun v =>
    (fun Y a i => (xV v x : Fv F v ⊗[F] E) * Y a i) ⁻¹' A v
  have hco : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => by
    by_cases hv : v ∈ S
    · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
    · rw [hAo v hv]
      exact (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1).2.2.2.1 v
  have hloc : ∀ v, MeasurableSet (A' v) ∧
      m v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (A' v) = m v (hermScal (Fv F v) σ ((a : AF F).2 v)) (A v) ∧
      m v (hermScal (Fv F v) σ ((a : AF F).2 v)) (A v) < ⊤ := fun v => by
    have hRv := GlobalTheory.T.completion_is_local_ring F v
    have hRv' := hRv
    obtain ⟨_, _, _, _, -⟩ := hRv'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, -, -, -, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    have := hB 1 1
    obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have hA := (hco v).2.measurableSet
    refine ⟨meas_mul hcm (Fv F v) hRv _ hA, ?_, ?_⟩
    · rw [pr_snd]
      exact map_scal hS hcm hJ (Fv F v) hRv (k1 1 1) (k2 1) (hm v) (xV v x) (isNm_v v hxn) (t.isUnit.map _) hA
    · have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 1 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 1) (k2 1) (hm v)
        (hermScal (Fv F v) σ ((a : AF F).2 v))).1
      exact (hco v).1.measure_lt_top
  have hcof : ∀ᶠ v in cofinite, A' v = latV b v := by
    filter_upwards [eventually_preimage (b := b) hcm x, S.finite_toSet.eventually_cofinite_notMem] with v h1 h2
    have h3 : v ∉ S := by simpa using h2
    simp only [A', hAo v h3]
    exact h1
  have hφinf : Measurable fun Y : Fin 1 → Fin 1 → Ainf F ⊗[F] E =>
      ENNReal.ofReal (φ (fun a i => (xI x : Ainf F ⊗[F] E) * Y a i)) := by
    have : BorelSpace (Ainf F) := ⟨rfl⟩
    have hR := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
    have hR' := hR
    obtain ⟨_, _, _, _, -⟩ := hR'
    obtain ⟨_, -, -, -, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
    have := hB 1 1
    exact (hφc.measurable.comp (meas_mul hcm (Ainf F) hR _)).ennreal_ofReal
  have hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J (t : F))) κ (mi (hermScal (Ainf F) σ (algebraMap F _ (t : F))))
      (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ (t : F)))) := hEP
  obtain ⟨-, e⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 1 _ κ _ _ hEu _ A' hφinf (fun v => (hloc v).1)
    (fun v => by
      rw [smul_apply', (hloc v).2.1]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hloc v).2.2) hcof
  have hfv : ∀ v, v ∉ S → gv m A v ((a : AF F).2 v) = rv v (eR E v) ((a : AF F).2 v) := fun v hv => by
    rw [gv, hAo v hv]
    exact hL v hv _ (idele_ne a v)
  have hg : ∀ v, ((cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ (t : F)))) (A' v)).toReal =
      gv m A v ((a : AF F).2 v) := fun v => by
    rw [smul_apply', (hloc v).2.1, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rfl
  have hfin : (Function.mulSupport fun v => gv m A v ((a : AF F).2 v)).Finite := by
    have h1 : ∀ᶠ v in cofinite, gv m A v ((a : AF F).2 v) = 1 := by
      filter_upwards [idele_val a, S.finite_toSet.eventually_cofinite_notMem] with v h1 h2
      rw [hfv v (by simpa using h2)]
      exact rv_unit _ _ h1
    exact Filter.eventually_cofinite.1 h1
  have hprod : ∏' v, gv m A v ((a : AF F).2 v) = (∏ v ∈ S, gv m A v ((a : AF F).2 v)) *
      ∏ᶠ v : {v // v ∉ S}, rv v.1 (eR E v.1) ((a : AF F).2 v.1) := by
    rw [tprod_split S _ hfin]
    congr 1
    exact finprod_congr fun v => hfv v.1 v.2
  have hG : ∫⁻ Y, ENNReal.ofReal (φ (fun a i => (xI x : Ainf F ⊗[F] E) * Y a i))
      ∂(mi (hermScal (Ainf F) σ (algebraMap F _ (t : F)))) = ENNReal.ofReal (Gi mi φ (a : AF F).1) := by
    rw [inf_factor hS hcm hJ hli hmi hφc hφs hφ0 hφu hxn (t.isUnit.map _), pr_fst]
  have hG0 : 0 ≤ Gi mi φ (a : AF F).1 := integral_nonneg hφ0
  calc _ = ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A' v},
        ENNReal.ofReal (φ (fun a i => (xI x : Ainf F ⊗[F] E) * projInf X a i)) ∂(thetaMeas σ J μ 𝓕 (sph σ J (t : F))) := by
        simp only [projInf_mul, projV_mul]
        rfl
    _ = _ := e
    _ = _ := by
      simp only [hg]
      rw [hG, hprod, mul_assoc, ← ENNReal.ofReal_mul hG0, PositivityTheory.Rg.Base1.pure, mul_assoc]

end Term

section Support

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Matrix (Fin 1) (Fin 1) E} {d : ℕ} {b : Module.Basis (Fin d) F E}

theorem gramR_one (R : Type) [CommRing R] [Algebra F R] {j : F} (hj : J = fun _ _ => algebraMap F E j)
    (X : Fin 1 → Fin 1 → R ⊗[F] E) :
    gramR R σ J X 0 0 = sigR R σ (X 0 0) * ((1 : R) ⊗ₜ[F] algebraMap F E j) * X 0 0 := by
  subst hj
  simp [gramR, hR, hform, JR, inclR, Matrix.map_apply]
  rfl

theorem mem_H (hcm : IsCMExt F E σ) (hJ : IsHermND σ J)
    {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)} {li : Measure (Ainf F)}
    {mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 1 → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 1 → Fv F v ⊗[F] E)}
    (hmi : IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 1) (coordHerm (Ainf F) σ b li 1) mi)
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 1) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hL : ∀ v, v ∉ S → ∀ s : Fv F v, s ≠ 0 →
      (cfac E v : ℝ) * (m v (hermScal (Fv F v) σ s) (latV b v)).toReal = rv v (eR E v) s)
    {φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ} {A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)}
    (ht : IsTest σ J b S φ A) {H : Subgroup (AF F)ˣ} (hH : IsH σ H) (a : (AF F)ˣ)
    (h : PositivityTheory.Rg.Base1.pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) a ≠ 0) : a ∈ H := by
  obtain ⟨hφc, hφs, hφ0, hφu, hAS, hAo⟩ := ht
  have h1 : Gi mi φ (a : AF F).1 * (∏ v ∈ S, gv m A v ((a : AF F).2 v)) *
      ∏ᶠ v : {v // v ∉ S}, rv v.1 (eR E v.1) ((a : AF F).2 v.1) ≠ 0 := by
    intro h0
    apply h
    rw [PositivityTheory.Rg.Base1.pure, h0]
    simp
  have hGne := left_ne_zero_of_mul (left_ne_zero_of_mul h1)
  have hPne := right_ne_zero_of_mul (left_ne_zero_of_mul h1)
  have hQne := right_ne_zero_of_mul h1
  have hfinQ : (Function.mulSupport fun v : {v // v ∉ S} => rv v.1 (eR E v.1) ((a : AF F).2 v.1)).Finite := by
    have h2 : ∀ᶠ v in cofinite, rv v (eR E v) ((a : AF F).2 v) = 1 := (idele_val a).mono fun v hv => rv_unit _ _ hv
    exact ((Filter.eventually_cofinite.1 h2).preimage Subtype.val_injective.injOn).subset fun v hv => hv
  have hv : ∀ v, m v (hermScal (Fv F v) σ ((a : AF F).2 v)) (A v) ≠ 0 := fun v => by
    by_cases hvS : v ∈ S
    · have h3 := Finset.prod_ne_zero_iff.1 hPne v hvS
      intro h0
      apply h3
      simp [gv, h0]
    · have h3 := ne_zero_of_finprod _ hfinQ hQne ⟨v, hvS⟩
      simp only at h3
      rw [← hL v hvS _ (idele_ne a v)] at h3
      rw [hAo v hvS]
      intro h0
      apply h3
      simp [h0]
  choose Z hZA hZg using fun v => exists_of_fib_ne (hm v) _ (hv v)
  have hI : mi (hermScal (Ainf F) σ (a : AF F).1) {X | φ X ≠ 0} ≠ 0 := by
    intro h0
    apply hGne
    rw [Gi]
    exact integral_eq_zero_of_ae (ae_iff.2 h0)
  obtain ⟨Y, -, hYg⟩ := exists_of_fib_ne hmi _ hI
  have hZl : ∀ᶠ v in cofinite, Z v ∈ latV b v := by
    filter_upwards [S.finite_toSet.eventually_cofinite_notMem] with v h2
    rw [← hAo v (by simpa using h2)]
    exact hZA v
  have hP := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨X, hX1, hX2⟩ := hP.2.2.2.2.2.2.2.1 Y Z hZl
  obtain ⟨j, hj, hj0, -⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm J hJ.1
  have hj1 := hj0 hJ.2
  set y : AF F ⊗[F] E := X 0 0 with hy
  have hyI : pI y = Y 0 0 := by
    rw [← hX1]
    rfl
  have hyV : ∀ v, pV v y = Z v 0 0 := fun v => by
    rw [← hX2 v, projV_projFin_apply]
  have hw : sigR (AF F) σ y * ((1 : AF F) ⊗ₜ[F] algebraMap F E j) * y = (a : AF F) ⊗ₜ[F] (1 : E) := by
    have key := hP.2.2.2.2.2.2.1 (fun _ _ => sigR (AF F) σ y * ((1 : AF F) ⊗ₜ[F] algebraMap F E j) * y)
      (fun _ _ => (a : AF F) ⊗ₜ[F] (1 : E)) ?_ ?_
    · exact congrFun (congrFun key 0) 0
    · funext c i
      simp only [projInf_apply, map_mul]
      have e1 : pI (sigR (AF F) σ y) = sigR (Ainf F) σ (pI y) := map_sigR (fstA F) _
      have e2 : pI ((1 : AF F) ⊗ₜ[F] algebraMap F E j) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E j := rfl
      have e3 : pI ((a : AF F) ⊗ₜ[F] (1 : E)) = (a : AF F).1 ⊗ₜ[F] (1 : E) := rfl
      rw [e1, e2, e3, hyI, ← gramR_one (Ainf F) hj Y, hYg]
      rfl
    · intro v
      funext c i
      simp only [projV_projFin_apply, map_mul]
      have e1 : pV v (sigR (AF F) σ y) = sigR (Fv F v) σ (pV v y) := map_sigR ((evalV F v).comp (sndA F)) _
      have e2 : pV v ((1 : AF F) ⊗ₜ[F] algebraMap F E j) = (1 : Fv F v) ⊗ₜ[F] algebraMap F E j := rfl
      have e3 : pV v ((a : AF F) ⊗ₜ[F] (1 : E)) = (a : AF F).2 v ⊗ₜ[F] (1 : E) := rfl
      rw [e1, e2, e3, hyV, ← gramR_one (Fv F v) hj (Z v), hZg v]
      rfl
  have hc : ((1 : AF F) ⊗ₜ[F] algebraMap F E j) = (algebraMap F (AF F) j) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hinv : y * ((((a⁻¹ : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] algebraMap F E j) * sigR (AF F) σ y) = 1 := by
    calc _ = (((a⁻¹ : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) * (sigR (AF F) σ y * ((1 : AF F) ⊗ₜ[F] algebraMap F E j) * y) := by ring
      _ = 1 := by rw [hw, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, mul_one]; rfl
  let xu : (AF F ⊗[F] E)ˣ := Units.mkOfMulEqOne y _ hinv
  let jU : Fˣ := Units.mk0 j hj1
  have hn : IsNm σ xu ((pr jU)⁻¹ * a) := by
    have e0 : (((pr jU)⁻¹ : (AF F)ˣ) : AF F) * algebraMap F (AF F) j = 1 := Units.inv_mul (pr jU)
    have e1 : ((((pr jU)⁻¹ * a : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) =
        ((((pr jU)⁻¹ : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) * ((a : AF F) ⊗ₜ[F] (1 : E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.val_mul]
    have e2 : ((((pr jU)⁻¹ : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) * ((algebraMap F (AF F) j) ⊗ₜ[F] (1 : E)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, e0, mul_one]
      rfl
    show ((((pr jU)⁻¹ * a : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) = sigR (AF F) σ y * y
    rw [e1, ← hw, hc]
    calc _ = (((((pr jU)⁻¹ : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E)) * ((algebraMap F (AF F) j) ⊗ₜ[F] (1 : E))) * (sigR (AF F) σ y * y) := by ring
      _ = _ := by rw [e2, one_mul]
  exact (hH a).2 ⟨jU, xu, _, hn, (mul_inv_cancel_left _ _).symm⟩

end Support

theorem thetaId : Scal → LocR → ThetaId := by
  intro hS hLoc F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm κ hκ
  have hL0 := hLoc F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm
  refine ⟨(Filter.eventually_cofinite.1 hL0).toFinset, fun S hS0 φ A ht => ?_⟩
  have hL : ∀ v, v ∉ S → ∀ s : Fv F v, s ≠ 0 →
      (cfac E v : ℝ) * (m v (hermScal (Fv F v) σ s) (latV b v)).toReal = rv v (eR E v) s := fun v hv => by
    by_contra hc
    exact hv (hS0 (by simpa using hc))
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  refine ⟨fun x n hxn => ?_, fun H hH a ha => ?_⟩
  · rw [mean, thetaMeas_ne hcm hJ, Measure.restrict_sum_of_countable, lintegral_sum_measure, th,
      ← ENNReal.tsum_mul_left, ← (unitsEquivNeZero (G₀ := F)).tsum_eq]
    refine tsum_congr fun t => ?_
    exact term_eq hS hcm hJ hli hlam hmi hm hL ht hxn t (hκ t t.ne_zero)
  · by_contra h0
    exact ha (mem_H hcm hJ hmi hm hL ht hH a h0)

end GlobalTheory.CompanionTheory.RgBase.Theta

end
