import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralLeOfDisjointTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaSupPair

open MeasureTheory

theorem covolume_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ y, y ∈ GlobalTheory.dualLattice L ↔ J y ∈ L) : ZLattice.covolume L = 1 := by
  have h1 := GlobalTheory.covolume_mul_covolume_dualLattice L
  have h2 := ZLattice.covolume_comap L volume volume (e := J.toContinuousLinearEquiv)
    J.measurePreserving
  have h3 : GlobalTheory.dualLattice L = ZLattice.comap ℝ L J.toContinuousLinearEquiv.toLinearMap := by
    ext y
    rw [h]
    rfl
  rw [h3, h2] at h1
  have hp := ZLattice.covolume_pos L volume
  nlinarith

def mulI (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι where
  toFun x := Complex.I • x
  invFun x := (-Complex.I) • x
  map_add' x y := smul_add _ _ _
  map_smul' c x := by simp only [RingHom.id_apply]; rw [smul_comm]
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  norm_map' x := by simp [norm_smul]

theorem real_inner_eq_im {ι : Type} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    inner ℝ x y = (inner ℂ x (mulI ι y)).im := by
  change _ = (inner ℂ x (Complex.I • y)).im
  rw [inner_smul_right]
  simp [PiLp.inner_apply, Complex.inner]

theorem sup_le_euclidean (ι : Type) [Fintype ι] (A : AddSubgroup (EuclideanSpace ℂ ι)) (v : ℝ)
    (hv : 1 ≤ v) (hmin : ∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖x‖ ^ 2)
    (hspan : Submodule.span ℝ (A : Set (EuclideanSpace ℂ ι)) = ⊤)
    (hdual : ∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (inner ℂ y x).im = m)
    (G : EuclideanSpace ℂ ι → ℂ) (hG : Differentiable ℂ G)
    (hper : ∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2) =
      ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) :
    (∃ Fd : Set (EuclideanSpace ℂ ι), IsAddFundamentalDomain A Fd volume) ∧
      ∀ Fd : Set (EuclideanSpace ℂ ι), IsAddFundamentalDomain A Fd volume →
      ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤
        3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι *
          ⨍ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  set L : Submodule ℤ (EuclideanSpace ℂ ι) := AddSubgroup.toIntSubmodule A with hL
  have hv0 : 0 < v := by linarith
  haveI hdA : DiscreteTopology A := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set A) = Subtype.val ⁻¹' {x : EuclideanSpace ℂ ι | ‖x‖ ^ 2 < 1 / v} := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro rfl
        simpa using hv0
      · intro hx
        by_contra h0
        exact absurd (hmin x x.2 (fun h => h0 (Subtype.ext h))) (not_le.2 hx)
    rw [this]
    exact (isOpen_lt (by fun_prop) continuous_const).preimage continuous_subtype_val
  haveI : DiscreteTopology L := hdA
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  have hcov : ZLattice.covolume L = 1 := by
    refine covolume_eq_one L (mulI ι) fun y => ?_
    rw [GlobalTheory.mem_dualLattice]
    change _ ↔ mulI ι y ∈ A
    rw [hdual]
    refine forall_congr' fun x => forall_congr' fun _ => exists_congr fun m => ?_
    rw [real_inner_eq_im, eq_comm]
  let b := Module.Free.chooseBasis ℤ L
  have hF0 : IsAddFundamentalDomain A (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) volume :=
    ZLattice.isAddFundamentalDomain b volume
  refine ⟨⟨_, hF0⟩, fun Fd hFd z => ?_⟩
  haveI : Countable A := by
    have : Countable L := Countable.of_equiv _ b.repr.toEquiv.symm
    exact this
  have hvol : volume Fd = 1 := by
    have := ZLattice.covolume_eq_measure_fundamentalDomain L volume (F := Fd) hFd
    rw [hcov] at this
    exact (ENNReal.toReal_eq_one_iff _).1 this.symm
  have hcont : Continuous fun z : EuclideanSpace ℂ ι =>
      ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) := by
    have := hG.continuous
    fun_prop
  have hint : IntegrableOn (fun z : EuclideanSpace ℂ ι =>
      ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) Fd := by
    rw [hFd.integrableOn_iff hF0]
    · exact (hcont.continuousOn.integrableOn_compact
        (ZSpan.fundamentalDomain_isBounded _).isCompact_closure).mono_set subset_closure
    · intro g x
      have := hper g g.2 x
      rw [add_comm] at this
      exact this
  have := GlobalTheory.ThetaSupBall.sup_le_mean_square ι A v Fd G hv hmin hFd hvol hG hper hint z
  rwa [setAverage_eq, Measure.real, hvol, ENNReal.toReal_one, inv_one, one_smul]

theorem sup_le_coord {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
    [IsScalarTower ℝ ℂ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι]
    (φ : W ≃L[ℂ] EuclideanSpace ℂ ι) (A : AddSubgroup W) (v : ℝ)
    (hv : 1 ≤ v) (hmin : ∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖φ x‖ ^ 2)
    (hspan : Submodule.span ℝ (A : Set W) = ⊤)
    (hdual : ∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (inner ℂ (φ y) (φ x)).im = m)
    (G : W → ℂ) (hG : Differentiable ℂ G)
    (hper : ∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖φ (z + x)‖ ^ 2) =
      ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖φ z‖ ^ 2)) :
    (∃ Fd : Set W, IsAddFundamentalDomain A Fd μ) ∧
      ∀ Fd : Set W, IsAddFundamentalDomain A Fd μ →
      ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖φ z‖ ^ 2) ≤
        3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι *
          ⨍ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖φ w‖ ^ 2) ∂μ := by
  set A' : AddSubgroup (EuclideanSpace ℂ ι) := A.map φ.toLinearEquiv.toAddEquiv.toAddMonoidHom
    with hA'
  have hmem : ∀ x, x ∈ A' ↔ φ.symm x ∈ A := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, by simp⟩
  obtain ⟨⟨F0, hF0⟩, hB⟩ := sup_le_euclidean ι A' v hv
    (by
      intro x hx h0
      have := hmin _ ((hmem x).1 hx) (by simpa using h0)
      simpa using this)
    (by
      have : (A' : Set (EuclideanSpace ℂ ι)) =
          (φ.toLinearEquiv.toLinearMap.restrictScalars ℝ) '' (A : Set W) := rfl
      rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
      exact φ.surjective)
    (by
      intro x
      rw [hmem, hdual]
      constructor
      · intro h y hy
        simpa using h _ ((hmem y).1 hy)
      · intro h y hy
        simpa using h (φ y) ((hmem _).2 (by simpa using hy)))
    (fun w => G (φ.symm w)) (hG.comp φ.symm.differentiable)
    (by
      intro x hx z
      have := hper _ ((hmem x).1 hx) (φ.symm z)
      simpa using this)
  let e : EuclideanSpace ℂ ι ≃ᵐ W := φ.symm.toHomeomorph.toMeasurableEquiv
  let ν : Measure W := Measure.map e volume
  haveI : ν.IsAddHaarMeasure :=
    (φ.symm.toContinuousAddEquiv).isAddHaarMeasure_map volume
  have hν : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc : Measure.addHaarScalarFactor ν μ ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ).ne'
  have hmp : MeasurePreserving e volume ν := ⟨e.measurable, rfl⟩
  have h1 : ν ≪ μ := by rw [hν]; exact Measure.smul_absolutelyContinuous
  have h2 : μ ≪ ν := by
    rw [hν]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  let ε : A ≃ A' :=
    { toFun := fun x => ⟨φ x, (hmem _).2 (by simp)⟩
      invFun := fun x => ⟨φ.symm x, (hmem _).1 x.2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  constructor
  · refine ⟨e '' F0, IsAddFundamentalDomain.mono ?_ h2⟩
    refine hF0.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving ε ?_
    intro g x
    change φ.symm (φ g + x) = g + φ.symm x
    simp
  · intro Fd hFd z
    have hFd' : IsAddFundamentalDomain A' (e ⁻¹' Fd) volume := by
      refine (hFd.mono h1).preimage_of_equiv hmp.quasiMeasurePreserving ε.bijective ?_
      intro g x
      change φ.symm (φ g + x) = g + φ.symm x
      simp
    have := hB _ hFd' (φ z)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    have h3 : ⨍ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖φ w‖ ^ 2) ∂μ =
        ⨍ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖φ w‖ ^ 2) ∂ν := by
      rw [hν, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
        measureReal_nnreal_smul_apply]
      have : ((Measure.addHaarScalarFactor ν μ : NNReal) : ℝ) ≠ 0 := by exact_mod_cast hc
      simp only [smul_eq_mul, NNReal.smul_def, mul_inv]
      field_simp
    rw [h3, setAverage_eq, setAverage_eq, ← hmp.setIntegral_preimage_emb e.measurableEmbedding]
    congr 2
    · rw [Measure.real, Measure.real, e.map_apply]
    · ext w
      change _ = ‖G (φ.symm w)‖ ^ 2 * Real.exp (-Real.pi * ‖φ (φ.symm w)‖ ^ 2)
      simp

def coordEq (D : D7) (N N' : ℕ) (c : ℂ) (hc : c ≠ 0) :
    VC D N N' ≃L[ℂ] EuclideanSpace ℂ (D.what₂.Tau × Fin N' × Fin N) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => WithLp.toLp 2 fun k => c * z k.1 k.2.1 k.2.2
      invFun := fun w τ i j => c⁻¹ * w (τ, i, j)
      map_add' := fun x y => by ext k; simp [mul_add]
      map_smul' := fun a x => by ext k; simp [mul_left_comm]
      left_inv := fun x => by ext τ i j; simp [hc]
      right_inv := fun x => by ext k; simp [hc] }

theorem inner_coordEq (D : D7) (T : Tor D) (N N' : ℕ) (ha : 0 < area T.abelian₂)
    (hc : (((Real.sqrt (area T.abelian₂))⁻¹ : ℝ) : ℂ) ≠ 0) (x y : VC D N N') :
    inner ℂ (coordEq D N N' _ hc y) (coordEq D N N' _ hc x) = Hf D T x y := by
  have hs : (((Real.sqrt (area T.abelian₂))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (area T.abelian₂))⁻¹ : ℝ) : ℂ) =
      ((area T.abelian₂ : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt ha.le, Complex.ofReal_inv]
  rw [PiLp.inner_apply, Hf, div_eq_mul_inv, ← hs]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  change inner ℂ (_ * y τ i j) (_ * x τ i j) = _
  rw [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem Hf_add_re (D : D7) (T : Tor D) {N N' : ℕ} (z y : VC D N N') :
    (Hf D T (z + y) (z + y)).re = (Hf D T z z).re + 2 * (Hf D T z y).re + (Hf D T y y).re := by
  simp only [Hf, Complex.div_ofReal_re, Complex.re_sum, Pi.add_apply, Finset.mul_sum,
    Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem normSq_U (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) (y z : VC D N N') :
    ‖U D T y G z‖ ^ 2 = ‖G (z + y)‖ ^ 2 * Real.exp (-Real.pi * (Hf D T (z + y) (z + y)).re) *
      Real.exp (Real.pi * (Hf D T z z).re) := by
  rw [U, norm_mul, mul_pow, Complex.norm_exp, Hf_add_re, mul_assoc, ← Real.exp_add, sq (Real.exp _),
    ← Real.exp_add]
  congr 2
  simp
  ring

theorem area_pos (Λ : AddSubgroup ℂ) (P : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ P.lattice) :
    0 < area Λ := by
  have hp : 0 < |((starRingEnd ℂ) P.ω₁ * P.ω₂).im| := by
    refine abs_pos.2 fun h0 => ?_
    have h1 := LinearIndependent.pair_iff.1 P.indep
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
    have a := h1 P.ω₂.re (-P.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have b := h1 P.ω₂.im (-P.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have c := h1 0 1 (by apply Complex.ext <;> simp [a.1, b.1])
    exact one_ne_zero c.2
  have key : ∀ m n m' n' : ℤ,
      |((starRingEnd ℂ) (m * P.ω₁ + n * P.ω₂) * (m' * P.ω₁ + n' * P.ω₂)).im| =
      |((starRingEnd ℂ) P.ω₁ * P.ω₂).im| * |((m * n' - n * m' : ℤ) : ℝ)| := fun m n m' n' => by
    rw [← abs_mul]
    congr 1
    simp
    ring
  refine hp.trans_le (le_csInf ⟨_, hp, _, (h _).2 P.ω₁_mem_lattice, _, (h _).2 P.ω₂_mem_lattice, rfl⟩ ?_)
  rintro r ⟨hr, w₁, h1, w₂, h2, rfl⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h1)
  obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h2)
  rw [key] at hr ⊢
  have h0 : (m * n' - n * m' : ℤ) ≠ 0 := fun e => by simp [e] at hr
  have : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  exact le_mul_of_one_le_right hp.le this

theorem sup_translate_le : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (N N' : ℕ) L L', SD D L → SD D L' → ∀ G ∈ Th D (tor0 D cc δ) L L', ∀ (y z : VC D N N'),
      ‖U D (tor0 D cc δ) y G z‖ ^ 2 ≤
        3 * (2 * ((fF D * N * N' : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * N * N') *
          normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') G *
          Real.exp (Real.pi * (Hf D (tor0 D cc δ) z z).re) := by
  intro D hD cc δ hC N N' L L' hL hL' G hG y z
  obtain ⟨P, hP⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC
  obtain ⟨-, hlog, hrd, -, hcard, -⟩ := GlobalTheory.NormSum.letters_and_sizes D hD
  obtain ⟨-, -, hint, huni, -, hspan, hq⟩ := GlobalTheory.ThetaLine.theta_line D hD cc δ hC N N'
    (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)
  set T := tor0 D cc δ with hT
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hsd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 hd
  have ha : 0 < area T.abelian₂ := area_pos (lamOf D cc δ) P hP
  have hc : (((Real.sqrt (area T.abelian₂))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (inv_pos.2 (Real.sqrt_pos.2 ha)).ne'
  set φ := coordEq D N N' _ hc with hφ
  have hin : ∀ x y, inner ℂ (φ y) (φ x) = Hf D T x y := inner_coordEq D T N N' ha hc
  have hn : ∀ x, ‖φ x‖ ^ 2 = (Hf D T x x).re := by
    intro x
    rw [← hin, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  have hsq : Real.sqrt D.host.d ≤ D.host.rdE := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    rw [← Real.log_le_log_iff hd (by positivity), Real.log_pow]
    exact_mod_cast hlog
  haveI i1 : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i2 : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (VC D N N')).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨hex, hB⟩ := sup_le_coord (volume : Measure (VC D N N')) _ φ (La D T L L') D.host.rdE hrd
    (by
      intro x hx h0
      obtain ⟨m, hm⟩ := hq x hx
      rw [qH, ← hn] at hm
      have hp : 0 < ‖φ x‖ ^ 2 := by
        have : φ x ≠ 0 := by simpa using h0
        positivity
      have hm0 : (0 : ℝ) < m := by rw [← hm]; positivity
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hm0)
      rw [div_le_iff₀ (by linarith)]
      nlinarith)
    hspan
    (by
      intro x
      simp only [hin]
      exact ⟨fun hx y hy => hint x hx y hy, huni x⟩)
    G hG.1
    (by
      intro x hx z
      have h1 := congrArg (fun t => ‖t‖ ^ 2) (hG.2 x hx z)
      have h2 : ‖al D T x‖ = 1 := by simp [al, norm_zpow]
      simp only [norm_mul, h2, one_mul] at h1
      rw [hn, hn, ← h1, normSq_U, mul_assoc (_ * _), ← Real.exp_add]
      simp)
  have := hB _ (Classical.epsilon_spec hex) (z + y)
  simp only [hn] at this
  have hcd : Fintype.card (D.what₂.Tau × Fin N' × Fin N) = fF D * N * N' := by
    simp only [Fintype.card_prod, Fintype.card_fin, hcard]
    ring
  rw [hcd] at this
  rw [normSq_U]
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

end GlobalTheory.ThetaSupPair
