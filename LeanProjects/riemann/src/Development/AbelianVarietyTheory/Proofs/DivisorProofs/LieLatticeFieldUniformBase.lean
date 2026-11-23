import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLeastHermLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisSmoothCommGroupSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTangentBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegralChangeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointDefinedOverNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointFibreOverNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreOfNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreChangeOfPolarizedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCharacterRankEqTorusRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelAfterExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelLocalizationTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartTangentSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianMapCochainFrameIndependenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianIntegralModelTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainFrameExtendsIntegrallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTangentCoefficientsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLieBasisComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverTorusSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingClosedAllFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionOpenLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsAlongFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundTorusPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormConjugatePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizationAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscUniformHermitianBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialMapHolomorphicUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialChartDerivativeBoundStatement

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdFib

section Chart

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram Filter

theorem eq_of_exp_eq {a b : ℝ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) :
    a = b := by
  obtain ⟨k, hk⟩ := exists_nat_gt |b - a|
  have hk0 : (0 : ℝ) < k := (abs_nonneg _).trans_lt hk
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k (by exact_mod_cast hk0))
  have hk1 : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : ((b - a : ℝ) : ℂ) = ((m * k : ℝ) : ℂ) := by
    push_cast
    field_simp at hm
    linear_combination hm
  have e' : b - a = m * k := by exact_mod_cast e
  rw [e', abs_mul, abs_of_pos hk0, mul_lt_iff_lt_one_left hk0] at hk
  have : m = 0 := by
    have : |m| < 1 := by exact_mod_cast hk
    exact Int.abs_lt_one_iff.1 this
  rw [this] at e'
  simp only [Int.cast_zero, zero_mul] at e'
  linarith

theorem limit_mem {n a g rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (hP : IsPeriodChart rk τ₀ B) {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    (hK : IsLatFam (Metric.ball 0 1) K) (Dn : ℂ)
    (h : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ i, z (Fin.castLE ha i) ≠ 0) → ∀ large₂ : Fin a → ℂ,
      (∀ i, Complex.exp (large₂ i) = z (Fin.castLE ha i)) → ∀ m m' : Fin g → ℤ,
      Dn • ((fun i => (m i : ℂ)) + period τ₀ B z large₂ *ᵥ fun i => (m' i : ℂ)) ∈ K z)
    {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ Metric.ball (0 : Fin n → ℂ) 1) (m m' : Fin g → ℤ)
    (hm : ∀ i, z₀ (Fin.castLE ha i) = 0 → B i *ᵥ m' = 0) :
    Dn • ((fun i => (m i : ℂ)) + period τ₀ B z₀ (fun i => Complex.log (z₀ (Fin.castLE ha i))) *ᵥ fun i => (m' i : ℂ)) ∈
      K z₀ := by
  classical
  let b : Fin a → Fin g → ℂ := fun i => (B i).map (Int.cast : ℤ → ℂ) *ᵥ fun i => (m' i : ℂ)
  have hb : ∀ i, z₀ (Fin.castLE ha i) = 0 → b i = 0 := fun i hi => funext fun k => by
    have := congrArg (Int.cast : ℤ → ℂ) (congrFun (hm i hi) k)
    simpa [b, Matrix.mulVec, dotProduct] using this
  have hper : ∀ z large₂, (period τ₀ B z large₂ *ᵥ fun i => (m' i : ℂ)) =
      (τ₀ z *ᵥ fun i => (m' i : ℂ)) + ∑ i, (large₂ i / (2 * Real.pi * Complex.I)) • b i := fun z large₂ => by
    simp only [period, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, b]
  let G : (Fin n → ℂ) → Fin g → ℂ := fun z => Dn • ((fun i => (m i : ℂ)) + ((τ₀ z *ᵥ fun i => (m' i : ℂ)) +
    ∑ i, ((Complex.log (z₀ (Fin.castLE ha i)) + Complex.log (z (Fin.castLE ha i) / z₀ (Fin.castLE ha i))) /
      (2 * Real.pi * Complex.I)) • b i))
  have hball : Metric.ball (0 : Fin n → ℂ) 1 = polydisc n 1 := by
    ext z
    simp [polydisc, pi_norm_lt_iff one_pos]
  have hGc : ContinuousAt G z₀ := by
    refine ContinuousAt.const_smul (continuousAt_const.add (ContinuousAt.add
      (f := fun z => τ₀ z *ᵥ fun i => (m' i : ℂ)) ?_ ?_)) Dn
    · refine continuousAt_pi.2 fun k => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact tendsto_finset_sum _ fun l _ => ContinuousAt.mul
        ((hP.holo k l).continuousOn.continuousAt (hball ▸ Metric.isOpen_ball.mem_nhds hz₀)) continuousAt_const
    · refine tendsto_finset_sum _ fun i _ => ?_
      by_cases hi : z₀ (Fin.castLE ha i) = 0
      · simp only [hb i hi, smul_zero]
        exact tendsto_const_nhds
      · have c : ContinuousAt (fun z : Fin n → ℂ => Complex.log (z (Fin.castLE ha i) / z₀ (Fin.castLE ha i))) z₀ :=
          ContinuousAt.clog ((continuous_apply _).continuousAt.div_const _) (by simp [div_self hi])
        exact (((continuousAt_const (y := Complex.log (z₀ (Fin.castLE ha i)))).add c).div_const
          (2 * Real.pi * Complex.I)).smul (continuousAt_const (y := b i))
  have hG₀ : G z₀ = Dn • ((fun i => (m i : ℂ)) +
      period τ₀ B z₀ (fun i => Complex.log (z₀ (Fin.castLE ha i))) *ᵥ fun i => (m' i : ℂ)) := by
    rw [hper]
    refine congrArg (fun s => Dn • (_ + (_ + s))) (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hi : z₀ (Fin.castLE ha i) = 0
    · simp [hb i hi]
    · simp [div_self hi]
  rw [← hG₀]
  by_contra hn
  have h₁ : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ G z ∉ K z :=
    (continuousAt_id.prodMk hGc).eventually (hK.2.2.1.mem_nhds (x := (z₀, G z₀)) ⟨hz₀, hn⟩)
  have h₂ : ∃ᶠ z in 𝓝 z₀, z ∈ Set.pi Set.univ fun _ : Fin n => ({0}ᶜ : Set ℂ) :=
    mem_closure_iff_frequently.1 (dense_pi Set.univ (fun _ _ => dense_compl_singleton 0) z₀)
  obtain ⟨z, hz, hz1, hzK⟩ := (h₂.and_eventually h₁).exists
  have hz' : ∀ k, z k ≠ 0 := fun k => hz k trivial
  have := h z hz1 (fun i => hz' _) (fun i => if z₀ (Fin.castLE ha i) = 0 then Complex.log (z (Fin.castLE ha i)) else
    Complex.log (z₀ (Fin.castLE ha i)) + Complex.log (z (Fin.castLE ha i) / z₀ (Fin.castLE ha i))) (fun i => by
      split_ifs with hi
      · exact Complex.exp_log (hz' _)
      · rw [Complex.exp_add, Complex.exp_log hi, Complex.exp_log (div_ne_zero (hz' _) hi), mul_div_cancel₀ _ hi]) m m'
  refine hzK ?_
  rw [hper] at this
  convert this using 5 with i
  split_ifs with hi
  · simp [hb i hi]
  · rfl

theorem abLe_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {y₀ : CxPts (genStr Z) σ} {n a : ℕ} (ha : a ≤ n) {g rk : ℕ}
    {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {B : Fin a → Matrix (Fin g) (Fin g) ℤ}
    {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)} {ex : ExpMaps Z σ g} {d : ℝ} {Dn : ℕ}
    (hP : IsPeriodChart rk τ₀ B) (hE : IsExpChart e ex) (hx₀ : y₀ ∈ e.source) (h0 : e y₀ = 0) (hd : 0 < d) (hD : 0 < Dn)
    (hin : ∀ x ∈ e.source, Inner x ↔ ∀ i : Fin a, e x (Fin.castLE ha i) ≠ 0)
    (hcl : ∀ x ∈ e.source, Inner x → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (hodgeGram ha τ₀ B (e x))⁻¹) v w).im : ℂ) / k) →
      GlobalTheory.UU.CubWeil Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) ∧
      ∀ large₂ : Fin a → ℂ, (∀ i, Complex.exp (large₂ i) = e x (Fin.castLE ha i)) → ∀ m m' : Fin g → ℤ,
        ex x ((Dn : ℂ) • ((fun i => (m i : ℂ)) + period τ₀ B (e x) large₂ *ᵥ fun i => (m' i : ℂ))) = 1)
    (met : ∀ y : CxPts (genStr Z) σ, TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ)
    {U₁ : Set (CxPts (genStr Z) σ)} (hU₁ : U₁ ∈ 𝓝 y₀) {C₂ : ℝ}
    (hm : ∀ y ∈ U₁, ∀ (v : TanM (y.1 ≫ genι Z) Z.t.G) (w : Fin g → ℂ),
      IsDerivAt0 (fun u => (ex y u).left) w (tv v).left → ‖w‖ ^ 2 ≤ C₂ * (met y v v).re) :
    ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, ∀ y ∈ U, AbLe (met y) C := by
  obtain ⟨ρ, C₁, hρ, hρ1, hC₁, hpure⟩ := GlobalTheory.T.polydisc_uniform_hermitian_bound n a g rk ha τ₀ B d Dn hP hd hD
  obtain ⟨htarget, -, -, hadd, hjoint, htan⟩ := hE
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz => e.map_target (htarget ▸ hz)
  have hri : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e (e.symm z) = z := fun z hz => e.right_inv (htarget ▸ hz)
  have hExpAt : ∀ y ∈ e.source, IsExpAt Z.t (y.1 ≫ genι Z) (ex y) := fun y hy =>
    ⟨hadd y hy, (htan y hy).1, (htan y hy).2⟩
  have hzero : ∀ y ∈ e.source, ex y 0 = 1 := fun y hy => by
    have := hadd y hy 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    isLatFam_ker _ _ _ Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hinner : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ i, z (Fin.castLE ha i) ≠ 0) → Inner (e.symm z) :=
    fun z hz hnz => (hin _ (hsymm z hz)).2 fun i => by rw [hri z hz]; exact hnz i
  refine ⟨U₁ ∩ (e.source ∩ e ⁻¹' Metric.ball 0 ρ), inter_mem hU₁ (inter_mem (e.open_source.mem_nhds hx₀)
    ((e.continuousAt hx₀).preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds 0 hρ))), Real.pi * (C₁ * C₂), ?_⟩
  rintro y ⟨hy₁, hy₂, hy₃⟩
  obtain ⟨z₀, hz₀, rfl⟩ : ∃ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, e.symm z₀ = y := ⟨_, hy₃, e.left_inv hy₂⟩
  have hz₁ : z₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball hρ1 hz₀
  intro φ m hφ n' hn' u Hm χ hA v v' W h₁ h₂
  have hslice : IsHolTo Set.univ (fun w => (ex (e.symm z₀) w).left) := by
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z₀, w)) hHol isOpen_univ
      ((differentiableOn_const z₀).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz₁ (Set.mem_univ w)
    exact this
  obtain ⟨π, p₁, p₂, p₃, p₄⟩ := GlobalTheory.T.exponential_map_holomorphic_uniformization _ _ _ Z.t _ g (ex (e.symm z₀)) (hExpAt _ hy₂) hslice φ m hφ n' hn' u Hm χ hA
  obtain ⟨w, hw, -⟩ := (htan _ hy₂).2 _ (isTan_tv v)
  obtain rfl := p₁ w v' W (h₁ ▸ hw) h₂
  have key := hpure z₀ (fun k => (pi_norm_lt_iff hρ).1 (mem_ball_zero_iff.1 hz₀) k) (K z₀) n' π Hm hA.1 hA.2.1 p₂ p₃ ?_ ?_ w
  · rw [_root_.mul_assoc, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key.trans (mul_le_mul_of_nonneg_left (hm _ hy₁ v w hw) hC₁)) Real.pi_pos.le
  · intro v₁ hv₁ v₂ hv₂
    obtain ⟨ζ₁, rfl, a₁, b₁⟩ := hLF.2.2.2 z₀ hz₁ v₁ hv₁
    obtain ⟨ζ₂, rfl, a₂, b₂⟩ := hLF.2.2.2 z₀ hz₁ v₂ hv₂
    refine ⟨ζ₁, ζ₂, a₁.continuousAt, a₂.continuousAt, rfl, rfl, ?_⟩
    have c₁ : ∀ᶠ z in 𝓝 z₀, ζ₁ z ∈ K z :=
      ((continuousAt_id.prodMk a₁.continuousAt).eventually b₁).mono fun z h => h.2 rfl
    have c₂ : ∀ᶠ z in 𝓝 z₀, ζ₂ z ∈ K z :=
      ((continuousAt_id.prodMk a₂.continuousAt).eventually b₂).mono fun z h => h.2 rfl
    obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 (((Metric.isOpen_ball.eventually_mem hz₁).and (c₁.and c₂)).and
      (a₁.eventually_analyticAt.and a₂.eventually_analyticAt))
    filter_upwards [Metric.ball_mem_nhds z₀ hδ] with z hz hnz
    have hz' := (hB z hz).1.1
    refine eq_of_exp_eq fun k hk => ?_
    have hol : ∀ ζ : (Fin n → ℂ) → Fin g → ℂ, (∀ b ∈ Metric.ball z₀ δ, AnalyticAt ℂ ζ b) →
        IsHolTo (Metric.ball z₀ δ) fun b => (ex (e.symm b) ((k : ℂ)⁻¹ • ζ b)).left := fun ζ hζ => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (b, (k : ℂ)⁻¹ • ζ b)) hHol Metric.isOpen_ball
        (differentiableOn_id.prodMk ((differentiableOn_const ((k : ℂ)⁻¹)).smul
          fun b hb => (hζ b hb).differentiableAt.differentiableWithinAt))
        fun b hb => Set.mk_mem_prod (hB b hb).1.1 (Set.mem_univ _)
      exact this
    have q₁ := GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo Z.X Z.t.G Z.t.PP Z.t.cub n k (Metric.ball z₀ δ)
      (fun b => (e.symm b).1 ≫ genι Z) (fun b => ex (e.symm b) ((k : ℂ)⁻¹ • ζ₁ b))
      (fun b => ex (e.symm b) ((k : ℂ)⁻¹ • ζ₂ b)) (Units.mk0 _ (Complex.exp_ne_zero _)) z₀ z hk Metric.isOpen_ball
      (convex_ball z₀ δ).isPreconnected (hol ζ₁ fun b hb => (hB b hb).2.1) (hol ζ₂ fun b hb => (hB b hb).2.2)
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hB b hb).1.1)) (hzero _ (hsymm _ (hB b hb).1.1)) hk (hB b hb).1.2.1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hB b hb).1.1)) (hzero _ (hsymm _ (hB b hb).1.1)) hk (hB b hb).1.2.2⟩)
      (Metric.mem_ball_self hδ) hz (p₄ k _ _ _ hk hv₁ hv₂ rfl)
    have q₂ := (hcl _ (hsymm z hz') (hinner z hz' hnz)).1 k _ _ (Units.mk0 _ (Complex.exp_ne_zero _)) hk
      (hB z hz).1.2.1 (hB z hz).1.2.2 rfl
    have q₃ := congrArg Units.val (unitOn_injective (q₂.unique q₁))
    rw [hri z hz'] at q₃
    exact q₃
  · refine ⟨fun i => Complex.log (z₀ (Fin.castLE ha i)), fun i hi => Complex.exp_log hi, fun m₁ m₂ hm₂ => ?_⟩
    refine limit_mem ha hP hLF Dn (fun z hz hnz large₂ hL m₁ m₂ => ?_) hz₁ m₁ m₂ hm₂
    have := (hcl _ (hsymm z hz) (hinner z hz hnz)).2 large₂ (by rw [hri z hz]; exact hL) m₁ m₂
    rwa [hri z hz] at this

theorem abLe_local : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, ∀ y ∈ U, AbLe (x.met σ y) C := by
  intro D A N j S κ s x σ hσ y₀
  obtain ⟨U', hU'⟩ : ∃ U' : Formalism.L2.PjFree.Unf (S.Xo κ.l) κ.c σ (S.Dw.p + S.Dw.q), Formalism.L2.PjFree.IsUnf U' := by
    rw [S.rank_eq]
    exact ⟨_, s.unif.law σ hσ⟩
  obtain ⟨n, a, ha, g, rk, τ₀, B, e, ex, d, Dn, hP, hE, hx₀, h0, hd, hD, hin, hcl⟩ :=
    GlobalTheory.T.exists_uniformization_at_point _ _ _ _ _ _ _ _ _ s.T σ U' hσ hU' y₀
  obtain ⟨U₁, hU₁, C₂, -, hm⟩ := GlobalTheory.T.exponential_chart_derivative_bound D A N j S κ s x σ n g e ex hE y₀ hx₀
  exact abLe_chart ha hP hE hx₀ h0 hd hD hin hcl (x.met σ) hU₁ hm

end Chart

theorem exists_hasModel : Hypotheses2 → HypothesesH → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp K)), ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K'), ∀ (K'' : Type) [Field K''] [NumberField K''] (j' : K' →+* K'') (A : Over (Sp K'')) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap (j'.comp j)) ψ → HasModel A := by
  intro p2 pH K _ _ P
  obtain ⟨K₁, _, _, a₁, h₁⟩ := GlobalTheory.T.semiabelian_model_after_extension pH.sieg 3 le_rfl (by decide) K P
  obtain ⟨K₂, _, _, a₂, h₂⟩ := GlobalTheory.T.semiabelian_model_after_extension pH.sieg 5 (by norm_num) (by decide) K P
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let io : K →ₐ[ℚ] Qb := IsAlgClosed.lift
  letI := a₁.toAlgebra
  letI := a₂.toAlgebra
  letI := (io : K →+* Qb).toAlgebra
  haveI : Algebra.IsAlgebraic K K₁ := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic K K₂ := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let i₁ : K₁ →ₐ[K] Qb := IsAlgClosed.lift
  let i₂ : K₂ →ₐ[K] Qb := IsAlgClosed.lift
  obtain ⟨K', _, _, i, j₁, j₂, e₁, e₂⟩ := exists_common (i₁ : K₁ →+* Qb) (i₂ : K₂ →+* Qb)
  have e : j₁.comp a₁ = j₂.comp a₂ := RingHom.ext fun a => i.injective
    (((RingHom.congr_fun e₁ _).trans (i₁.commutes a)).trans ((RingHom.congr_fun e₂ _).trans (i₂.commutes a)).symm)
  refine ⟨K', _, inferInstance, j₁.comp a₁, fun K'' _ _ j' A _ ψ hψ => ?_⟩
  refine GlobalTheory.T.semiabelian_model_localization_transfer p2.p22 K'' A ((3 : ℕ) : 𝓞 K'') ((5 : ℕ) : 𝓞 K'') (by norm_num) (by norm_num)
    (Nat.Coprime.cast (by norm_num)) (h₁ K'' (j'.comp j₁) A ψ hψ) (h₂ K'' (j'.comp j₂) A ψ ?_)
  rwa [e] at hψ

section Bounds

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (x : ToroidalCompactificationData s)

theorem exists_abLe_good (σ : κ.c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ) :
    ∃ C : ℝ, ∀ y : CxPts (genStr s.T.Z) σ, AbLe (x.met σ y) C := by
  classical
  haveI := CxPts.compactSpace σ (ProjSpace.isProjOver_pullback_snd _ s.T.Z.proj : IsProjOver (genStr s.T.Z))
  choose U hU C hC using abLe_local D A N j S κ s x σ hσ
  obtain ⟨T, -, hT⟩ := isCompact_univ.elim_nhds_subcover U fun y _ => hU y
  refine ⟨∑ a ∈ T, |C a|, fun y => ?_⟩
  obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  exact (hC a y hy).mono ((x.met_smooth σ).1 y)
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun a => |C a|) (fun _ _ => abs_nonneg _) ha))

theorem exists_abLe_at (σ : κ.c.F →+* ℂ) : ∃ C : ℝ, ∀ y : CxPts (genStr s.T.Z) σ, AbLe (x.met σ y) C := by
  by_cases hσ : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact exists_abLe_good s x σ hσ
  have hg : Formalism.L2.PjFree.GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by
    have := Formalism.L2.PjFree.goodEmb_goodOf κ.c σ
    unfold Formalism.L2.PjFree.goodOf at this
    rwa [if_neg hσ] at this
  obtain ⟨C, hC⟩ := exists_abLe_good s x _ hg
  refine ⟨C, fun y' => ?_⟩
  have cc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => Complex.conj_conj a))
  let y : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ) := ⟨spMap (starRingEnd ℂ) ≫ y'.1, by
    rw [Category.assoc, y'.2, ← Spec.map_comp]; rfl⟩
  have e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1 := by
    show _ = _ ≫ _ ≫ _
    rw [← Category.assoc, cc, Category.id_comp]
  exact GlobalTheory.T.hermitian_form_conjugate_points _ _ _ s.T.Z.t _ _ (by rw [e, Category.assoc]) (x.met _ y) (x.met σ y')
    (fun v v' h => x.met_conj _ _ y y' v v v' v' e h h) C (hC y)

theorem exists_abLe : ∃ C : ℝ, ∀ σ (y : CxPts (genStr s.T.Z) σ), AbLe (x.met σ y) C := by
  choose C hC using exists_abLe_at s x
  exact ⟨∑ σ, |C σ|, fun σ y => (hC σ y).mono ((x.met_smooth σ).1 y)
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun a => |C a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))⟩

def TorLe (y : Sp Qb ⟶ gen s.T.Z) (C : ℝ) (K : Type) [Field K] [NumberField K] (yK : Sp K ⟶ gen s.T.Z) : Prop :=
  ∃ (r : ℕ) (ε : Fin r → TanM (yK ≫ genι s.T.Z) s.T.Z.t.G), IsCochFrame s.T.Z.t (yK ≫ genι s.T.Z) ε ∧
    TorRk s.T.Z.t (y ≫ genι s.T.Z) r ∧ ∀ (σ : K →+* ℂ) (σ' : κ.c.F →+* ℂ) (z : CxPts (genStr s.T.Z) σ')
      (hz : spMap σ ≫ yK ≫ genι s.T.Z = z.1 ≫ genι s.T.Z),
      ((C : ℂ) • gramOf (x.met σ' z) (fun i => bcTan σ hz (ε i)) - 1).PosSemidef

theorem gramOf_posSemidef {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ} (hg : IsBlockMetric g)
    {n : ℕ} (u : Fin n → TanM z t.G) : (gramOf g u).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
  · ext a b
    exact (hg.1 _ _).symm
  · rw [← form_sum]
    by_cases h0 : ∑ a, v a • u a = 0
    · simp [h0]
    · exact (Complex.pos_iff.2 ⟨hg.2.1 _ h0, (Complex.conj_eq_iff_im.1 (hg.1 _ _).symm).symm⟩).le

variable {s x} in

theorem large_torLe_mono {y : Sp Qb ⟶ gen s.T.Z} {C C' : ℝ} (h : Large y (TorLe s x y C)) (hC : C ≤ C') :
    Large y (TorLe s x y C') := by
  obtain ⟨K₀, _, _, io₀, h⟩ := h
  refine ⟨K₀, _, inferInstance, io₀, fun K _ _ io j hj yK hy => ?_⟩
  obtain ⟨r, ε, h₁, h₂, h₃⟩ := h K io j hj yK hy
  refine ⟨r, ε, h₁, h₂, fun σ σ' z hz => ?_⟩
  have hd : (0 : ℂ) ≤ ((C' - C : ℝ) : ℂ) := Complex.zero_le_real.2 (sub_nonneg.2 hC)
  have := (h₃ σ σ' z hz).add ((gramOf_posSemidef ((x.met_smooth σ').1 z) fun i => bcTan σ hz (ε i)).smul hd)
  convert this using 1
  push_cast
  module

theorem torLe_step (p22 : GlobalTheory.Published.SemiAbelianHomExtension) (ts : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated) (a : gen s.T.Z) :
    ∃ (U : (gen s.T.Z).Opens) (C : ℝ), a ∈ U ∧ ∀ y : Sp Qb ⟶ gen s.T.Z, y (IsLocalRing.closedPoint Qb) ∈ U →
      a ⤳ y (IsLocalRing.closedPoint Qb) → Large y (TorLe s x y C) := by
  have hp := isProper_genStr s.T.Z
  obtain ⟨W, _, π, r, u, hπ, hW, ha, hu, hg, k, _, g, T, hk, hT⟩ :=
    GlobalTheory.T.exists_finite_cover_torus_split p22 _ _ _ s.T.Z.t κ.c.F _ (genStr s.T.Z) (genι s.T.Z) hp a
  have hcl := GlobalTheory.T.torus_embedding_closed_all_fibres ts W _ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (π ≫ genι s.T.Z) _ s.T.Z.t.semi) r u hu hg
  obtain ⟨U, hU, hrk⟩ := GlobalTheory.T.torus_extension_open_locus _ _ _ s.T.Z.t κ.c.F _ (genStr s.T.Z) (genι s.T.Z) hp k g T
  obtain ⟨C, hC⟩ := GlobalTheory.T.height_bound_torus_points D A N j S κ s x W π r u hπ hu hcl
  refine ⟨U, C, hk ▸ hU, fun y hy hay => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.T.algebraic_point_lifts_along_finite W _ π hπ y (ha ▸ hay)
  obtain ⟨K₀, _, _, io₀, w₀, hw₀⟩ := GlobalTheory.T.algebraic_point_defined_over_number_field κ.c.F W (π ≫ genStr s.T.Z) inferInstance w
  refine Large.of_point io₀ (w₀ ≫ π) (by rw [← Category.assoc, hw₀, hw]) fun K _ _ io j _ => ?_
  obtain ⟨ε, h₁, h₂⟩ := hC K (spMap j ≫ w₀) _ (Category.assoc _ _ _)
  exact ⟨r, ε, h₁, hT ▸ hrk y hy (hk ▸ hay), h₂⟩

theorem exists_torLe (p22 : GlobalTheory.Published.SemiAbelianHomExtension) (ts : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated) :
    ∃ C : ℝ, ∀ y : Sp Qb ⟶ gen s.T.Z, Large y (TorLe s x y C) := by
  have hp := isProper_genStr s.T.Z
  haveI : IsLocallyNoetherian (gen s.T.Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr s.T.Z)
  haveI : CompactSpace (gen s.T.Z) := QuasiCompact.compactSpace_of_compactSpace (genStr s.T.Z)
  haveI : IsNoetherian (gen s.T.Z) := {}
  suffices h : ∀ Z : TopologicalSpace.Closeds (gen s.T.Z), ∃ C : ℝ, ∀ y : Sp Qb ⟶ gen s.T.Z,
      y (IsLocalRing.closedPoint Qb) ∈ Z → Large y (TorLe s x y C) by
    obtain ⟨C, hC⟩ := h ⊤
    exact ⟨C, fun y => hC y trivial⟩
  intro Z
  induction Z using WellFoundedLT.induction with
  | ind Z ih =>
  rcases (Z : Set (gen s.T.Z)).eq_empty_or_nonempty with h0 | hne
  · exact ⟨0, fun y hy => absurd (show _ ∈ (Z : Set (gen s.T.Z)) from hy) (by simp [h0])⟩
  by_cases hirr : IsPreirreducible (Z : Set (gen s.T.Z))
  · obtain ⟨a, ha⟩ := QuasiSober.sober (α := gen s.T.Z) ⟨hne, hirr⟩ Z.isClosed
    obtain ⟨U, C₁, haU, h₁⟩ := torLe_step s x p22 ts a
    obtain ⟨C₂, h₂⟩ := ih (Z ⊓ U.compl) (inf_lt_left.2 fun h => h ha.mem haU)
    refine ⟨max C₁ C₂, fun y hy => ?_⟩
    by_cases hU : y (IsLocalRing.closedPoint Qb) ∈ U
    · exact large_torLe_mono (h₁ y hU (ha.specializes hy)) (le_max_left _ _)
    · exact large_torLe_mono (h₂ y ⟨hy, hU⟩) (le_max_right _ _)
  · rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
    push_neg at hirr
    obtain ⟨Z₁, Z₂, c₁, c₂, hZ, n₁, n₂⟩ := hirr
    obtain ⟨C₁, h₁⟩ := ih (Z ⊓ ⟨Z₁, c₁⟩) (inf_lt_left.2 n₁)
    obtain ⟨C₂, h₂⟩ := ih (Z ⊓ ⟨Z₂, c₂⟩) (inf_lt_left.2 n₂)
    refine ⟨max C₁ C₂, fun y hy => ?_⟩
    rcases hZ hy with h | h
    · exact large_torLe_mono (h₁ y ⟨hy, h⟩) (le_max_left _ _)
    · exact large_torLe_mono (h₂ y ⟨hy, h⟩) (le_max_right _ _)

theorem large_fibAt (p2 : Hypotheses2) (pH : HypothesesH) (y : Sp Qb ⟶ gen s.T.Z) : Large y fun K _ _ yK =>
    ∃ (φ : Fib K) (m : CubeMap φ.G s.T.Z.t.G), FibAt s.T.Z.t (yK ≫ genι s.T.Z) φ m ∧ HasModel φ.P.A := by
  obtain ⟨K₀, _, _, io₀, y₀, φ, m, hy, hφ⟩ : ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb)
      (y₀ : Sp K₀ ⟶ gen s.T.Z) (φ : Fib K₀) (m : CubeMap φ.G s.T.Z.t.G),
      spMap io₀ ≫ y₀ = y ∧ FibAt s.T.Z.t (y₀ ≫ genι s.T.Z) φ m := by
    by_cases hb : y (IsLocalRing.closedPoint Qb) ∈ genBd s.T.Z
    · exact GlobalTheory.T.algebraic_point_fibre_over_number_field _ _ _ _ _ _ _ _ _ s.T y hb
    · have hp := isProper_genStr s.T.Z
      obtain ⟨K₀, _, _, io₀, y₀, hy⟩ := GlobalTheory.T.algebraic_point_defined_over_number_field κ.c.F _ (genStr s.T.Z) inferInstance y
      obtain ⟨φ, m, hφ⟩ := GlobalTheory.T.exists_fibre_of_number_field_point _ _ _ _ _ _ s.T.Z K₀ y₀ fun h => hb (by
        rw [← hy]
        exact (Scheme.Hom.comp_apply (spMap io₀) y₀ _).symm ▸
          (congrArg y₀ (Subsingleton.elim (α := PrimeSpectrum K₀) _ _) ▸ h :))
      exact ⟨K₀, _, inferInstance, io₀, y₀, φ, m, hy, hφ⟩
  obtain ⟨K₁, _, _, j₁, hM⟩ := exists_hasModel p2 pH K₀ φ.P
  letI := j₁.toAlgebra
  letI := io₀.toAlgebra
  haveI : Algebra.IsAlgebraic K₀ K₁ := Algebra.IsAlgebraic.tower_top (K := ℚ) K₀
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let io₁ : K₁ →ₐ[K₀] Qb := IsAlgClosed.lift
  have e₁ : (io₁ : K₁ →+* Qb).comp j₁ = io₀ := RingHom.ext fun a => io₁.commutes a
  refine Large.of_point (io₁ : K₁ →+* Qb) (spMap j₁ ≫ y₀) ?_ fun K _ _ io j _ => ?_
  · rw [← hy, ← e₁, ← Category.assoc, ← Spec.map_comp]
    rfl
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre abelianSchemeLaws_all.1.polBaseChange (j.comp j₁) φ.P
  obtain ⟨φ', m', χ, ψ', rfl, -, h₁, -⟩ := GlobalTheory.T.fibre_change_of_polarized_field _ _ _ _ K₀ K (j.comp j₁) _ φ m hφ Q ψ hQ
  refine ⟨φ', m', ?_, hM K j _ ψ hQ.2.1⟩
  have e : (spMap j ≫ spMap j₁ ≫ y₀) ≫ genι s.T.Z = spMap (j.comp j₁) ≫ y₀ ≫ genι s.T.Z := by
    rw [← Category.assoc (spMap j), ← Spec.map_comp, Category.assoc]
    rfl
  exact e ▸ h₁

end Bounds

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} {t : SAB H X}
  {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK)

theorem torusExt_of_fibAt (p22 : GlobalTheory.Published.SemiAbelianHomExtension) (ts : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated) {φ : Fib K}
    {m : CubeMap φ.G t.G} (hφ : FibAt t xK φ m) (hM : HasModel φ.P.A) {r : ℕ} {ε : Fin r → TanM xK t.G}
    (hε : IsCochFrame t xK ε) (hrk : Module.finrank ℤ φ.X = r) {n : ℕ} {b : Fin n → TanM xK t.G}
    (hb : LieSmooth.TanBasis t b) (h : HermFam K (Fin n → K)) {C : ℝ}
    (hC : ∀ σ : K →+* ℂ, ∃ (z : Sp ℂ ⟶ X) (hz : spMap σ ≫ xK = z) (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ),
      IsBlockMetric g ∧ AbLe g C ∧ ((C : ℂ) • gramOf g (fun i => bcTan σ hz (ε i)) - 1).PosSemidef ∧
      ∀ u v, h.form σ u v = g (bcTan σ hz (∑ i, v i • b i)) (bcTan σ hz (∑ i, u i • b i))) :
    ∃ (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K)) (r : ℕ) (ε : Fin r → Fin n → K)
      (q : (Fin n → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h' ∧ TorusExt h (lieCoordLat t hx b) ε q h' F.lieLat C := by
  obtain ⟨G, _, θ, hG, hθ⟩ := hM
  haveI := φ.P.isAb.comm
  obtain ⟨v, hv⟩ := LieField.exists_isLieBasis_field K φ.P.A φ.P.g φ.P.smoothDim
  obtain ⟨q, hq, hqm⟩ := GlobalTheory.T.abelian_part_tangent_surjection _ _ _ _ K _ φ m hφ _ v hv
  obtain ⟨hli, hker⟩ := GlobalTheory.T.abelian_map_cochain_frame_independence _ _ _ _ K _ φ m hφ _ v hv q hqm r ε hε hrk
  obtain ⟨β, hβ⟩ : ∃ β : (Fin n → K) ≃ₗ[K] TanM xK t.G, ∀ c, β c = ∑ i, c i • b i :=
    ⟨(Module.Basis.mk hb.1 hb.2.ge).equivFun.symm, fun c => by simp⟩
  have hfull : Full (lieCoordLat t hx b) := by
    obtain ⟨m, r, M, hr, hM, hL, -⟩ := GlobalTheory.T.tangent_basis_integral_change t hx b hb
    exact GlobalTheory.CM.LieLattice.fg_and_span_eq_top _ r M hr (fun i => (hM i).2) hL
  let F : SemiFib K := SemiFib.mk φ.P G hG θ hθ v hv
  obtain ⟨h', hh'⟩ := F.exists_isHerm
  have hmem : ∀ c, c ∈ lieCoordLat t hx b ↔ ∃ w, bcTan (algebraMap (𝓞 K) K) hx w = β c := fun c => by
    rw [hβ]; rfl
  have hsp : ∀ c, c ∈ Submodule.span K (Set.range fun i => β.symm (ε i)) ↔ β c ∈ Submodule.span K (Set.range ε) := fun c => by
    simp only [Submodule.mem_span_range_iff_exists_fun]
    refine exists_congr fun a => ?_
    rw [← β.injective.eq_iff, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
  have hk : LinearMap.ker (q ∘ₗ β.toLinearMap) = Submodule.span K (Set.range fun i => β.symm (ε i)) := by
    ext c
    rw [hsp, ← hker, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe]
  refine ⟨F, h', r, fun i => β.symm (ε i), q ∘ₗ β.toLinearMap, hh', hfull,
    SemiFib.full_lieLat K F, hli.map' β.symm.toLinearMap β.symm.ker, hq.comp β.surjective, hk, ?_, ?_, fun σ => ?_⟩
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro c ⟨hc, hc'⟩
      obtain ⟨w, hw⟩ := (hmem c).1 hc
      have hc'' : β c ∈ Submodule.span K (Set.range ε) := hker ▸ hc'
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hc''
      choose a' ha' using GlobalTheory.T.integral_tangent_coefficients_integral ts _ _ _ _ K xO _ hx r ε hε a w (hw.trans ha.symm)
      refine (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).2 ⟨a', β.injective ?_⟩
      rw [← ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul K, ha', map_smul, LinearEquiv.apply_symm_apply]
    · rintro _ ⟨i, rfl⟩
      refine ⟨(hmem _).2 ?_, ?_⟩
      · rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.T.cochain_frame_extends_integrally p22 _ _ _ _ K xO _ hx r ε hε i
      · exact (hk ▸ Submodule.subset_span ⟨i, rfl⟩ : β.symm (ε i) ∈ LinearMap.ker (q ∘ₗ β.toLinearMap))
  · intro c hc
    obtain ⟨w, hw⟩ := (hmem c).1 hc
    have := GlobalTheory.T.semiabelian_integral_model_tangent p22 _ _ _ _ K xO _ hx φ m hφ G hG θ hθ v hv q hqm w
    rwa [hw] at this
  · obtain ⟨z, hz, g, hg, h₁, h₂, hh⟩ := hC σ
    have hgram : ∀ (n' : ℕ) (u : Fin n' → Fin n → K), h.gram σ u = gramOf g fun i => bcTan σ hz (β (u i)) := fun n u => by
      ext a b
      simp only [gramOf, HermFam.gram, of_apply, hβ, hh]
    refine ⟨?_, fun n u => ?_⟩
    · rw [hgram]
      simpa only [LinearEquiv.apply_symm_apply] using h₂
    · rw [hgram]
      exact GlobalTheory.T.semiabelian_lie_basis_comparison _ _ _ _ K _ φ m hφ G hG θ hθ v hv h' hh' q hqm σ _ hz _ _ hg h₁ n fun i => β (u i)

end Generic

section Main

open Formalism.MainNotions GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4 GlobalTheory.Mean4O

theorem torusExt_structure : Hypotheses2 → HypothesesH → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → OnObj fun D O _ _ H _ => ∀ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∃ C₀ : ℝ, ∀ y : Pt O.s, y ∉ H.int → ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb), ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ → ∀ (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)), IsLieAtWith O x P y K io L h → ∃ (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K)) (r : ℕ) (ε : Fin r → Fin (D.R.f * O.N) → K) (q : (Fin (D.R.f * O.N) → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h' ∧ TorusExt h L ε q h' F.lieLat C₀ := by
  intro p2 pH ts D O _ _ _ _ _ _ x P _
  obtain ⟨C₁, h₁⟩ := exists_abLe O.s x
  obtain ⟨C₂, h₂⟩ := exists_torLe O.s x p2.p22 ts
  refine ⟨max C₁ C₂, fun y _ => ?_⟩
  obtain ⟨K₀, i₁, i₂, io₀, hK⟩ := (large_fibAt O.s p2 pH y.y).and (large_torLe_mono (h₂ y.y) (le_max_right C₁ C₂))
  refine ⟨K₀, i₁, i₂, io₀, fun K _ _ io j hj L h hL => ?_⟩
  obtain ⟨fK, yK, xO, hx, hio, e, b, -, hf, hb, rfl, hh⟩ := hL
  obtain ⟨⟨φ, m, hφ, hM⟩, r, ε, hε, hr, hgr⟩ := hK K io j hj yK hio
  have hio' : spMap io ≫ yK ≫ genι O.s.T.Z = y.y ≫ genι O.s.T.Z := by rw [← Category.assoc, hio]
  have hrk : Module.finrank ℤ φ.X = r := by
    obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre abelianSchemeLaws_all.1.polBaseChange io φ.P
    obtain ⟨φ', m', -, -, -, -, a₁, -, -, -, a₂⟩ := GlobalTheory.T.fibre_change_of_polarized_field _ _ _ _ K Qb io _ φ m hφ Q ψ hQ
    exact a₂ ▸ GlobalTheory.T.fibre_character_rank_eq_torus_rank _ _ _ _ Qb _ φ' m' (hio' ▸ a₁) r hr
  refine torusExt_of_fibAt hx p2.p22 ts hφ hM hε hrk (LieSmooth.tanBasis_and_eigFrame_of_baseChange y io fK yK hio hf e b hb).1 h fun σ => ?_
  let z : CxPts (genStr O.s.T.Z) (σ.comp fK) := ⟨spMap σ ≫ yK, by
    rw [Category.assoc, hf, ← Spec.map_comp]; rfl⟩
  have hz : spMap σ ≫ yK ≫ genι O.s.T.Z = z.1 ≫ genι O.s.T.Z := (Category.assoc _ _ _).symm
  exact ⟨_, hz, x.met _ z, (x.met_smooth _).1 z, (h₁ _ z).mono ((x.met_smooth _).1 z) (le_max_left _ _), hgr σ _ z hz,
    hh σ z rfl⟩

end Main

end GlobalTheory.BdFib

end
