import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumPiProdEnnreal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
namespace GlobalTheory.LatCount
open scoped ENNReal

theorem tail_term {b : ℝ} (hb : 0 < b) (i : ℕ) :
    ((1 + b * ((i : ℝ) + 1)) ^ 2)⁻¹ ≤ 1 / b * ((1 + b * (i : ℝ))⁻¹ - (1 + b * ((i : ℝ) + 1))⁻¹) := by
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h1 : 0 < 1 + b * i := by positivity
  have h2 : 0 < 1 + b * ((i : ℝ) + 1) := by positivity
  have e2 : 1 / b * ((1 + b * (i : ℝ))⁻¹ - (1 + b * ((i : ℝ) + 1))⁻¹) =
      ((1 + b * i) * (1 + b * ((i : ℝ) + 1)))⁻¹ := by
    rw [inv_sub_inv h1.ne' h2.ne']
    field_simp
    ring
  rw [e2]
  exact inv_anti₀ (by positivity) (by nlinarith)

theorem tail_nonneg {b : ℝ} (hb : 0 < b) (i : ℕ) :
    0 ≤ 1 / b * ((1 + b * (i : ℝ))⁻¹ - (1 + b * ((i : ℝ) + 1))⁻¹) := by
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  refine mul_nonneg (by positivity) (sub_nonneg.2 (inv_anti₀ (by positivity) ?_))
  nlinarith

theorem tail_le {b : ℝ} (hb : 0 < b) :
    ∑' n : ℕ, ENNReal.ofReal (((1 + b * ((n : ℝ) + 1)) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 / b) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  calc ∑ i ∈ Finset.range n, ENNReal.ofReal (((1 + b * ((i : ℝ) + 1)) ^ 2)⁻¹)
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
          (1 / b * ((1 + b * (i : ℝ))⁻¹ - (1 + b * ((i : ℝ) + 1))⁻¹)) :=
        Finset.sum_le_sum fun i _ => ENNReal.ofReal_le_ofReal (tail_term hb i)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
          1 / b * ((1 + b * (i : ℝ))⁻¹ - (1 + b * ((i : ℝ) + 1))⁻¹)) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => tail_nonneg hb i).symm
    _ ≤ ENNReal.ofReal (1 / b) := by
        apply ENNReal.ofReal_le_ofReal
        have hs := Finset.sum_range_sub' (fun i : ℕ => (1 + b * (i : ℝ))⁻¹) n
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, inv_one] at hs
        rw [← Finset.mul_sum, hs]
        have : 0 ≤ (1 + b * (n : ℝ))⁻¹ := by positivity
        have hb1 : 0 < 1 / b := by positivity
        nlinarith

end GlobalTheory.LatCount

namespace GlobalTheory.LatCount
open scoped ENNReal

theorem tsum_int_split (g : ℤ → ℝ≥0∞) :
    ∑' z : ℤ, g z = g 0 + ∑' n : ℕ, g ((n : ℤ) + 1) + ∑' n : ℕ, g (-((n : ℤ) + 1)) := by
  have h1 : ∑' z : ℤ, g z = ∑' n : ℕ, g (n : ℤ) + ∑' n : ℕ, g (-((n : ℤ) + 1)) := by
    rw [tsum_of_nat_of_neg_add_one]
    · exact ENNReal.summable
    · exact ENNReal.summable
  have h2 : ∑' n : ℕ, g (n : ℤ) = g ((0 : ℕ) : ℤ) + ∑' n : ℕ, g (((n + 1 : ℕ) : ℤ)) := by
    rw [tsum_eq_zero_add']
    exact ENNReal.summable
  rw [h1, h2]
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]

theorem tsum_int_le {b : ℝ} (hb : 0 < b) :
    ∑' z : ℤ, ENNReal.ofReal (((1 + b * |(z : ℝ)|) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 / b) := by
  rw [tsum_int_split (fun z : ℤ => ENNReal.ofReal (((1 + b * |(z : ℝ)|) ^ 2)⁻¹))]
  have hpos : ∀ n : ℕ, |(((n : ℤ) + 1 : ℤ) : ℝ)| = (n : ℝ) + 1 := by
    intro n
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one]
    exact abs_of_nonneg (by positivity)
  have hneg : ∀ n : ℕ, |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
    intro n
    rw [Int.cast_neg, abs_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
    exact abs_of_nonneg (by positivity)
  have h0 : ENNReal.ofReal (((1 + b * |((0 : ℤ) : ℝ)|) ^ 2)⁻¹) = 1 := by simp
  simp only [hpos, hneg, h0]
  have ht := tail_le hb
  calc 1 + ∑' n : ℕ, ENNReal.ofReal (((1 + b * ((n : ℝ) + 1)) ^ 2)⁻¹) +
        ∑' n : ℕ, ENNReal.ofReal (((1 + b * ((n : ℝ) + 1)) ^ 2)⁻¹)
      ≤ 1 + ENNReal.ofReal (1 / b) + ENNReal.ofReal (1 / b) := add_le_add (add_le_add le_rfl ht) ht
    _ = ENNReal.ofReal (1 + 2 / b) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

end GlobalTheory.LatCount

namespace GlobalTheory.LatCount

open scoped ENNReal

theorem cone_pow_le {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (k : Fin r) : min c 1 ^ r ≤ t k := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min c 1 := lt_min hc one_pos
  have hm1 : min c 1 ≤ 1 := min_le_right _ _
  have key : ∀ n : ℕ, ∀ k : Fin r, (k : ℕ) + 1 + n = r → min c 1 ^ (n + 1) ≤ t k := by
    intro n
    induction n with
    | zero =>
      intro k hk
      simpa using (min_le_left c 1).trans (hlast k (by simpa using hk))
    | succ n ih =>
      intro k hk
      have hlt : (k : ℕ) + 1 < r := by omega
      have h1 := ih ⟨k + 1, hlt⟩ (by simp only; omega)
      have h2 := hstep k ⟨k + 1, hlt⟩ rfl
      calc min c 1 ^ (n + 1 + 1) = min c 1 * min c 1 ^ (n + 1) := by ring
        _ ≤ min c 1 * t ⟨k + 1, hlt⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨k + 1, hlt⟩ := mul_le_mul_of_nonneg_right (min_le_left _ _) (hpos _).le
        _ ≤ t k := h2
  have hk : (k : ℕ) + 1 + (r - (k + 1)) = r := by omega
  calc min c 1 ^ r ≤ min c 1 ^ (r - (k + 1) + 1) := pow_le_pow_of_le_one hm0.le hm1 (by omega)
    _ ≤ t k := key _ k hk

open NumberField in

theorem exists_repr_le (D : D7) : ∃ C : ℝ, 0 < C ∧ ∀ y : D.host.E,
    ∑ l, |((integralBasis D.host.E).repr y l : ℝ)| ≤ C * ∑ τ, ‖tauE D τ y‖ := by
  classical
  let B := canonicalEmbedding.latticeBasis D.host.E
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) → (((D.host.E →+* ℂ) → ℂ) →L[ℂ] ℂ) :=
    fun l => LinearMap.toContinuousLinearMap (B.coord l)
  refine ⟨∑ l, ‖f l‖ + 1, by positivity, fun y => ?_⟩
  have hnorm : ‖canonicalEmbedding D.host.E y‖ ≤ ∑ τ, ‖tauE D τ y‖ := by
    rw [canonicalEmbedding.norm_le_iff]
    intro φ
    obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
    have : ‖φ y‖ = ‖tauE D τ y‖ := by
      rw [← InfinitePlace.apply, ← InfinitePlace.apply]
      simp only at hτ
      rw [hτ]
    rw [this]
    exact Finset.single_le_sum (f := fun τ => ‖tauE D τ y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ τ)
  have hl : ∀ l, |((integralBasis D.host.E).repr y l : ℝ)| ≤
      ‖f l‖ * ‖canonicalEmbedding D.host.E y‖ := by
    intro l
    have h1 : f l (canonicalEmbedding D.host.E y) = ((integralBasis D.host.E).repr y l : ℂ) := by
      simp only [f, B, LinearMap.coe_toContinuousLinearMap']
      rw [Module.Basis.coord_apply, canonicalEmbedding.integralBasis_repr_apply]
    have h2 := (f l).le_opNorm (canonicalEmbedding D.host.E y)
    rw [h1] at h2
    have h3 : ‖((integralBasis D.host.E).repr y l : ℂ)‖ = |((integralBasis D.host.E).repr y l : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rwa [h3] at h2
  calc ∑ l, |((integralBasis D.host.E).repr y l : ℝ)|
      ≤ ∑ l, ‖f l‖ * ‖canonicalEmbedding D.host.E y‖ := Finset.sum_le_sum fun l _ => hl l
    _ = (∑ l, ‖f l‖) * ‖canonicalEmbedding D.host.E y‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ l, ‖f l‖ + 1) * ∑ τ, ‖tauE D τ y‖ :=
        mul_le_mul (by linarith) hnorm (norm_nonneg _) (by positivity)

end GlobalTheory.LatCount

namespace GlobalTheory.LatCount

open scoped ENNReal
open NumberField

theorem repr_int {D : D7} {x : D.host.E} (hx : IsIntegral ℤ x)
    (l : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) :
    (((⌊(integralBasis D.host.E).repr x l⌋ : ℤ) : ℚ)) = (integralBasis D.host.E).repr x l := by
  have h := NumberField.integralBasis_repr_apply (K := D.host.E) (⟨x, hx⟩ : 𝓞 D.host.E) l
  have e : algebraMap (𝓞 D.host.E) D.host.E ⟨x, hx⟩ = x := rfl
  rw [e, eq_intCast] at h
  rw [h, Int.floor_intCast]

theorem repr_nat_mul {D : D7} (L : ℕ) (y : D.host.E)
    (l : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) :
    (integralBasis D.host.E).repr ((L : D.host.E) * y) l = (L : ℚ) * (integralBasis D.host.E).repr y l := by
  have e : (L : D.host.E) * y = (L : ℚ) • y := by
    rw [Algebra.smul_def, map_natCast]
  rw [e, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem lattice_count : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (c : ℝ), 0 < c →
    ∃ (N A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ L : ℕ, 0 < L → ∀ t ∈ GlobalTheory.SiegelSet.cone r c,
      ∑' ξ : Matrix (Fin m) (Fin r) D.host.E,
        {ξ : Matrix (Fin m) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ ≤
        ENNReal.ofReal (C * (L : ℝ) ^ A) := by
  intro D θ hθ m r c hc
  classical
  obtain ⟨C, hC, hCb⟩ := exists_repr_le D
  let P := Fin m × Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let c0 : ℝ := min c 1 ^ r
  have hc0 : 0 < c0 := pow_pos (lt_min hc one_pos) _
  refine ⟨2 * Fintype.card P, Fintype.card P, (1 + 2 * C / c0) ^ Fintype.card P, by positivity,
    fun L hL t ht => ?_⟩
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by positivity
  set S := {ξ : Matrix (Fin m) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}
    with hS
  rw [← tsum_subtype S]
  let b : ℝ := c0 / (C * L)
  have hb : 0 < b := by positivity
  let kap : Matrix (Fin m) (Fin r) D.host.E → P → ℤ := fun ξ p =>
    ⌊(integralBasis D.host.E).repr ((L : D.host.E) * ξ p.1 p.2.1) p.2.2⌋
  have hint : ∀ ξ ∈ S, ∀ p : P, (((kap ξ p : ℤ) : ℚ)) =
      (L : ℚ) * (integralBasis D.host.E).repr (ξ p.1 p.2.1) p.2.2 := by
    intro ξ hξ p
    rw [← repr_nat_mul]
    exact repr_int (hξ p.1 p.2.1) p.2.2
  let G : (P → ℤ) → ℝ≥0∞ := fun k => ∏ p, ENNReal.ofReal (((1 + b * |((k p : ℤ) : ℝ)|) ^ 2)⁻¹)
  have hpt : ∀ ξ : S, ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
      ‖(compAt θ τ ((ξ : Matrix (Fin m) (Fin r) D.host.E).map (incA D) : Mx D m r) *
        diagonal (fun k => (t k : ℂ))) i j‖) ^ (2 * Fintype.card P))⁻¹ ≤ G (kap ξ) := by
    rintro ⟨ξ, hξ⟩
    show ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
      ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) *
        diagonal (fun k => (t k : ℂ))) i j‖) ^ (2 * Fintype.card P))⁻¹ ≤ G (kap ξ)
    have hcomp : ∀ τ, compAt θ τ (ξ.map (incA D) : Mx D m r) = ξ.map (tauE D τ) := by
      intro τ; ext i j; exact (hθ τ).1 (ξ i j)
    have htpos : ∀ k, 0 < t k := ht.1
    have hentry : ∀ τ i j, ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) *
        diagonal (fun k => (t k : ℂ))) i j‖ = ‖tauE D τ (ξ i j)‖ * t j := by
      intro τ i j
      rw [hcomp, Matrix.mul_diagonal, Matrix.map_apply, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (htpos j)]
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∑ τ, ∑ i, ∑ j, ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) *
        diagonal (fun k => (t k : ℂ))) i j‖ := ⟨_, rfl⟩
    rw [← hs]
    have hs0 : 0 ≤ s := by
      rw [hs]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hs_ge : b * ∑ p : P, |((kap ξ p : ℤ) : ℝ)| ≤ s := by
      have e1 : ∀ p : P, |((kap ξ p : ℤ) : ℝ)| =
          L * |((integralBasis D.host.E).repr (ξ p.1 p.2.1) p.2.2 : ℝ)| := by
        intro p
        have := congrArg (fun q : ℚ => (q : ℝ)) (hint ξ hξ p)
        simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
        rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have e2 : ∑ p : P, |((kap ξ p : ℤ) : ℝ)| =
          L * ∑ i, ∑ j, ∑ l, |((integralBasis D.host.E).repr (ξ i j) l : ℝ)| := by
        simp only [e1, P, Fintype.sum_prod_type, Finset.mul_sum]
      have e3 : s = ∑ i, ∑ j, ∑ τ, ‖tauE D τ (ξ i j)‖ * t j := by
        rw [hs]; simp only [hentry]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
      have hij : ∀ i j, c0 / C * ∑ l, |((integralBasis D.host.E).repr (ξ i j) l : ℝ)| ≤
          ∑ τ, ‖tauE D τ (ξ i j)‖ * t j := by
        intro i j
        have h1 := hCb (ξ i j)
        have htj : c0 ≤ t j := cone_pow_le hc ht j
        calc c0 / C * ∑ l, |((integralBasis D.host.E).repr (ξ i j) l : ℝ)|
            ≤ c0 / C * (C * ∑ τ, ‖tauE D τ (ξ i j)‖) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ∑ τ, c0 * ‖tauE D τ (ξ i j)‖ := by
              rw [← mul_assoc, div_mul_cancel₀ _ hC.ne', Finset.mul_sum]
          _ ≤ ∑ τ, ‖tauE D τ (ξ i j)‖ * t j := Finset.sum_le_sum fun τ _ => by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_left htj (norm_nonneg _)
      have hb' : b * L = c0 / C := by simp only [b]; field_simp
      rw [e2, e3, ← mul_assoc, hb', Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hij i j
    have hkp : ∀ p, 1 + b * |((kap ξ p : ℤ) : ℝ)| ≤ 1 + s := by
      intro p
      have h1 : |((kap ξ p : ℤ) : ℝ)| ≤ ∑ p : P, |((kap ξ p : ℤ) : ℝ)| :=
        Finset.single_le_sum (f := fun p => |((kap ξ p : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ p)
      have h2 := mul_le_mul_of_nonneg_left h1 hb.le
      linarith
    show ENNReal.ofReal (((1 + s) ^ (2 * Fintype.card P))⁻¹) ≤
      ∏ p, ENNReal.ofReal (((1 + b * |((kap ξ p : ℤ) : ℝ)|) ^ 2)⁻¹)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.prod_inv_distrib]
    apply inv_anti₀ (Finset.prod_pos fun p _ => by positivity)
    calc ∏ p, (1 + b * |((kap ξ p : ℤ) : ℝ)|) ^ 2 ≤ ∏ _p : P, (1 + s) ^ 2 :=
          Finset.prod_le_prod (fun p _ => by positivity)
            (fun p _ => pow_le_pow_left₀ (by positivity) (hkp p) 2)
      _ = (1 + s) ^ (2 * Fintype.card P) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hinj : Function.Injective (fun ξ : S => kap ξ) := by
    rintro ⟨ξ, hξ⟩ ⟨ξ', hξ'⟩ h
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    have hL0 : (L : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
    apply mul_left_cancel₀ hL0
    apply (integralBasis D.host.E).repr.injective
    ext l
    have h1 := hint ξ hξ (i, j, l)
    have h2 := hint ξ' hξ' (i, j, l)
    have h3 : kap ξ (i, j, l) = kap ξ' (i, j, l) := congrFun h (i, j, l)
    rw [repr_nat_mul, repr_nat_mul]
    rw [← h1, ← h2, h3]
  calc ∑' ξ : S, ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
      ‖(compAt θ τ ((ξ : Matrix (Fin m) (Fin r) D.host.E).map (incA D) : Mx D m r) *
        diagonal (fun k => (t k : ℂ))) i j‖) ^ (2 * Fintype.card P))⁻¹
      ≤ ∑' ξ : S, G (kap ξ) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' k, G k := ENNReal.tsum_comp_le_tsum_of_injective hinj G
    _ = ∏ _p : P, ∑' z : ℤ, ENNReal.ofReal (((1 + b * |(z : ℝ)|) ^ 2)⁻¹) :=
        GlobalTheory.HL.tsum_pi_prod_ennreal (X := fun _ : P => ℤ)
          (fun (_ : P) (z : ℤ) => ENNReal.ofReal (((1 + b * |(z : ℝ)|) ^ 2)⁻¹))
    _ ≤ ∏ _p : P, ENNReal.ofReal (1 + 2 / b) := Finset.prod_le_prod' fun _ _ => tsum_int_le hb
    _ = ENNReal.ofReal ((1 + 2 / b) ^ Fintype.card P) := by
        rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal ((1 + 2 * C / c0) ^ Fintype.card P * (L : ℝ) ^ Fintype.card P) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        have e : 2 / b = 2 * C / c0 * L := by
          simp only [b]; field_simp
        rw [e]
        have : 0 ≤ 2 * C / c0 := by positivity
        nlinarith

end GlobalTheory.LatCount
