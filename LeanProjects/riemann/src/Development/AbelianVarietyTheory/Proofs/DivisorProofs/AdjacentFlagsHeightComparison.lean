import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionMetricCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityInequalityLogOneSubCosSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAdjugateMulEqSumPermRing
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyPartitionDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernMatrixIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesHeightCompareStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixDens
open scoped ComplexOrder

namespace GlobalTheory.AdjMix

section PartOne

def IsWeights (m : ℕ) (a : ℝ) (c : Fin (m + 2) → ℝ) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℝ R] (f : Polynomial R), f.natDegree < m + 2 →
    ∑ t, c t • f.eval ((t : ℕ) : R) = a • f.coeff 1

theorem exists_isWeights (m : ℕ) (a : ℝ) : ∃ c, IsWeights m a c := by
  let W : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := Matrix.vandermonde fun t => ((t : ℕ) : ℝ)
  have hW : IsUnit W.det := by
    rw [isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.2 fun s t h => Fin.ext (by exact_mod_cast h)
  let c := Matrix.vecMul (Pi.single 1 a) W⁻¹
  have hc : Matrix.vecMul c W = Pi.single 1 a := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hW, Matrix.vecMul_one]
  have hc' (j : Fin (m + 2)) : ∑ t, c t * ((t : ℕ) : ℝ) ^ (j : ℕ) = (Pi.single 1 a : Fin (m + 2) → ℝ) j := by
    rw [← hc]
    simp [Matrix.vecMul, dotProduct, W]
  refine ⟨c, fun R _ _ f hf => ?_⟩
  have e (t : Fin (m + 2)) : c t • f.eval ((t : ℕ) : R) =
      ∑ j : Fin (m + 2), (c t * ((t : ℕ) : ℝ) ^ (j : ℕ)) • f.coeff j := by
    rw [Polynomial.eval_eq_sum_range' hf, Finset.smul_sum, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, Algebra.smul_def (((t : ℕ) : ℝ) ^ (j : ℕ)), map_pow, map_natCast, mul_comm]
  rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
  simp only [← Finset.sum_smul, hc']
  rw [Finset.sum_eq_single 1 (fun j _ hj => by simp [hj]) (by simp)]
  simp

variable {d : ℕ} {c : Fin (d + 2) → ℝ}

theorem IsWeights.sum {a : ℝ} (hc : IsWeights d a c) : ∑ t, c t = 0 := by
  simpa [Polynomial.coeff_one] using hc ℝ 1 (by simp)

theorem IsWeights.pow (hc : IsWeights d ((d + 1 : ℝ)⁻¹) c) {R : Type} [CommRing R] [Algebra ℝ R] (N A : R) :
    ∑ t, c t • (N + (t : ℕ) * A) ^ (d + 1) = A * N ^ d := by
  have h := hc R ((Polynomial.C N + Polynomial.X * Polynomial.C A) ^ (d + 1)) (by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_pow_le.trans ?_)
    have : (Polynomial.C N + Polynomial.X * Polynomial.C A).natDegree ≤ 1 := by compute_degree
    nlinarith)
  have h1 : ((Polynomial.C N + Polynomial.X * Polynomial.C A) ^ (d + 1)).coeff 1 = (d + 1 : ℝ) • (A * N ^ d) := by
    have hd (P : Polynomial R) : P.coeff 1 = (Polynomial.derivative P).eval 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      simp
    rw [hd, Polynomial.derivative_pow, Algebra.smul_def]
    simp
    ring
  rw [h1, smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h
  simpa [mul_comm A] using h

theorem IsWeights.det (hc : IsWeights d ((d + 1 : ℝ)⁻¹) c) (A M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ∑ t, c t * ((d + 1).factorial / Real.pi ^ (d + 1) * (A + ((t : ℕ) : ℂ) • M).det.re) = mix d A M := by
  have h := hc ℂ (A.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det (by
    rw [add_comm (A.map _)]
    exact Nat.lt_succ_of_le ((Polynomial.natDegree_det_X_add_C_le M A).trans (by simp)))
  have ev (z : ℂ) : (A.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det.eval z =
      (A + z • M).det := by
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [mul_comm z]
  obtain ⟨P, hP⟩ := det_add_X_smul_first_variation ℂ _ A M
  simp only [ev] at h
  rw [hP] at h
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_zero, Polynomial.coeff_X_pow_mul',
    Polynomial.coeff_C_succ] at h
  have h' := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.real_smul, Complex.re_ofReal_mul] at h'
  norm_num at h'
  have e : ∑ t, c t * ((d + 1).factorial / Real.pi ^ (d + 1) * (A + ((t : ℕ) : ℂ) • M).det.re) =
      (d + 1).factorial / Real.pi ^ (d + 1) * ∑ t, c t * (A + ((t : ℕ) : ℂ) • M).det.re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e, h', mix, Nat.factorial_succ]
  push_cast
  field_simp

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem mix_sub (A M M' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : mix d A (M - M') = mix d A M - mix d A M' := by
  simp only [mix, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, mul_sub]

theorem isDens_chernDens {B : LB X} {φ : Weight p σ B} (h : φ.IsCInf) :
    IsDens fun (c : AlgChart p σ (d + 1)) y => c.chernDens φ y :=
  ((chernMat_isForm k X p σ _ B φ h).isDens_mix (chernMat_isForm k X p σ _ B φ h)).congr fun c y _ => by
    rw [mix_self]
    rfl

section Dens

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]

theorem total_sum (hR : Nonempty (AnRead p σ D)) {J : Type} [Fintype J] {ρ : J → AlgChart p σ D → CxPts p σ → ℝ}
    (h : ∀ j, IsDens (ρ j)) : total (fun c y => ∑ j, ρ j c y) = ∑ j, total (ρ j) := by
  obtain ⟨ν, w, _, -, -, -, h₁, h₂⟩ := exists_refMeasure k X p σ D hR
  choose g hg e using fun j => h₁ (ρ j) (h j)
  rw [Finset.sum_congr rfl fun j _ => (h₂ _ _ (hg j) (e j)).2, ← integral_finset_sum _ fun j _ =>
    (hg j).integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)]
  refine (h₂ _ _ (continuous_finset_sum _ fun j _ => hg j) fun c y hy => ?_).2
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => e j c y hy

theorem total_add_sub (hR : Nonempty (AnRead p σ D)) {ρ ρ' : AlgChart p σ D → CxPts p σ → ℝ} (h : IsDens ρ)
    (h' : IsDens ρ') : total (fun c y => ρ c y + ρ' c y) = total ρ + total ρ' ∧
      total (fun c y => ρ c y - ρ' c y) = total ρ - total ρ' := by
  obtain ⟨ν, w, _, -, -, -, h₁, h₂⟩ := exists_refMeasure k X p σ D hR
  obtain ⟨g, hg, e⟩ := h₁ ρ h
  obtain ⟨g', hg', e'⟩ := h₁ ρ' h'
  have i := hg.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  have i' := hg'.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  rw [(h₂ ρ g hg e).2, (h₂ ρ' g' hg' e').2, ← integral_add i i', ← integral_sub i i']
  exact ⟨(h₂ _ _ (hg.add hg') fun c y hy => by rw [e c y hy, e' c y hy, Pi.add_apply, add_mul]).2,
    (h₂ _ _ (hg.sub hg') fun c y hy => by rw [e c y hy, e' c y hy, Pi.sub_apply, sub_mul]).2⟩

theorem green_sum (hR : Nonempty (AnRead p σ D)) {J : Type} [Fintype J] (a : J → ℝ)
    {κ : J → AlgChart p σ D → CxPts p σ → ℝ} {η δ : AlgChart p σ D → CxPts p σ → ℝ} (hκ : ∀ j, IsDens (κ j))
    (hη : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, η c y = ∑ j, a j * κ j c y) (hδ : IsDens δ)
    {v f : CxPts p σ → ℝ} {S : Set (CxPts p σ)} (hv : Continuous v) (hv0 : ∀ y, 0 ≤ v y) (hSo : IsOpen S)
    (hS0 : ∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, part ρ Sᶜ = 0)
    (hSv : ∀ y ∈ S, v y < 1 ∧ f y = Real.log (1 - v y) / 2) (i₁ : ∀ j, IntegrableOn f S (part (κ j)))
    (i₂ : ∀ j, IntegrableOn f S (part fun c y => -κ j c y))
    (H : ∀ n : ℕ, total (fun c y => v y ^ (n + 1) * η c y + (n + 1) * v y ^ n * (1 - v y) * δ c y) = 0) :
    2 * ∑ j, a j * (∫ y in S, f y ∂(part (κ j)) - ∫ y in S, f y ∂(part fun c y => -κ j c y)) = total δ := by
  obtain ⟨ν, w, hfin, hν, -, -, hdens, hmeas⟩ := exists_refMeasure k X p σ D hR
  choose g hg hgw using fun j => hdens (κ j) (hκ j)
  obtain ⟨e, he, hew⟩ := hdens δ hδ
  have p₁ j := (hmeas (κ j) (g j) (hg j) (hgw j)).1
  have p₂ j := (hmeas (fun c y => -κ j c y) (fun y => -g j y) (hg j).neg
    fun c y hy => by rw [hgw j c y hy, neg_mul]).1
  have hSm : MeasurableSet S := hSo.measurableSet
  have hae : ∀ᵐ y ∂ν, y ∈ S := mem_ae_iff.2 (hν ▸ hS0 w)
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hF : Set.EqOn f (fun y => Real.log (1 - v y) / 2) S := fun y hy => (hSv y hy).2
  have key (j) := CurveDens.integrableOn_and_sub_withDensity (ν := ν) (hg j).measurable hSm
    ((p₁ j ▸ i₁ j).congr_fun hF hSm) ((p₂ j ▸ i₂ j).congr_fun hF hSm)
  simp only [IntegrableOn, hres] at key
  have hG : Continuous fun y => ∑ j, a j * g j y := continuous_finset_sum _ fun j _ => continuous_const.mul (hg j)
  have hs (y) : (∑ j, a j * g j y) * Real.log (1 - v y) = 2 * ∑ j, a j * (g j y * (Real.log (1 - v y) / 2)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hi : Integrable (fun y => (∑ j, a j * g j y) * Real.log (1 - v y)) ν := by
    simp only [hs]
    exact (integrable_finset_sum _ fun j _ => (key j).1.const_mul _).const_mul _
  have main := CurveDens.integral_log_eq_of_forall_pow (ν := ν) (v := v) (D := fun y => ∑ j, a j * g j y) (d := e)
    hv.measurable hG.measurable he.measurable
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    hv0 (hae.mono fun y hy => (hSv y hy).1) hi
    (fun n => by
      have hc : Continuous fun y => v y ^ (n + 1) * (∑ j, a j * g j y) +
          ((n : ℝ) + 1) * v y ^ n * (1 - v y) * e y := by fun_prop
      rw [← (hmeas _ _ hc fun c y hy => ?_).2]
      · exact H n
      · rw [hη c y hy, hew c y hy, Finset.sum_congr rfl fun j _ => by rw [hgw j c y hy, ← mul_assoc], ← Finset.sum_mul]
        ring)
  rw [(hmeas δ e he hew).2, ← main]
  simp only [hs]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => (key j).1.const_mul _]
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun j _ => ?_)
  rw [integral_const_mul, ← (key j).2, p₁, p₂, setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF]

end Dens

section Sq

open MvPolynomial

variable [IsIntegral X]

def IsSq (d : ℕ) (N A : HermLB p) (x : ℝ) : Prop :=
  ∃ Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ, IsArFun ![A, N] (d + 1) Ψ ∧
    Ψ (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ d) = x

variable {N A B : HermLB p} {x y : ℝ}

theorem IsSq.unique (hX : IsArithVar p (d + 1)) (h : IsSq d N A x) (h' : IsSq d N A y) : x = y := by
  obtain ⟨Ψ, h, rfl⟩ := h
  obtain ⟨Ψ', h', rfl⟩ := h'
  rw [Model.isArFun_unique hX h h']

theorem IsSq.congr (hC : Published.ArCalc) (hX : IsArithVar p (d + 1)) (e : A.Isometric B) (h : IsSq d N A x) :
    IsSq d N B x := by
  obtain ⟨Ψ, h, rfl⟩ := h
  refine ⟨Ψ, ((hC.arIso k X p _ hX).2 _ _ Ψ h).2.1 _ fun i => ?_, rfl⟩
  fin_cases i
  · exact e
  · exact .refl _

theorem isSq_of_comb (hC : Published.ArCalc) (hX : IsArithVar p (d + 1)) {κ : Type} [Fintype κ] {L : κ → HermLB p}
    {Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L (d + 1) Φ) {a n : κ → ℤ} (ha : (comb L a).Isometric A)
    (hn : (comb L n).Isometric N) :
    IsSq d N A (Φ (lin (fun j => (a j : ℝ)) ^ 2 * lin (fun j => (n j : ℝ)) ^ d)) := by
  refine ⟨_, ((hC.arIso k X p _ hX).2 _ _ Φ hΦ).2.2 (Fin 2) ![A, N] ![a, n] fun i => ?_, ?_⟩
  · fin_cases i
    · exact ha
    · exact hn
  · simp

abbrev slide (L L' N : HermLB p) (t : ℕ) : HermLB p := comb ![L, L', N] ![t, -t, 1]

theorem isSq_sub [IsLocallyNoetherian X] (hC : Published.ArCalc) (hX : IsArithVar p (d + 1))
    (hc : IsWeights d ((d + 1 : ℝ)⁻¹) c) {L Q L' Q' : HermLB p} (e : (L.tens Q).Isometric (L'.tens Q'))
    {x y x' y' : ℝ} (hx : IsSq d N L x) (hy : IsSq d N Q y) (hx' : IsSq d N L' x') (hy' : IsSq d N Q' y')
    {r : (L'.dual.tens Q).B.ι → X.functionFieldˣ} (hr : IsRatSec (L'.dual.tens Q).B r)
    (hiso : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      i (genericPoint Z) ∈ ((L'.dual.tens Q).div hr).supp → (L.restr i).Isometric (L'.restr i)) :
    (∀ t, (slide L L' N t).ArchIntegrable (L'.dual.tens Q) (d + 1) hr) ∧
      x + y - x' - y' = 2 * ∑ t, c t * (slide L L' N t).archInt (L'.dual.tens Q) (d + 1) hr := by
  have := hX.isNoetherian
  have e' : L.icls + Q.icls = L'.icls + Q'.icls := HermLB.icls_eq_iff.2 e
  have eP : (L'.dual.tens Q).icls = -L'.icls + Q.icls := rfl
  generalize L'.dual.tens Q = P at *
  let T : Option (Fin 3) → HermLB p := fun o => o.elim P ![L, L', N]
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k X p _ hX).2 _ T).1
  choose ht hht using fun t : ℕ => (hC.arExists k X p _ hX).1 (slide L L' N t)
  have hmix (t : ℕ) := hC.arMix k X p _ hX (Fin 3) P _ Ψ hΨ ![t, -t, 1] (ht t) (hht t) r hr
  refine ⟨fun t => (hmix t).1, ?_⟩
  have sq {A : HermLB p} {x : ℝ} (hx : IsSq d N A x) (a : ℤ) (b : Fin 3 → ℤ)
      (h : a • P.icls + (b 0 • L.icls + b 1 • L'.icls + b 2 • N.icls) = A.icls) :
      x = Ψ ((((a : ℤ) : MvPolynomial (Option (Fin 3)) ℝ) * MvPolynomial.X none +
        (((b 0 : ℤ) : MvPolynomial (Option (Fin 3)) ℝ) * MvPolynomial.X (some 0) +
        ((b 1 : ℤ) : MvPolynomial (Option (Fin 3)) ℝ) * MvPolynomial.X (some 1) +
        ((b 2 : ℤ) : MvPolynomial (Option (Fin 3)) ℝ) * MvPolynomial.X (some 2))) ^ 2 * MvPolynomial.X (some 2) ^ d) := by
    refine (hx.unique hX (isSq_of_comb hC hX hΨ (a := fun o => o.elim a b) (n := fun o => o.elim 0 ![0, 0, 1])
      (HermLB.icls_eq_iff.1 ?_) (HermLB.icls_eq_iff.1 ?_))).trans ?_
    · simpa [icls_comb, Fin.sum_univ_three, T] using h
    · simp [icls_comb, Fin.sum_univ_three, T]
    · simp [lin, Fin.sum_univ_three]
  have hloc (z : X) : ∑ t, c t * (((P.div hr).mult z : ℝ) * ht t z) = 0 := by
    by_cases hz : (P.div hr).mult z = 0
    · simp [hz]
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have e₀ := HermLB.icls_eq_iff.2 (hiso Z i (CartierDiv.mem_supp_of_mult_ne_zero hz))
    have e₁ (t : ℕ) : ht t (i (genericPoint Z)) = ht 0 (i (genericPoint Z)) := by
      refine AdjFlag.height_eq hX (hht t) (hht 0) i (HermLB.icls_eq_iff.1 ?_)
      rw [HermLB.icls_pull, HermLB.icls_pull] at e₀ ⊢
      simp [icls_comb, Fin.sum_univ_three, e₀]
    simp only [e₁, ← Finset.sum_mul, hc.sum, zero_mul]
  have e₂ : ∑ t, c t * ∑ᶠ z, ((P.div hr).mult z : ℝ) * ht t z = 0 := by
    have hfin : (Function.support fun z => ((P.div hr).mult z : ℝ)).Finite :=
      (P.div hr).finite_support_mult.subset fun z hz => by simpa using hz
    simp_rw [mul_finsum]
    rw [← finsum_sum_comm _ _ fun n _ => (hfin.subset (Function.support_mul_subset_left _ _)).subset
      (Function.support_mul_subset_right _ _)]
    exact finsum_eq_zero_of_forall_eq_zero hloc
  have e₃ : Ψ (MvPolynomial.X none * ((MvPolynomial.X (some 0) - MvPolynomial.X (some 1)) *
      MvPolynomial.X (some 2) ^ d)) = -∑ t, c t * (slide L L' N t).archInt P (d + 1) hr := by
    rw [← hc.pow, Finset.mul_sum, map_sum, ← zero_sub, ← e₂, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← mul_sub, ← (hmix t).2]
    congr 4
    simp [lin, Fin.sum_univ_three]
    ring
  rw [← neg_neg (∑ t, _), ← e₃, sq hx 0 ![1, 0, 0] (by simp), sq hy 1 ![0, 1, 0] (by simp [eP]),
    sq hx' 0 ![0, 1, 0] (by simp), sq hy' 1 ![1, 0, 0] (by simp [eP, add_assoc, add_comm Q.icls, e']),
    ← map_add, ← map_sub, ← map_sub, ← map_neg, two_mul, ← map_add]
  congr 1
  simp
  ring

end Sq

end PartOne

section PartTwo

open Matrix
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem bcMat_eq {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (a : AdaptedChart S r s) (c : AlgChart p σ D) (H : h.IsCInf)
    {y : CxPts p σ} (hy : y ∈ c.e.source) (ha : y ∈ ptsIn p σ a.U) :
    bcMat h hS h₁ h₃ c y = formMat (h.bcForm a c y) := by
  rw [bcMat, Met.bcForm_eq hS a _ c H hy ha (Met.exists_adapted hS h₁ h₃ y).choose_spec]

theorem bcMat_iso {S S' : ShortComplex X.Modules} {r s : ℕ} {h : VMetric p S.X₂ (r + s)}
    {h' : VMetric p S'.X₂ (r + s)} (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁)
    (e₂ : S.X₂ ≅ S'.X₂) (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) (hI : h.IsIsometry h' e₂) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) :
    bcMat (h.met σ) hS h₁ h₃ c y = bcMat (h'.met σ) hS' h₁' h₃' c y := by
  have hg := IsoSeq.g_isoThird hS hS' e₁ e₂ he
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  rw [bcMat_eq hS h₁ h₃ a c (H σ) hy ha,
    bcMat_eq hS' h₁' h₃' (IsoSeq.mapChart e₁ e₂ _ hg a) c (H' σ) hy ha, Met.bcForm, Met.bcForm]
  refine congrArg formMat (extTrace_congr ?_)
  filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)).mem_nhds
    (ChartGlue.mem_over c.e hy ha)] with v hv
  exact (IsoSeq.gram_mapChart he hg hI σ a hv.2).symm

set_option maxHeartbeats 2000000 in

theorem bcMat_stage_of_frames {A M B L Q V : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {u : A ⟶ B}
    {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {q₂ : B ⟶ V} {w₀ : f ≫ q₀ = 0} {w₁ : g ≫ q₁ = 0} {w₂ : u ≫ q₂ = 0}
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {l : L ⟶ V} {m : V ⟶ Q} {w₃ : l ≫ m = 0}
    (hS₃ : (ShortComplex.mk l m w₃).ShortExact) {n : ℕ} (hA : IsVB A n) (hM : IsVB M (n + 1))
    (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g)
    {h : Met p σ B (n + 1 + 1)} (hfg : f ≫ g = u) (hlq : q₀ ≫ l = g ≫ q₂) (hmq : q₂ ≫ m = q₁)
    (H : h.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {U : X.Opens}
    (hyU : y ∈ ptsIn p σ U) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U)) (t₁ : Fin 1 → Γ(B, U))
    (he : IsFrame e) (ht : IsFrame fun i => q₀.app U (t i))
    (ht₁ : IsFrame fun i => q₁.app U (t₁ i)) :
    bcMat (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y +
        bcMat (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      bcMat (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y +
        bcMat (S := ShortComplex.mk l m w₃)
          (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  have hfg' (s : Γ(A, U)) : g.app U (f.app U s) = u.app U s := congr(($hfg).app U s)
  have hlq' (s : Γ(M, U)) : l.app U (q₀.app U s) = q₂.app U (g.app U s) := congr(($hlq).app U s)
  have hmq' (s : Γ(B, U)) : m.app U (q₂.app U s) = q₁.app U s := congr(($hmq).app U s)
  let a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1 := ⟨U, e, t, he, ht⟩
  let a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1 :=
    ⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩
  have ht₃ : IsFrame fun i => m.app U (q₂.app U (t₁ i)) := by simpa only [hmq'] using ht₁
  let a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1 :=
    ⟨U, fun i => q₀.app U (t i), fun i => q₂.app U (t₁ i), ht, ht₃⟩
  let t₂ : Fin (1 + 1) → Γ(B, U) :=
    Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm
  have ht₂e (j : Fin 1 ⊕ Fin 1) : q₂.app U (t₂ (finSumFinEquiv j)) = a₃.frame j := by
    rcases j with j | j
    · simp [t₂, a₃, AdaptedChart.frame, hlq']
    · simp [t₂, a₃, AdaptedChart.frame]
  have ht₂ : IsFrame fun i => q₂.app U (t₂ i) := by
    have e₀ : (fun i => q₂.app U (t₂ i)) = (a₃.mid hS₃).e := by
      funext i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      rw [ht₂e]
      simp [AdaptedChart.mid]
    rw [e₀]
    exact (a₃.mid hS₃).isFrame
  let a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1) := ⟨U, e, t₂, he, ht₂⟩
  let T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U) :=
    Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)
  have hT₀ (x : Fin n ⊕ Fin 1) : g.app U (a₀.frame x) = T (Sum.map id Sum.inl x) := by
    rcases x with i | i
    · simp [a₀, T, AdaptedChart.frame, hfg']
    · simp [a₀, T, AdaptedChart.frame]
  have hT₁ (x : (Fin n ⊕ Fin 1) ⊕ Fin 1) :
      a₁.frame (Sum.map finSumFinEquiv id x) = T (Equiv.sumAssoc _ _ _ x) := by
    rcases x with (i | i) | i
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid, hfg']
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid]
    · simp [a₁, T, AdaptedChart.frame]
  have hT₂ (x : Fin n ⊕ (Fin 1 ⊕ Fin 1)) :
      a₂.frame (Sum.map id finSumFinEquiv x) = T x := by
    rcases x with i | i | i
    · simp [a₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]

  let K : CxPts p σ → Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) ℂ := h.gram T
  have g₀ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (h.restrict hg hM).gram a₀.frame z =
        (K z).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := by
    ext i j
    refine ((h.form_restrict hg hM _ _ hz).trans ?_)
    rw [hT₀, hT₀]
    rfl
  have g₁ {z : CxPts p σ} : (K z).submatrix (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) =
      (h.gram a₁.frame z).submatrix (Sum.map finSumFinEquiv (Equiv.refl (Fin 1)))
        (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₁.frame _) (a₁.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₁ i).symm (hT₁ j).symm
  have g₂ {z : CxPts p σ} : K z =
      (h.gram a₂.frame z).submatrix (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv)
        (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₂.frame _) (a₂.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₂ i).symm (hT₂ j).symm
  have g₃ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram a₃.frame z =
        quotGram (K z) := by
    have e₀ := (QuotStage.quotStages (Fin n) (Fin (1 + 1)) Unit).2 (Fin n) (Fin 1 ⊕ Fin 1)
      (Equiv.refl _) finSumFinEquiv (h.gram a₂.frame z)
    ext i j
    rw [g₂, e₀, submatrix_apply, ← Met.quot_G h hS₂ hA hV a₂ hz,
      ← Met.form_frame _ a₂.quot hz]
    exact congrArg₂ (fun s s' => (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1)
      h hS₂ hA hV).form s s' z) (ht₂e i).symm (ht₂e j).symm
  have hW : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ U :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds
      (ChartGlue.mem_over c.e hy hyU)) fun _ hv => hv.2
  have d₀ : bcMat (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y =
      formMat (extTrace (fun v => (K (c.e.symm v)).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl)) (c.e y)) := by
    rw [bcMat_eq hS₀ hA hL a₀ c (H.restrict hg hM) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₀ hv)]
  have d₁ : bcMat (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      formMat (extTrace (fun v => (K (c.e.symm v)).submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _)) (c.e y)) := by
    rw [bcMat_eq hS₁ hM hQ a₁ c H hy hyU, Met.bcForm]
    simp only [g₁]
    rw [extTrace_submatrix_sumMap]
  have d₂ : bcMat (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y =
      formMat (extTrace (fun v => K (c.e.symm v)) (c.e y)) := by
    rw [bcMat_eq hS₂ hA hV a₂ c H hy hyU, Met.bcForm]
    simp only [g₂]
    rw [extTrace_submatrix_sumMap]
  have d₃ : bcMat (S := ShortComplex.mk l m w₃)
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y =
      formMat (extTrace (fun v => quotGram (K (c.e.symm v))) (c.e y)) := by
    rw [bcMat_eq hS₃ hL hQ a₃ c (Met.IsCInf.quot hS₂ hA hV H) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₃ hv)]
  have hK : MContDiffAt 1 (fun v => K (c.e.symm v)) (c.e y) :=
    ((H.gram T hyU).mContDiffAt c hy).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 (c.e y), (K (c.e.symm v)).PosDef := hW.mono fun v hv => by
    rw [g₂]
    exact (Met.posDef_gram_frame (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ a₂ hv).submatrix
      ((Equiv.refl (Fin n)).injective.sumMap finSumFinEquiv.injective)
  rw [d₀, d₁, d₂, d₃]
  ext i j
  simp only [formMat, Matrix.add_apply, of_apply, ← add_div]
  rw [extTrace_add_extTrace (ReciprocityTheory.L2DbarEstimates.V D) (Fin n) (Fin 1) (Fin 1) (fun v => K (c.e.symm v))
      (c.e y) _ _ hK hp]

theorem bcMat_stage {A M B L Q V : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {u : A ⟶ B}
    {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {q₂ : B ⟶ V} {w₀ : f ≫ q₀ = 0} {w₁ : g ≫ q₁ = 0} {w₂ : u ≫ q₂ = 0}
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {l : L ⟶ V} {m : V ⟶ Q} {w₃ : l ≫ m = 0}
    (hS₃ : (ShortComplex.mk l m w₃).ShortExact) {n : ℕ} (hA : IsVB A n) (hM : IsVB M (n + 1))
    (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g)
    {h : Met p σ B (n + 1 + 1)} (hfg : f ≫ g = u) (hlq : q₀ ≫ l = g ≫ q₂) (hmq : q₂ ≫ m = q₁)
    (H : h.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    bcMat (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y +
        bcMat (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      bcMat (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y +
        bcMat (S := ShortComplex.mk l m w₃)
          (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  obtain ⟨b₀, hb₀⟩ := Met.exists_adapted (p := p) (σ := σ) hS₀ hA hL y
  obtain ⟨b₁, hb₁⟩ := Met.exists_adapted hS₁ hM hQ y
  refine bcMat_stage_of_frames hS₀ hS₁ hS₂ hS₃ hA hM hL hQ hV hg hfg hlq hmq H c hy
    (U := b₀.U ⊓ b₁.U) (mem_ptsIn_inf.2 ⟨hb₀, hb₁⟩) (fun i => resM A inf_le_left (b₀.e i))
    (fun i => resM M inf_le_left (b₀.t i)) (fun i => resM B inf_le_right (b₁.t i))
    (b₀.he.res inf_le_left) ?_ ?_
  · simp only [app_resM]
    exact b₀.ht.res inf_le_left
  · simp only [app_resM]
    exact b₁.ht.res inf_le_right

end PartTwo

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

def bcI (N : HermLB p) (d : ℕ) {S : ShortComplex X.Modules} {r s : ℕ} (h : VMetric p S.X₂ (r + s)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) : ℝ :=
  ∑ᶠ σ, total fun (c : AlgChart p σ (d + 1)) y => mix d (chernMat (N.φ σ) c y) (bcMat (h.met σ) hS h₁ h₃ c y)

theorem isDens_bc {B : LB X} {φ : Weight p σ B} (hφ : φ.IsCInf) {S : ShortComplex X.Modules} {r s : ℕ}
    {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (H : h.IsCInf) :
    IsDens fun (c : AlgChart p σ (d + 1)) y => mix d (chernMat φ c y) (bcMat h hS h₁ h₃ c y) :=
  (chernMat_isForm k X p σ _ B φ hφ).isDens_mix (T.bott_chern_matrix_is_form k X p σ _ S r s h hS h₁ h₃ H)

theorem iso_seq (N : HermLB p) (d : ℕ) (S S' : ShortComplex X.Modules) {r s : ℕ} {h : VMetric p S.X₂ (r + s)}
    (h' : VMetric p S'.X₂ (r + s)) (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁)
    (e₂ : S.X₂ ≅ S'.X₂) (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) (hI : h.IsIsometry h' e₂) :
    (VMetric.det (H.quot hS h₁ h₃)).Isometric (VMetric.det (H'.quot hS' h₁' h₃')) ∧
      bcI N d h hS h₁ h₃ = bcI N d h' hS' h₁' h₃' :=
  ⟨(T.det_metric_shortExact_iso_isometric k X p S S' r s h h' H H' hS hS' h₁ h₃ h₁' h₃' e₁ e₂ he hI).1,
    finsum_congr fun _ => total_congr fun c _ hy => by
      rw [bcMat_iso H H' hS hS' h₁ h₃ h₁' h₃' e₁ e₂ he hI c hy]⟩

variable {N : HermLB p}

theorem sum_chernDens_slide {c : Fin (d + 2) → ℝ} (hc : IsWeights d ((d + 1 : ℝ)⁻¹) c) (L L' N : HermLB p)
    (a : AlgChart p σ (d + 1)) {y : CxPts p σ} (hy : y ∈ a.e.source) :
    mix d (chernMat (N.φ σ) a y) (chernMat (L.φ σ) a y) - mix d (chernMat (N.φ σ) a y) (chernMat (L'.φ σ) a y) =
      ∑ t, c t * a.chernDens ((slide L L' N t).φ σ) y := by
  rw [← mix_sub, ← hc.det]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : chernMat ((slide L L' N t).φ σ) a y =
      chernMat (N.φ σ) a y + ((t : ℕ) : ℂ) • (chernMat (L.φ σ) a y - chernMat (L'.φ σ) a y) := by
    rw [chernMat_comb k X p σ _ _ _ _ a y hy, Fin.sum_univ_three, smul_sub]
    simp
    abel
  rw [← e]
  rfl

section RankTwo

variable {V L Q L' Q' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0}
  {l' : L' ⟶ V} {m' : V ⟶ Q'} {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
  (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1)
  (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')

variable [IsIntegral X] {h : VMetric p V (1 + 1)} (H : h.IsCInf)

theorem rank_two (hC : Published.ArCalc) (hA : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1)) {x y x' y' : ℝ}
    (hx : IsSq d N (VMetric.det (H.restrict hl hL)) x)
    (hy : IsSq d N (VMetric.det (VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H)) y)
    (hx' : IsSq d N (VMetric.det (H.restrict hl' hL')) x')
    (hy' : IsSq d N (VMetric.det (VMetric.IsCInf.quot (S := .mk l' m' w') hS' hL' hQ' H)) y') :
    x + y - bcI N d (S := .mk l m w) h hS hL hQ = x' + y' - bcI N d (S := .mk l' m' w') h hS' hL' hQ' := by
  by_cases hs : l' ≫ m = 0
  · obtain ⟨e, he⟩ := T.iso_of_equal_sublines_shortExact X V L Q L' Q' l m w l' m' w' hS hS' hQ hQ' hs
    obtain ⟨e₁, e₂⟩ := iso_seq N d (.mk l' m' w') (.mk l m w) h H H hS' hS hL' hQ' hL hQ
      e (Iso.refl V) (he.trans (Category.comp_id _).symm) fun _ _ _ _ _ _ => rfl
    have e₃ := T.det_metric_isometric_of_isometry k X p L' L 1 (h.restrict hl' hL') (h.restrict hl hL) (H.restrict hl' hL')
      (H.restrict hl hL) e (AdjFlag.isIsometry_restrict _ _ _ _ e he)
    rw [e₂, hx.unique hA (hx'.congr hC hA e₃), hy.unique hA (hy'.congr hC hA e₁)]
  have := hA.isLocallyNoetherian
  have HQ := VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H
  obtain ⟨r, hr, hv, hn⟩ := T.exists_ratSec_det_dual_tensor_support k X p L' Q (h.restrict hl' hL')
    (VMetric.quot (S := .mk l m w) h hS hL hQ) (H.restrict hl' hL') HQ (l' ≫ m) hs
  obtain ⟨c, hc⟩ := exists_isWeights d ((d + 1 : ℝ)⁻¹)
  obtain ⟨i₀, e₀⟩ := isSq_sub hC hA hc
    ((T.det_metric_shortExact_isometric k X p (.mk l m w) 1 1 h H hS hL hQ hl).trans
      (T.det_metric_shortExact_isometric k X p (.mk l' m' w') 1 1 h H hS' hL' hQ' hl').symm) hx hy hx' hy' hr
    fun Z i _ _ hz => T.det_metric_restriction_vanishing_locus k X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z i (hv _ hz)
  generalize (VMetric.det (H.restrict hl' hL')).dual.tens (VMetric.det HQ) = P at *
  have key (σ : k →+* ℂ) : 2 * ∑ t, c t * ((slide (VMetric.det (H.restrict hl hL)) (VMetric.det (H.restrict hl' hL'))
      N t).φ σ).chernInt (d + 1) (offSupp p σ (P.div hr)) (logNorm (P.φ σ) r) =
      total (fun (c : AlgChart p σ (d + 1)) y =>
        mix d (chernMat (N.φ σ) c y) (bcMat (S := .mk l m w) (h.met σ) hS hL hQ c y)) -
      total (fun (c : AlgChart p σ (d + 1)) y =>
        mix d (chernMat (N.φ σ) c y) (bcMat (S := .mk l' m' w') (h.met σ) hS' hL' hQ' c y)) := by
    have := hA.compactSpace σ
    have := CxPts.secondCountableTopology_of_isProjOver σ hA.isProjOver
    have := CxPts.t2Space_cxPts_of_isProjOver σ hA.isProjOver
    obtain ⟨v, hv, hv₁, hb⟩ := T.exists_continuous_cosSq_angle_function k X p σ V L L' _ (h.met σ) l l' (H σ) hl hl' hL hL'
    have d₁ := isDens_bc (d := d) (N.cInf σ) (S := .mk l m w) hS hL hQ (H σ)
    have d₂ := isDens_bc (d := d) (N.cInf σ) (S := .mk l' m' w') hS' hL' hQ' (H σ)
    rw [← (total_add_sub (hG σ) d₁ d₂).2]
    simp only [Weight.chernInt, (chernPart_eq _).1, (chernPart_eq _).2]
    have j₀ (t) := i₀ t σ
    simp only [Weight.ChernIntegrableOn, (chernPart_eq _).1, (chernPart_eq _).2] at j₀
    refine green_sum (hG σ) c (fun t => isDens_chernDens (HermLB.cInf _ σ))
      (fun a y hy => sum_chernDens_slide hc (VMetric.det (H.restrict hl hL))
        (VMetric.det (H.restrict hl' hL')) N a hy) (d₁.sub d₂) hv₁ (fun y => (hb y).1) (isOpen_offSupp _)
      (fun ρ => ?_) (fun y hy => ?_) (fun t => (j₀ t).1) (fun t => (j₀ t).2)
      (T.short_exact_vector_bundles_height_compare k X p σ d (hG σ) V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' (h.met σ) (H σ) _ (N.φ σ)
        (N.cInf σ) v hv)
    · rw [← MixDensNull.part_over_closed k X p _ hA _ (P.div hr).supp.isClosed (P.div hr).genericPoint_notMem_supp σ ρ]
      congr 1
      ext y
      exact mem_offSupp.not.trans not_not
    · obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
      obtain ⟨n₁, n₂⟩ := hn σ y hy U t' ht' hU
      have e := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hv ht ht' hU
      have := div_pos n₁ (AdjFlag.form_frame_pos ((h.met σ).restrict hl' hL') ht' hU)
      replace this := this.trans_eq e
      exact ⟨by linarith, n₂.trans (congrArg (Real.log · / 2) e)⟩
  have := hA.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have e₂ := Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => key σ
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_sub_distrib] at e₂
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype, Finset.mul_sum Finset.univ _ (c _)] at e₀
  rw [bcI, bcI, finsum_eq_sum_of_fintype (α := k →+* ℂ), finsum_eq_sum_of_fintype (α := k →+* ℂ)]
  linarith

end RankTwo

theorem isSq_congr [IsIntegral X] {E : X.Modules} {r : ℕ} {h h' : VMetric p E r} (e : h = h')
    {H : h.IsCInf} {H' : h'.IsCInf} {x : ℝ} (hx : IsSq d N (VMetric.det H') x) : IsSq d N (VMetric.det H) x := by
  subst e
  exact hx

section ThreeStep

variable [IsIntegral X] {A B V : X.Modules} {u : A ⟶ B} {q₂ : B ⟶ V} {w₂ : u ≫ q₂ = 0}
  (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {n : ℕ} (hA : IsVB A n) (hV : IsVB V (1 + 1))
  {h : VMetric p B (n + 1 + 1)} (H : h.IsCInf)
  {M L Q : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {w₀ : f ≫ q₀ = 0}
  {w₁ : g ≫ q₁ = 0} (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact)
  (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hM : IsVB M (n + 1)) (hL : IsVB L 1)
  (hQ : IsVB Q 1) (hg : IsSubbundle g)

omit [IsIntegral X] in
include H in

theorem three_step (hX : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1)) (hu : f ≫ g = u) :
    ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact)
      (hl : IsSubbundle l),
      (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL =
        VMetric.quot (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧
      VMetric.quot (S := .mk l m w₃)
          (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ =
        VMetric.quot (S := .mk g q₁ w₁) h hS₁ hM hQ ∧
      bcI N d (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL +
          bcI N d (S := .mk g q₁ w₁) h hS₁ hM hQ =
        bcI N d (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV +
          bcI N d (S := .mk l m w₃)
            (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ := by
  obtain ⟨l, m, w₃, hS₃, e₁, e₂⟩ := T.exists_shortExact_of_composition X A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hu
  have hl : IsSubbundle l := isSubbundle_of_shortExact hS₃ hQ
  have key (σ : k →+* ℂ) := T.shortExact_composition_compatibility k X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m
    w₃ hS₃ n hA hM hL hQ hV hg (h.met σ) hu e₁ e₂ hl
  refine ⟨l, m, w₃, hS₃, hl, VMetric.ext (funext fun σ => (key σ).1),
    VMetric.ext (funext fun σ => (key σ).2), ?_⟩
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [bcI, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  have H₀ := (H σ).restrict hg hM
  have H₃ := Met.IsCInf.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ)
  have s₁ := (total_add_sub (hG σ) (isDens_bc (N.cInf σ) (S := .mk f q₀ w₀) hS₀ hA hL H₀)
    (isDens_bc (N.cInf σ) (S := .mk g q₁ w₁) hS₁ hM hQ (H σ))).1
  have s₂ := (total_add_sub (hG σ)
    (isDens_bc (N.cInf σ) (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ))
    (isDens_bc (N.cInf σ) (S := .mk l m w₃) hS₃ hL hQ H₃)).1
  refine s₁.symm.trans ((total_congr fun c y hy => ?_).trans s₂)
  exact mix_add.symm.trans ((congrArg _
    (bcMat_stage hS₀ hS₁ hS₂ hS₃ hA hM hL hQ hV hg hu e₁ e₂ (H σ) c hy)).trans mix_add)

variable {M' L' Q' : X.Modules} {f' : A ⟶ M'} {g' : M' ⟶ B} {q₀' : M' ⟶ L'} {q₁' : B ⟶ Q'}
  {w₀' : f' ≫ q₀' = 0} {w₁' : g' ≫ q₁' = 0} (hS₀' : (ShortComplex.mk f' q₀' w₀').ShortExact)
  (hS₁' : (ShortComplex.mk g' q₁' w₁').ShortExact) (hM' : IsVB M' (n + 1)) (hL' : IsVB L' 1)
  (hQ' : IsVB Q' 1) (hg' : IsSubbundle g')

theorem two_steps (hC : Published.ArCalc) (hX : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1))
    (hu : f ≫ g = f' ≫ g') {x y x' y' : ℝ}
    (hx : IsSq d N (VMetric.det (VMetric.IsCInf.quot (S := .mk f q₀ w₀) hS₀ hA hL (H.restrict hg hM))) x)
    (hy : IsSq d N (VMetric.det (VMetric.IsCInf.quot (S := .mk g q₁ w₁) hS₁ hM hQ H)) y)
    (hx' : IsSq d N (VMetric.det (VMetric.IsCInf.quot (S := .mk f' q₀' w₀') hS₀' hA hL' (H.restrict hg' hM'))) x')
    (hy' : IsSq d N (VMetric.det (VMetric.IsCInf.quot (S := .mk g' q₁' w₁') hS₁' hM' hQ' H)) y') :
    x + y - (bcI N d (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL +
        bcI N d (S := .mk g q₁ w₁) h hS₁ hM hQ) =
      x' + y' - (bcI N d (S := .mk f' q₀' w₀') (h.restrict hg' hM') hS₀' hA hL' +
        bcI N d (S := .mk g' q₁' w₁') h hS₁' hM' hQ') := by
  have m₀ : Mono f := hS₀.mono_f
  have m₁ : Mono g := hS₁.mono_f
  have hS₂ : (ShortComplex.mk (f ≫ g) _ (Limits.cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hV : IsVB (Limits.cokernel (f ≫ g)) (1 + 1) := by
    obtain ⟨l, m, w₃, hS₃, -⟩ := T.exists_shortExact_of_composition X A M B L Q _ f g _ q₀ q₁ _ w₀ w₁ _ hS₀ hS₁ hS₂ rfl
    exact (VBExt.isVB_and_cls_det_of_shortExact X _ 1 1 hS₃ hL hQ).1
  obtain ⟨l, m, w₃, hS₃, hl, e₁, e₂, e₃⟩ := three_step (N := N) hS₂ hA hV H hS₀ hS₁ hM hL hQ hg hX hG rfl
  obtain ⟨l', m', w₃', hS₃', hl', e₁', e₂', e₃'⟩ :=
    three_step (N := N) hS₂ hA hV H hS₀' hS₁' hM' hL' hQ' hg' hX hG hu.symm
  have HV := VMetric.IsCInf.quot (S := .mk (f ≫ g) _ (Limits.cokernel.condition _)) (r := n)
    (s := 1 + 1) hS₂ hA hV H
  have aux {a a' b c c' d d' : ℝ} (e : d = b + c) (e' : d' = b + c') (k : a - c = a' - c') :
      a - d = a' - d' := by linarith
  exact aux e₃ e₃' (rank_two hS₃ hS₃' hL hQ hL' hQ' hl hl' HV hC hX hG (isSq_congr e₁ hx)
    (isSq_congr e₂ hy) (isSq_congr e₁' hx') (isSq_congr e₂' hy'))

end ThreeStep

section Flags

open VMetric

variable {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) {fl fl' : Vert.Flag E r}

abbrev stepBc (N : HermLB p) (d : ℕ) (h : VMetric p E r) (fl : Vert.Flag E r) (i : Fin r) : ℝ :=
  bcI N d (h.stepMet fl i) (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)

include H in

theorem bcPair_eq_sum (hX : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1)) (fl : Vert.Flag E r) :
    bcPair h fl N d = ∑ i, stepBc N d h fl i := by
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [bcPair, stepBc, bcI, finsum_eq_sum_of_fintype]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  refine (total_congr fun c y _ => ?_).trans (total_sum (hG σ) fun i =>
    isDens_bc (N.cInf σ) (h := (h.stepMet fl i).met σ) _ _ _ (H.restrict _ _ σ))
  rw [flagDens, flagMat, mix_sum]

theorem step_eq {i : Fin r} (h₀ : fl.SameStep fl' i.castSucc) (h₁ : fl.SameStep fl' i.succ) :
    (grLB fl i H).Isometric (grLB fl' i H) ∧ stepBc N d h fl i = stepBc N d h fl' i := by
  obtain ⟨e₀, h₀⟩ := h₀
  obtain ⟨e₁, h₁⟩ := h₁
  refine iso_seq N d (stepSeq fl i) (stepSeq fl' i) (h := h.stepMet fl i) (h.stepMet fl' i)
    (H.restrict _ _) (H.restrict _ _) _ _ _ _ _ _ e₀ e₁ ?_ (AdjFlag.isIsometry_restrict _ _ _ _ e₁ h₁)
  rw [← cancel_mono (fl'.ι i.succ)]
  simp only [Category.assoc, Vert.Flag.step_ι, h₀, h₁]

theorem mid_eq [IsIntegral X] (hC : Published.ArCalc) (hX : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1)) {n : ℕ}
    (hn : n + 1 < r) (h₀ : fl.SameStep fl' (Fin.castSucc ⟨n, by omega⟩))
    (h₂ : fl.SameStep fl' (Fin.succ ⟨n + 1, hn⟩)) {x y x' y' : ℝ} (hx : IsSq d N (grLB fl ⟨n, by omega⟩ H) x)
    (hy : IsSq d N (grLB fl ⟨n + 1, hn⟩ H) y) (hx' : IsSq d N (grLB fl' ⟨n, by omega⟩ H) x')
    (hy' : IsSq d N (grLB fl' ⟨n + 1, hn⟩ H) y') :
    x + y - (stepBc N d h fl ⟨n, by omega⟩ + stepBc N d h fl ⟨n + 1, hn⟩) =
      x' + y' - (stepBc N d h fl' ⟨n, by omega⟩ + stepBc N d h fl' ⟨n + 1, hn⟩) := by
  set i₀ : Fin r := ⟨n, by omega⟩
  set i₁ : Fin r := ⟨n + 1, hn⟩
  obtain ⟨e₀, h₀⟩ := h₀
  obtain ⟨e₂, h₂⟩ := h₂
  let g : fl.F i₀.succ ⟶ fl.F i₁.succ := fl.step i₁
  let f' : fl.F i₀.castSucc ⟶ fl'.F i₀.succ := e₀.hom ≫ fl'.step i₀
  let g' : fl'.F i₀.succ ⟶ fl.F i₁.succ := fl'.step i₁ ≫ e₂.inv
  let q' : fl.F i₁.succ ⟶ fl'.gr i₁ := e₂.hom ≫ fl'.π i₁
  have w₀' : f' ≫ fl'.π i₀ = 0 := by
    simp only [f', Category.assoc]
    rw [show fl'.step i₀ ≫ fl'.π i₀ = 0 from Limits.cokernel.condition _, Limits.comp_zero]
  have w₁' : g' ≫ q' = 0 := by
    simp only [g', q', Category.assoc, Iso.inv_hom_id_assoc]
    exact Limits.cokernel.condition _
  have hS₀' : (ShortComplex.mk f' _ w₀').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl' i₀) e₀.symm (Iso.refl _) (Iso.refl _)
      (by simp [f']) (by simp)) (stepSeq_shortExact fl' i₀)
  have hS₁' : (ShortComplex.mk g' q' w₁').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl' i₁)
      (Iso.refl _) e₂.symm (Iso.refl _)
      (by simp [g']) (by simp [q'])) (stepSeq_shortExact fl' i₁)
  have hg : IsSubbundle g := isSubbundle_of_shortExact (stepSeq_shortExact fl i₁) (fl.isVB_gr i₁)
  have hg' : IsSubbundle g' := isSubbundle_of_shortExact hS₁' (fl'.isVB_gr i₁)
  have gι : g ≫ fl.ι i₁.succ = fl.ι i₀.succ := fl.step_ι i₁
  have gι' : g' ≫ fl.ι i₁.succ = fl'.ι i₀.succ := by
    rw [← h₂, Category.assoc, Iso.inv_hom_id_assoc]
    exact fl'.step_ι i₁
  have hu : fl.step i₀ ≫ g = f' ≫ g' := by
    rw [← cancel_mono (fl.ι i₁.succ), Category.assoc, Category.assoc, gι, gι', fl.step_ι,
      Category.assoc, fl'.step_ι, h₀]
  have HB : (h.stepMet fl i₁).IsCInf := H.restrict _ _
  have res {F : X.Modules} {a : F ⟶ fl.F i₁.succ} {b : F ⟶ E} (ha : IsSubbundle a)
      (hb : IsSubbundle b) (hF : IsVB F (n + 1)) (e : a ≫ fl.ι i₁.succ = b) :
      ((h.stepMet fl i₁).restrict ha hF).IsIsometry (h.restrict hb hF) (Iso.refl F) :=
    fun σ U s t y hy => by
      refine ((h.met σ).form_restrict hb hF _ _ hy).trans (Eq.trans ?_
        ((((h.stepMet fl i₁).met σ).form_restrict ha hF s t hy).trans
          ((h.met σ).form_restrict (fl.isSubbundle i₁.succ) (fl.isVB i₁.succ) _ _ hy)).symm)
      rw [← e]
      rfl
  obtain ⟨a₁, b₁⟩ := iso_seq N d (stepSeq fl i₀) (stepSeq fl i₀) (h.stepMet fl i₀)
    (HB.restrict hg (fl.isVB i₀.succ)) (H.restrict _ _) (stepSeq_shortExact fl i₀)
    (stepSeq_shortExact fl i₀) (fl.isVB i₀.castSucc) (fl.isVB_gr i₀) (fl.isVB i₀.castSucc)
    (fl.isVB_gr i₀) (Iso.refl _) (Iso.refl _) (by simp) (res hg _ _ gι)
  obtain ⟨a₂, b₂⟩ := iso_seq N d (.mk f' _ w₀') (stepSeq fl' i₀) (h.stepMet fl' i₀)
    (HB.restrict hg' (fl'.isVB i₀.succ)) (H.restrict _ _) hS₀'
    (stepSeq_shortExact fl' i₀) (fl.isVB i₀.castSucc) (fl'.isVB_gr i₀) (fl'.isVB i₀.castSucc)
    (fl'.isVB_gr i₀) e₀ (Iso.refl _) (Category.comp_id _).symm (res hg' _ _ gι')
  obtain ⟨a₃, b₃⟩ := iso_seq N d (.mk g' q' w₁') (stepSeq fl' i₁) (h.stepMet fl' i₁)
    HB (H.restrict _ _) hS₁' (stepSeq_shortExact fl' i₁) (fl'.isVB i₀.succ) (fl'.isVB_gr i₁)
    (fl'.isVB i₁.castSucc) (fl'.isVB_gr i₁) (Iso.refl _) e₂ (by simp [g'])
    (AdjFlag.isIsometry_restrict _ _ _ _ e₂ h₂)
  have key := two_steps (fl.isVB i₀.castSucc) HB (stepSeq_shortExact fl i₀)
    (stepSeq_shortExact fl i₁) (fl.isVB i₀.succ) (fl.isVB_gr i₀) (fl.isVB_gr i₁) hg hS₀' hS₁'
    (fl'.isVB i₀.succ) (fl'.isVB_gr i₀) (fl'.isVB_gr i₁) hg' hC hX hG hu
    (hx.congr hC hX a₁.symm) hy (hx'.congr hC hX a₂.symm) (hy'.congr hC hX a₃.symm)
  exact (congrArg (fun t => x + y - (t + stepBc N d h fl i₁)) b₁).symm.trans
    (key.trans (congrArg₂ (fun s t => x' + y' - (s + t)) b₂ b₃))

theorem sum_eq [IsIntegral X] (hC : Published.ArCalc) (hX : IsArithVar p (d + 1)) (hG : GenSmooth p (d + 1))
    (ha : fl.Adjacent fl') {x x' : Fin r → ℝ} (hx : ∀ i, IsSq d N (grLB fl i H) (x i))
    (hx' : ∀ i, IsSq d N (grLB fl' i H) (x' i)) : ∑ i, x i - ∑ i, x' i = bcPair h fl N d - bcPair h fl' N d := by
  obtain ⟨j, hj⟩ := ha
  have same {i : Fin r} (h₀ : fl.SameStep fl' i.castSucc) (h₁ : fl.SameStep fl' i.succ) :
      x i - stepBc N d h fl i - (x' i - stepBc N d h fl' i) = 0 := by
    obtain ⟨e₁, e₂⟩ := step_eq (N := N) (d := d) H h₀ h₁
    rw [e₂, ((hx i).congr hC hX e₁).unique hX (hx' i), sub_self]
  suffices e : ∑ i, (x i - stepBc N d h fl i - (x' i - stepBc N d h fl' i)) = 0 by
    simp only [Finset.sum_sub_distrib] at e
    rw [bcPair_eq_sum H hX hG, bcPair_eq_sum H hX hG]
    linarith
  by_cases he : j = 0 ∨ j = Fin.last r
  · have all (i) : fl.SameStep fl' i := by
      by_cases hi : i = j
      · exact hi ▸ AdjFlag.sameStep_of_end he
      · exact hj i hi
    exact Finset.sum_eq_zero fun i _ => same (all _) (all _)
  obtain ⟨_ | n, hn⟩ := j
  · exact absurd (.inl rfl) he
  have hn' : n + 1 < r := by
    have : n + 1 ≠ r := fun e => he (.inr (Fin.ext e))
    omega
  rw [Fintype.sum_eq_add (⟨n, by omega⟩ : Fin r) (⟨n + 1, hn'⟩ : Fin r) (by simp) fun i hi => same (i := i)
    (hj _ fun e => hi.2 (Fin.ext (congrArg Fin.val e :)))
    (hj _ fun e => hi.1 (Fin.ext (Nat.succ_injective (congrArg Fin.val e :))))]
  have := mid_eq H hC hX hG hn' (hj _ (by simp [Fin.ext_iff])) (hj _ (by simp [Fin.ext_iff]))
    (hx _) (hx _) (hx' _) (hx' _)
  linarith

end Flags

theorem compare_of_adjacent : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (d : ℕ), IsArithVar p (d + 1) → GenSmooth p (d + 1) → ∀ (E : X.Modules) (r : ℕ)
    (h : VMetric p E r) (H : h.IsCInf) (fl fl' : Vert.Flag E r), fl.Adjacent fl' → Compare H d fl fl' := by
  intro hC k _ X p _ d hX hG E r h H fl fl' ha κ _ L Φ hΦ x x' hx hx' n
  classical
  have sq (j : κ) : IsSq d (comb L n) (L j) (Φ (MvPolynomial.X j ^ 2 * lin (fun j => (n j : ℝ)) ^ d)) := by
    convert isSq_of_comb hC hX hΦ (isometric_comb_single L j) (.refl (comb L n)) using 4
    simp [lin, Pi.single_apply, apply_ite]
  rw [← sum_eq H hC hX hG ha (fun i => (sq _).congr hC hX (hx i)) fun i => (sq _).congr hC hX (hx' i), sub_mul,
    map_sub, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum]

end GlobalTheory.AdjMix
