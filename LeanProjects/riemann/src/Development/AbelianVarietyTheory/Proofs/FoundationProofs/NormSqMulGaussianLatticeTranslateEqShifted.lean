import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValuesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordsAlongOrthonormalRealSubfieldBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalBasisLatticeIndexCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorPowFractionalIdealNonarchSizeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeterminantIdealHermitianLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOneStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.Vacuum

theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (k : ℤ) (hk : gl3FieldFirst Λ ω (2 * t) = k) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z = (-1 : ℂ) ^ k * U1 Λ t (U1 Λ ω G) z := by
  have h1 : (-1 : ℂ) ^ k = Complex.exp (-(Real.pi * Complex.I) * k) := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have h2 : (k : ℂ) * Complex.I = (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have : (k : ℂ) = ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) := by rw [hk]; simp
    rw [this, gl3FieldFirst]
    have h3 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    have h4 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp [map_ofNat]; ring
    rw [h4]
    simp only [map_mul, Complex.conj_conj] at h3
    rw [mul_comm t, h3]; push_cast; ring
  simp only [U1]
  rw [h1, show z + t + ω = z + ω + t by ring]
  have aux : ∀ a x y u v w : ℂ, x + y = u + v + w →
      a * Complex.exp x * Complex.exp y = Complex.exp u * (a * Complex.exp v * Complex.exp w) := by
    intro a x y u v w h
    rw [mul_assoc, ← Complex.exp_add, h, Complex.exp_add, Complex.exp_add]; ring
  apply aux
  have h5 : -((Real.pi : ℂ) * Complex.I) * k = -(Real.pi : ℂ) * (k * Complex.I) := by ring
  rw [h5, h2]; ring

theorem translate_operator_smul (Λ : AddSubgroup ℂ) (ω c : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (fun z => c * G z) z = c * U1 Λ ω G z := by
  simp only [U1]; ring

theorem evenTheta_properties_curveLattice (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) :
    Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ GL3Theta.th0 (lamOf D cc δ) t0 0 = 1 ∧
      ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = m ∧
        ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z =
          GL3Theta.th0 (lamOf D cc δ) t0 z := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hlat := Parity.lamOf_eq_closure D cc δ hC
  obtain ⟨⟨hd, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws _ hlat
  obtain ⟨hn, hp⟩ := Parity.even_im_hermitian_sub D hG cc δ hC t0 ht
  set Λ := lamOf D cc δ
  have h0 : U1 Λ t0 (sgStar Λ) 0 ≠ 0 := by
    simp only [U1, zero_add]
    exact mul_ne_zero (fun h => hn ((hz _).1 h)) (Complex.exp_ne_zero _)
  refine ⟨?_, div_self h0, fun ω hω => ?_⟩
  · unfold GL3Theta.th0
    refine Differentiable.div_const ?_ _
    unfold U1
    fun_prop
  · obtain ⟨m, k, hm, hk, hmk⟩ := hp ω hω
    refine ⟨m, hm, fun z => ?_⟩
    have e1 : GL3Theta.th0 Λ t0 = fun z => (U1 Λ t0 (sgStar Λ) 0)⁻¹ * U1 Λ t0 (sgStar Λ) z := by
      funext z; simp only [GL3Theta.th0]; ring
    have e2 : U1 Λ ω (sgStar Λ) = fun z => (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
      funext (hU ω hω)
    rw [e1, translate_operator_smul, exists_orthonormal_basis_family Λ ω t0 _ k hk, e2, translate_operator_smul]
    have e3 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ k * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hmk.2 h).neg_one_zpow]; norm_num
      · rw [(Int.not_even_iff_odd.1 (fun h' => h (hmk.1 h'))).neg_one_zpow]; norm_num
    linear_combination ((U1 Λ t0 (sgStar Λ) 0)⁻¹ * U1 Λ t0 (sgStar Λ) z) * e3

theorem norm_sq_mul_gaussian_latticeTranslate_eq_shifted (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    ‖U1 Λ ω G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) =
      ‖G (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  simp only [U1]
  rw [norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h1 : -(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
      (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)) =
      ((-Real.pi / area Λ : ℝ) : ℂ) * (z * (starRingEnd ℂ) ω + ω * (starRingEnd ℂ) ω / 2) := by
    push_cast; ring
  rw [h1, Complex.re_ofReal_mul, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

theorem normSq_pullB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (g : ℂ → ℂ)
    (hg : ∀ ω ∈ lamOf D cc δ, ∀ z, ‖U1 (lamOf D cc δ) ω g z‖ = ‖g z‖) :
    normSq D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (pullB D (tor0 D cc δ) b g) =
      nrm1Sq (lamOf D cc δ) g ^ r := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hlat := Parity.lamOf_eq_closure D cc δ hC
  obtain ⟨-, -, hpar, hmem, hbij⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' r b hb
  let e0 : VC D N N' →ₗ[ℝ] (Fin r → ℂ) :=
    { toFun := fun z k => coordB D (tor0 D cc δ) b k z
      map_add' := fun z w => by
        funext k; simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        funext k; simp [coordB, Finset.mul_sum, mul_assoc] }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := LinearEquiv.ofBijective e0 hbij
  haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have key := GlobalTheory.T.setAverage_prod_fundamentalDomain_planeLattice_pow (lamOf D cc δ) hlat
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area (lamOf D cc δ)))
    (fun ω hω z => by rw [← norm_sq_mul_gaussian_latticeTranslate_eq_shifted, hg ω hω]) (VC D N N') MeasureTheory.volume r e
    (LaB D (tor0 D cc δ) b) hmem
  unfold normSq nrm1Sq
  simp only
  rw [← key]
  congr 1
  funext z
  have h1 : (Hf D (tor0 D cc δ) z z).re = ∑ k, ‖e z k‖ ^ 2 / area (lamOf D cc δ) := by
    rw [Hf, hpar, Complex.div_ofReal_re, Complex.re_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]; rfl
  rw [h1, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, pullB, norm_prod, Finset.prod_pow]
  congr 2
  refine Finset.sum_congr rfl fun k _ => by ring

noncomputable def phiQ (D : D7) : D.host.E →+* Qbar :=
  D.host.φ₀.codRestrict (Qbar : IntermediateField ℚ ℂ) fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom

theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  obtain ⟨q, hq, h0'⟩ := RingOfIntegers.isIntegral_coe c
  have h0 : q.eval₂ (Int.castRingHom ℂ_[p]) (f (c : K)) = 0 := by
    have := congrArg f h0'
    rwa [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (f.comp _) (Int.castRingHom _)] at this
  by_contra hlt
  push Not at hlt
  set x := f (c : K)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at h0
  have h1 : x ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, Int.castRingHom ℂ_[p] (q.coeff i) * x ^ i := by
    linear_combination h0
  have h2 : ‖x ^ q.natDegree‖ < ‖x‖ ^ q.natDegree := by
    rw [h1, norm_neg]
    rcases Nat.eq_zero_or_pos q.natDegree with hz | hz
    · simp [hz]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (C := ‖x‖ ^ (q.natDegree - 1)) (by positivity) fun i hi => ?_) (pow_lt_pow_right₀ hlt (by omega))
    rw [norm_mul, norm_pow]
    have h3 : ‖Int.castRingHom ℂ_[p] (q.coeff i)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[p] (q.coeff i)
    have h4 : ‖x‖ ^ i ≤ ‖x‖ ^ (q.natDegree - 1) :=
      pow_le_pow_right₀ hlt.le (by have := Finset.mem_range.1 hi; omega)
    calc _ ≤ 1 * ‖x‖ ^ i := by gcongr
      _ ≤ _ := by rwa [one_mul]
  rw [norm_pow] at h2
  exact lt_irrefl _ h2

theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem exists_kappa (D : D7) (N N' r : ℕ) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb₀ : OnB D b₀)
    (hl₀ : LocBasis D 2 (YYl D (stdL D N) (stdL D N')) b₀) (hS : SD D (stdL D N)) (hS' : SD D (stdL D N')) :
    ∃ κ : ℂ, Mod1All κ ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b →
      LocBasis D p (YYl D (stdL D N) (stdL D N')) b →
      ‖lamC lam κ‖ ^ 2 =
        ‖lam (phiQ D (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E))‖ := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨I, hI, hloc⟩ := GlobalTheory.T.exists_determinantIdeal_hermitianLattice_basis D N N' r _ b₀ (GlobalTheory.T.hermitian_pairing_integral_values D N N' _ _ hS hS') (fun i => by
    obtain ⟨s, hs, h⟩ := hl₀.2.1 i
    refine ⟨s, Nat.pos_of_ne_zero ?_, h⟩
    rintro rfl
    simp at hs)
  have hI0 : I ≠ ⊥ := by
    obtain ⟨⟨s, hs, h⟩, -⟩ := hloc 2 b₀ hl₀
    rintro rfl
    have hu := GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one D hG N N' r b₀ b₀ hb₀ hb₀
    rw [Submodule.mem_bot, mul_eq_zero] at h
    rcases h with h | h
    · have : s = 0 := by exact_mod_cast h
      subst this; simp at hs
    · rw [h] at hu; simp at hu
  obtain ⟨h, α, hh, hα, hv⟩ := GlobalTheory.T.exists_generator_pow_fractionalIdeal_nonarch_size D.host.K I hI0 hI
  have hαE : (α : D.host.E) ≠ 0 := by simpa using hα
  have hαE' : D.host.conj (α : D.host.E) ≠ 0 := by simpa using hα
  set β : Qbar := phiQ D ((α : D.host.E) / D.host.conj (α : D.host.E)) with hβ
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq (β : ℂ) (n := 4 * h) (by omega)
  have hκQ : κ ∈ Qbar := mem_Qbar_of_pow (n := 4 * h) (by omega) (hκ ▸ β.2)
  have hκ' : (⟨κ, hκQ⟩ : Qbar) ^ (4 * h) = β := Subtype.ext (by simpa using hκ)
  refine ⟨κ, ⟨hκQ, fun σ => ?_⟩, fun p _ lam b hb hl => ?_⟩
  · have h1 : ‖σ β‖ = 1 := by
      have := D.host.conjE_apply (σ.comp (phiQ D)) (α : D.host.E)
      have h2 : σ β = (σ.comp (phiQ D)) (α : D.host.E) / (σ.comp (phiQ D)) (D.host.conj (α : D.host.E)) := by
        rw [← map_div₀]; rfl
      have h3 : (σ.comp (phiQ D)) (D.host.conj (α : D.host.E)) =
          (starRingEnd ℂ) ((σ.comp (phiQ D)) (α : D.host.E)) := this
      rw [h2, h3, norm_div, Complex.norm_conj, div_self]
      simpa using hα
    rw [← hκ', map_pow, norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  · set u : D.host.K := (Matrix.of fun i j => hYY D (b j) (b₀ i)).det
    obtain ⟨⟨s, hs, hsu⟩, hx⟩ := hloc p b hl
    have key : ∀ f : D.host.K →+* ℂ_[p], ‖f α‖ = ‖f u‖ ^ h := by
      intro f
      let v : D.host.K →*₀ ℝ := (normHom (α := ℂ_[p])).comp f.toMonoidWithZeroHom
      have hv' : ∀ x, v x = ‖f x‖ := fun x => rfl
      have h1 : v ((s : D.host.K) * u) = ‖f u‖ := by
        rw [hv', map_mul, norm_mul, map_natCast, norm_nat_coprime hs, one_mul]
      rw [← h1, ← hv']
      refine hv v (fun x => norm_nonneg (f x)) (fun x y => ?_) (fun c => norm_int_le f c) _ hsu fun x hxI => ?_
      · simp only [hv', map_add]; exact IsUltrametricDist.norm_add_le_max _ _
      · obtain ⟨s', c, hs', e⟩ := hx x hxI
        rw [h1, hv']
        have h2 := congrArg (fun y => ‖f y‖) e
        simp only [map_mul, norm_mul, map_natCast, norm_nat_coprime hs', one_mul] at h2
        rw [h2]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_int_le f c)
    have k1 := key ((lam.comp (phiQ D)).comp (algebraMap D.host.K D.host.E))
    have k2 := key (((lam.comp (phiQ D)).comp D.host.conj.toRingEquiv.toRingHom).comp
      (algebraMap D.host.K D.host.E))
    have hu := congrArg (fun y => ‖lam (phiQ D y)‖) (GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one D hG N N' r b₀ b hb₀ hb)
    simp only [map_mul, norm_mul, map_one, norm_one] at hu
    change ‖lam (phiQ D (α : D.host.E))‖ = ‖lam (phiQ D (u : D.host.E))‖ ^ h at k1
    change ‖lam (phiQ D (D.host.conj (α : D.host.E)))‖ = ‖lam (phiQ D (D.host.conj (u : D.host.E)))‖ ^ h at k2
    change ‖lam (phiQ D (u : D.host.E))‖ * ‖lam (phiQ D (D.host.conj (u : D.host.E)))‖ = 1 at hu
    have h3 : ‖lam ⟨κ, hκQ⟩‖ ^ (4 * h) = ‖lam (phiQ D (u : D.host.E))‖ ^ (2 * h) := by
      rw [← norm_pow, ← map_pow, hκ', hβ, map_div₀, map_div₀, norm_div, k1, k2, ← div_pow,
        eq_inv_of_mul_eq_one_right hu, div_inv_eq_mul, pow_mul, sq]
    rw [show lamC lam κ = lam ⟨κ, hκQ⟩ from lamC_coe lam ⟨κ, hκQ⟩]
    refine (pow_left_inj₀ (by positivity) (norm_nonneg _) (n := 2 * h) (by omega)).1 ?_
    rw [← h3, ← pow_mul]; congr 1; ring

theorem Iop_smul (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ) :
    Iop D T A₁ A₂ (fun z => c * G z) = fun z => c * Iop D T A₁ A₂ G z := by
  funext z
  simp only [Iop, U]
  rw [mul_left_comm c]
  congr 1
  rw [mul_finsum]
  congr 1; funext q; ring

theorem smul_mem_ThSp (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ)
    (h : G ∈ ThSp D T A) : (fun z => c * G z) ∈ ThSp D T A := by
  refine ⟨h.1.const_mul c, fun x hx z => ?_⟩
  beta_reduce
  rw [← h.2 x hx z]; simp only [U]; ring

theorem normSq_smul (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (c : ℂ) (hc : ‖c‖ = 1)
    (G : VC D N N' → ℂ) : normSq D T A (fun z => c * G z) = normSq D T A G := by
  simp only [normSq, norm_mul, hc, one_mul]

theorem exists_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ N N' : ℕ, Even (N * N') →
      ∃ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0 ∧ e0 ≠ 0 := by
  intro D cc δ hC t0 ht N N' hN
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨hd, h0, hth⟩ := evenTheta_properties_curveLattice D cc δ hC t0 ht
  have hK0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have hKb : ∀ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, OnB D b →
      KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := fun b hb => Or.inl ⟨_, b, hb, rfl⟩
  have hP : ∀ b : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, OnB D b →
      pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ ThSp D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := by
    intro b hb
    obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' _ b hb
    exact GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D _ N N' _ b _ hpar hmem hd hth
  obtain ⟨b₀, hb₀, hl₀⟩ := GlobalTheory.T.standardPairLattice_locally_orthonormal_basis D N N' hN 2 Nat.prime_two
  obtain ⟨κ, hκ, hκv⟩ := exists_kappa D N N' _ b₀ hb₀ hl₀ (hSD N) (hSD N')
  obtain ⟨hκQ, hκ1⟩ := id hκ
  have hκn : ‖κ‖ = 1 := hκ1 (Qbar : IntermediateField ℚ ℂ).val.toRingHom
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκn
  obtain ⟨-, u1, u2, u3⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hC N N' _ _ (hKb b₀ hb₀) hK0 _ (hP b₀ hb₀)
  have hE : ThetaVectorUpToUnits D (tor0 D cc δ) t0 (stdL D N) (stdL D N') (fun z => κ * Iop D (tor0 D cc δ)
      (LaB D (tor0 D cc δ) b₀) (La0 D (tor0 D cc δ) N N')
      (pullB D (tor0 D cc δ) b₀ (GL3Theta.th0 (lamOf D cc δ) t0)) z) := ⟨b₀, κ, hb₀, hκ, rfl⟩
  refine ⟨_, ⟨smul_mem_ThSp D _ _ κ _ u1,
    (GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hC t0 ht N N' _ _ (hSD N) (hSD N') hN _ hE).1, ?_, hE, ?_⟩, ?_⟩
  · rw [normSq_smul D _ _ κ hκn, u2]
    refine normSq_pullB D cc δ hC b₀ hb₀ _ fun ω hω z => ?_
    obtain ⟨m, -, hm⟩ := hth ω hω
    rw [← hm z, norm_mul, norm_zpow]; simp
  · intro p hp lam _
    obtain ⟨b, hb, hl⟩ := GlobalTheory.T.standardPairLattice_locally_orthonormal_basis D N N' hN p hp.out
    obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.T.thetaPullbackConstant_sq_eq_det D cc δ hC t0 ht N N' _ b₀ b hb₀ hb
    obtain ⟨μ, hμ, hI⟩ := GlobalTheory.T.admissible_characters_exist D cc δ hC N N' _ _ _ (hKb b₀ hb₀) (hKb b hb) hK0 _ (hP b₀ hb₀)
    have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
    have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
    set u := phiQ D (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) with hu
    have hc' : c ^ 2 = ζ * (u : ℂ) := hc
    have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc' ▸ mul_mem hζQ u.2)
    have n1 : ‖lam ⟨ζ, hζQ⟩‖ = 1 := by
      have : (⟨ζ, hζQ⟩ : Qbar) ^ m = 1 := Subtype.ext (by simpa using hζ)
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
      rw [← norm_pow, ← map_pow, this]; simp
    have n2 : ‖lam ⟨μ, hμQ⟩‖ = 1 := by
      have : (⟨μ, hμQ⟩ : Qbar) ^ 8 = 1 := Subtype.ext (by simpa using hμ)
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : 8 ≠ 0)).1 ?_
      rw [← norm_pow, ← map_pow, this]; simp
    have n3 : ‖lam ⟨c, hcQ⟩‖ = ‖lam ⟨κ, hκQ⟩‖ := by
      have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc')
      refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (n := 2) (by norm_num)).1 ?_
      rw [← norm_pow, ← map_pow, this, map_mul, norm_mul, n1, one_mul, ← hκv p lam b hb hl,
        ← lamC_coe lam ⟨κ, hκQ⟩]
    have n4 : ‖lam ⟨κ, hκQ⟩‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]
      exact fun h => hκ0 (congrArg Subtype.val h)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact n4 (by rw [← n3]; exact norm_eq_zero.2 (map_zero lam))
    have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ
    let ε : Qbar := ⟨κ, hκQ⟩ / (⟨c, hcQ⟩ * ⟨μ, hμQ⟩)
    have hε : (ε : ℂ) = κ / (c * μ) := by simp [ε]
    refine ⟨b, ε, hb, hl, ε.2, ?_, ?_, ?_⟩
    · rw [lamC_coe]
      simp only [ε, map_div₀, map_mul, norm_div, norm_mul, n2, n3, mul_one]
      exact div_self n4
    · exact GlobalTheory.T.localBasisLattice_index_coprime D hG cc δ N N' _ _ _ b p hp.out
        (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hC N N' _ hK0).2.2.2.2.1 hl
    · rw [hpull, Iop_smul, hI, hε]
      funext z
      field_simp
  · intro h
    have h1 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b₀) (La0 D (tor0 D cc δ) N N')
        (pullB D (tor0 D cc δ) b₀ (GL3Theta.th0 (lamOf D cc δ) t0)) = fun _ => 0 := by
      funext z
      exact (mul_eq_zero.1 (congrFun h z)).resolve_left hκ0
    rw [h1] at u3
    have h2 := congrFun u3 0
    simp [Iop, U, pullB, coordB, h0] at h2

end GlobalTheory.Vacuum
