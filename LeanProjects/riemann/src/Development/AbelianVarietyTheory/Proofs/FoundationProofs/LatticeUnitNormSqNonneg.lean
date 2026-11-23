import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedThetaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchNorm

theorem exists_galois (S : Set ℂ) (hS : S.Finite) (h : ∀ x ∈ S, x ∈ Qbar) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧ ∀ x ∈ S, x ∈ M := by
  have hint : ∀ x ∈ hS.toFinset, IsIntegral ℚ x := fun x hx =>
    (mem_algebraicClosure_iff.1 (h x (hS.mem_toFinset.1 hx))).isIntegral
  let p : Polynomial ℚ := ∏ x ∈ hS.toFinset, minpoly ℚ x
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun x hx => minpoly.ne_zero (hint x hx)
  have hsp : p.IsSplittingField ℚ (IntermediateField.adjoin ℚ (p.rootSet ℂ)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have := Polynomial.IsSplittingField.finiteDimensional (IntermediateField.adjoin ℚ (p.rootSet ℂ)) p
  have := Normal.of_isSplittingField (F := ℚ) (E := IntermediateField.adjoin ℚ (p.rootSet ℂ)) p
  refine ⟨IntermediateField.adjoin ℚ (p.rootSet ℂ), inferInstance, ⟨⟩, fun x hx => ?_⟩
  apply IntermediateField.subset_adjoin
  rw [Polynomial.mem_rootSet]
  refine ⟨hp, ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero (hS.mem_toFinset.2 hx) (minpoly.aeval ℚ x)

theorem exists_extension (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (ρ : M →ₐ[ℚ] ℂ) :
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x ∈ M, ρ' (TaylorLogMetric.liftM Qbar x) = ρ (TaylorLogMetric.liftM M x) := by
  have hle : M ≤ Qbar := le_algebraicClosure ℚ ℂ M
  let : Algebra M Qbar := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ M Qbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic M Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := Qbar) ρ
  refine ⟨φ, fun x hx => ?_⟩
  rw [← hφ]
  unfold TaylorLogMetric.liftM
  rw [dif_pos hx, dif_pos (hle hx)]
  rfl

theorem lattice_unitNormSq_nonneg (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) : 0 ≤ nrm1Sq Λ g := by
  unfold nrm1Sq
  simp only [MeasureTheory.average_eq, smul_eq_mul]
  exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun z => by positivity)

theorem area_nonneg (Λ : AddSubgroup ℂ) : 0 ≤ area Λ :=
  Real.sInf_nonneg fun _ h => h.1.le

theorem le_exp_posLog (y : ℝ) : y ≤ Real.exp (Real.posLog y) := by
  rcases le_or_gt y 0 with h | h
  · exact h.trans (Real.exp_pos _).le
  · calc y = Real.exp (Real.log y) := (Real.exp_log h).symm
      _ ≤ _ := Real.exp_le_exp.2 (le_max_right _ _)

theorem posLog_le_of_le_exp {y E : ℝ} (hy : 0 ≤ y) (hE : 0 ≤ E) (h : y ≤ Real.exp E) :
    Real.posLog y ≤ E := by
  refine (Real.posLog_le_posLog hy h).trans ?_
  rw [Real.posLog_apply, Real.log_exp]
  exact max_le hE le_rfl

theorem pow_le_exp {y t k : ℝ} {n : ℕ} (hy : 0 ≤ y) (ht : 0 ≤ t) (h : y ≤ Real.exp t) (hn : (n : ℝ) ≤ k) :
    y ^ n ≤ Real.exp (k * t) := by
  calc y ^ n ≤ Real.exp t ^ n := pow_le_pow_left₀ hy h n
    _ = Real.exp (n * t) := (Real.exp_nat_mul t n).symm
    _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hn ht)

theorem mul_le_exp {x y s t : ℝ} (hy : 0 ≤ y) (hx : x ≤ Real.exp s) (h : y ≤ Real.exp t) :
    x * y ≤ Real.exp (s + t) := by
  rw [Real.exp_add]
  exact mul_le_mul hx h hy (Real.exp_pos _).le

theorem le_exp_self (y : ℝ) : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]

theorem cls_le_exp (f k : ℕ) (n r l L : ℝ) (hf : 1 ≤ f) (hk : (k : ℝ) ≤ 2 * n) (hr : 0 ≤ r)
    (hl : 0 ≤ l) (hL : 0 ≤ L) (h1 : (f : ℝ) * (2 * n) ≤ Real.exp l) (h2 : r ≤ Real.exp L) :
    (12 * (f : ℝ) ^ 2 * (k : ℝ) ^ 4 * r ^ 2) ^ (6 * f * k ^ 2) ≤
      Real.exp (24 * f * n ^ 2 * (12 + 4 * l + 2 * L)) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine pow_le_exp (by positivity) (by positivity) ?_ ?_
  · have e1 : (f : ℝ) ^ 2 * (k : ℝ) ^ 4 ≤ Real.exp (4 * l) := by
      refine le_trans ?_ (pow_le_exp (y := (f : ℝ) * (2 * n)) (n := 4) (by nlinarith) hl h1 (by norm_num))
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ hf' (by norm_num)) (pow_le_pow_left₀ hk0 hk 4) (by positivity)
        (by positivity)
    have e2 : r ^ 2 ≤ Real.exp (2 * L) := pow_le_exp hr hL h2 (by norm_num)
    rw [mul_assoc (12 : ℝ)]
    exact mul_le_exp (by positivity) (mul_le_exp (by positivity) (le_exp_self 12) e1) e2
  · push_cast
    have := pow_le_pow_left₀ hk0 hk 2
    nlinarith

set_option maxHeartbeats 1600000 in

theorem sizes (f N a d s Q ch cT ca cd : ℕ) (B L r ν A : ℝ) (hf : 1 ≤ f) (hN : 1 ≤ N) (had : a ≤ d)
    (hd : d ≤ 2 * N) (hs : (s : ℝ) ≤ 2 * f * B) (hQ : 0 < Q) (hB : 1 ≤ B) (hL : 1 ≤ L) (hr : 1 ≤ r)
    (hrL : Real.log r ≤ L) (hν : 0 ≤ ν) (hA : 0 ≤ A) (hch : ch ≤ cd * Q ^ (d ^ 2 + 4))
    (hcT : cT ≤ 2 ^ (d * s))
    (hcd : (cd : ℝ) ≤ (12 * (f : ℝ) ^ 2 * (d : ℝ) ^ 4 * r ^ 2) ^ (6 * f * d ^ 2))
    (hca : (ca : ℝ) ≤ (12 * (f : ℝ) ^ 2 * (a : ℝ) ^ 4 * r ^ 2) ^ (6 * f * a ^ 2)) :
    (ch : ℝ) * cT * ((ca : ℝ) ^ 2 * (Q : ℝ) ^ (a * d) * (((a.factorial : ℝ) ^ s) ^ 2 *
      (3 * (2 * ((f * a * d : ℕ) : ℝ) * r + 1) ^ (f * a * d) * ν ^ (f * a * d) *
        (2 * Real.exp 1 * Real.pi * B / A) ^ (a * s)))) ≤
    Real.exp (1100 * f * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
      1100 * f * (N : ℝ) ^ 2 * (L + Real.log ((f : ℝ) * (2 * (N : ℝ)) * B)) + 1100 * (N : ℝ) ^ 2 * Real.log Q +
      (4 * f * (N : ℝ) ^ 2 * Real.posLog ν + 4 * f * N * B * Real.posLog A⁻¹)) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd' : (d : ℝ) ≤ 2 * N := by exact_mod_cast hd
  have ha' : (a : ℝ) ≤ 2 * N := by exact_mod_cast had.trans hd
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  generalize (N : ℝ) = n at *
  have hm1 : B * (2 * n) = Real.exp (Real.log (B * (2 * n))) := (Real.exp_log (by positivity)).symm
  have hm0 : 0 ≤ Real.log (B * (2 * n)) := Real.log_nonneg (by nlinarith)
  have hfn : 1 ≤ (f : ℝ) * (2 * n) := by nlinarith
  have hl1 : (f : ℝ) * (2 * n) * B = Real.exp (Real.log ((f : ℝ) * (2 * n) * B)) :=
    (Real.exp_log (by positivity)).symm
  have hl0 : 0 ≤ Real.log ((f : ℝ) * (2 * n) * B) := Real.log_nonneg (by nlinarith)
  have hq1 : (Q : ℝ) ≤ Real.exp (Real.log Q) := (Real.exp_log (by positivity)).ge
  have hq0 : 0 ≤ Real.log Q := Real.log_nonneg hQ'
  have hr1 : r ≤ Real.exp L := (Real.exp_log (by positivity)).ge.trans (Real.exp_le_exp.2 hrL)
  have hv1 := le_exp_posLog ν
  have hv0 : 0 ≤ Real.posLog ν := Real.posLog_nonneg
  have hu1 := le_exp_posLog A⁻¹
  have hu0 : 0 ≤ Real.posLog A⁻¹ := Real.posLog_nonneg
  generalize Real.log (B * (2 * n)) = m at *
  generalize Real.log ((f : ℝ) * (2 * n) * B) = l at *
  generalize Real.log Q = q at *
  generalize Real.posLog ν = v at *
  generalize Real.posLog A⁻¹ = u at *
  have hfl : (f : ℝ) * (2 * n) ≤ Real.exp l := by nlinarith
  have had' : (a : ℝ) * d ≤ 4 * n ^ 2 := by nlinarith
  have hG : ((f * a * d : ℕ) : ℝ) ≤ 4 * f * n ^ 2 := by push_cast; nlinarith
  have hG0 : (0 : ℝ) ≤ ((f * a * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 := hcd.trans (cls_le_exp f d n r l L hf hd' (by linarith) hl0 (by linarith) hfl hr1)
  have e2 := hca.trans (cls_le_exp f a n r l L hf ha' (by linarith) hl0 (by linarith) hfl hr1)
  have e3 : (ch : ℝ) ≤ Real.exp (24 * f * n ^ 2 * (12 + 4 * l + 2 * L) + 8 * n ^ 2 * q) := by
    have : (ch : ℝ) ≤ cd * (Q : ℝ) ^ (d ^ 2 + 4) := by exact_mod_cast hch
    refine this.trans (mul_le_exp (by positivity) e1 (pow_le_exp (by positivity) hq0 hq1 ?_))
    push_cast; nlinarith
  have e4 : (cT : ℝ) ≤ Real.exp (4 * f * n * B * 2) := by
    have : (cT : ℝ) ≤ (2 : ℝ) ^ (d * s) := by exact_mod_cast hcT
    refine this.trans (pow_le_exp (by positivity) (by positivity) (le_exp_self 2) ?_)
    push_cast
    have := mul_le_mul hd' hs hs0 (by positivity)
    linarith
  have e5 : (ca : ℝ) ^ 2 ≤ Real.exp (2 * (24 * f * n ^ 2 * (12 + 4 * l + 2 * L))) :=
    pow_le_exp (by positivity) (by positivity) e2 (by norm_num)
  have e6 : (Q : ℝ) ^ (a * d) ≤ Real.exp (4 * n ^ 2 * q) :=
    pow_le_exp (by positivity) hq0 hq1 (by push_cast; exact had')
  have e7 : ((a.factorial : ℝ) ^ s) ^ 2 ≤ Real.exp (2 * (2 * f * B * (2 * n * m))) := by
    refine pow_le_exp (by positivity) (by positivity) (pow_le_exp (by positivity) (by positivity) ?_ hs)
      (by norm_num)
    have : (a.factorial : ℝ) ≤ (a : ℝ) ^ a := by exact_mod_cast Nat.factorial_le_pow a
    exact this.trans (pow_le_exp ha0 hm0 (by nlinarith) ha')
  have e8 : (2 * ((f * a * d : ℕ) : ℝ) * r + 1) ^ (f * a * d) ≤
      Real.exp (4 * f * n ^ 2 * (3 + (2 * l + L))) := by
    refine pow_le_exp (by positivity) (by positivity) ?_ hG
    have h1 : ((f : ℝ) * (2 * n)) ^ 2 ≤ Real.exp (2 * l) := pow_le_exp (by positivity) hl0 hfl (by norm_num)
    have h2 : ((f * a * d : ℕ) : ℝ) ≤ Real.exp (2 * l) := by
      refine hG.trans (le_trans ?_ h1)
      have : 0 ≤ f * n ^ 2 * (f - 1) := by have : 0 ≤ (f : ℝ) - 1 := by linarith
                                           positivity
      nlinarith
    have h3 := mul_le_exp (by linarith) h2 hr1
    have h4 : 1 ≤ Real.exp (2 * l + L) := Real.one_le_exp (by linarith)
    have h5 := mul_le_exp (Real.exp_pos _).le (le_exp_self 3) (le_refl (Real.exp (2 * l + L)))
    linarith
  have e9 : ν ^ (f * a * d) ≤ Real.exp (4 * f * n ^ 2 * v) := pow_le_exp hν hv0 hv1 hG
  have e10 : (2 * Real.exp 1 * Real.pi * B / A) ^ (a * s) ≤ Real.exp (4 * f * n * B * (2 + 1 + 4 + m + u)) := by
    refine pow_le_exp (by positivity) (by positivity) ?_ ?_
    · rw [div_eq_mul_inv]
      refine mul_le_exp (by positivity) (mul_le_exp (by positivity) (mul_le_exp (by positivity)
        (mul_le_exp (by positivity) (le_exp_self 2) le_rfl) (Real.pi_le_four.trans (le_exp_self 4))) ?_) hu1
      nlinarith
    · push_cast
      have := mul_le_mul ha' hs hs0 (by positivity)
      linarith
  refine (mul_le_exp (by positivity) (mul_le_exp (by positivity) e3 e4)
    (mul_le_exp (by positivity) (mul_le_exp (by positivity) e5 e6)
      (mul_le_exp (by positivity) e7 (mul_le_exp (by positivity) (mul_le_exp (by positivity)
        (mul_le_exp (by positivity) (le_exp_self 3) e8) e9) e10)))).trans (Real.exp_le_exp.2 ?_)
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have t2 : 1 ≤ (f : ℝ) * n ^ 2 := by nlinarith
  have t1 : 0 ≤ (f : ℝ) * n * B := by positivity
  have p1 := mul_nonneg t1 hm0
  have p2 := mul_le_mul_of_nonneg_left hL t1
  have p3 := mul_nonneg (zero_le_one.trans t2) hl0
  have p4 := mul_le_mul_of_nonneg_left hL (zero_le_one.trans t2)
  have p5 := mul_nonneg (zero_le_one.trans hn2) hq0
  linarith

theorem mul_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) {w : ℂ}
    (hw : w ∈ lamOf D cc δ) : w * D.host.φ₀ ((a : D.host.K) : D.host.E) ∈ lamOf D cc δ := by
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨c * a, cc.mul_mem_right a hc, ?_⟩
    rw [mul_assoc, ← map_mul]
    congr 2
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem sum_prod_le {α β : Type} [Fintype α] [Fintype β] (g : α × β → ℝ) (X : ℝ) (h : ∀ p, g p ≤ X) :
    ∑ p, g p ≤ (Nat.card α : ℝ) * (Fintype.card β : ℝ) * X := by
  refine (Finset.sum_le_card_nsmul _ _ X fun p _ => h p).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, Nat.card_eq_fintype_card]

set_option maxHeartbeats 800000 in

theorem norm_meanInf_posLog_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta
  refine ⟨1100 + 4 * C₀, by positivity, ?_⟩
  intro D hI cc δ t0 Q hc ht hQ K _ _ _ σ N B L P x hN hB hL hrL hdL hsm hx
  obtain ⟨-, -, hr, hf, hcard, -⟩ := GlobalTheory.T.derivationDenominators_and_hostField_sizes D hI.g1
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 cc δ hc
  obtain ⟨-, hcd, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D P.d
  obtain ⟨hfin, hch⟩ := hJ P.J P.J_le P.idx_ne
  have hca := (GlobalTheory.NormSum.cls_finite_card_le D P.a).2.1
  have hcT := (GlobalTheory.MinorBound.minor_bound D P.a P.d P.n (fun _ => 0) 0 1 B one_pos hB le_rfl hsm.2
    (differentiable_const _) (fun z => by simp)).1
  have hcoord := GlobalTheory.T.thetaPair_coordinates_conjugate_bound D hI cc δ t0 Q hc ht P hQ B hB hsm.2
  let _ : Fintype (Cls D P.d P.J) := Fintype.ofFinite _
  have hwp : wpF (lamOf D cc δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := mul_mem_lamOf D cc δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have hz : ∀ h T, P.coord h T ∈ Qbar := fun h T => by
    obtain ⟨t', ht'⟩ := (hI.t0Ex cc δ hc).2 Qbar Qbar.val hdata.2.1 hdata.2.2
    exact (hcoord Qbar.val t' ht' h T).1
  let b := Module.finBasis ℚ K
  obtain ⟨M, hM1, hM2, hM⟩ := exists_galois
    (Set.range (fun i => σ (b i)) ∪
      Set.range (fun p : Cls D P.d P.J × Tup D P.a P.d P.n => P.coord p.1.out p.2) ∪
      {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wpF (lamOf D cc δ) t0})
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.toFinite _)) (by
      rintro y ((⟨i, rfl⟩ | ⟨p, rfl⟩) | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom σ.toRatAlgHom)
      · exact hz _ _
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, σ y ∈ M := fun y => by
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl (Or.inl ⟨i, rfl⟩)))
  have h2 : g2 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h3 : g3 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h4 : wpF (lamOf D cc δ) t0 ∈ M := hM _ (Or.inr (by simp))
  have hzM : ∀ p : Cls D P.d P.J × Tup D P.a P.d P.n, P.coord p.1.out p.2 ∈ M :=
    fun p => hM _ (Or.inl (Or.inr ⟨p, rfl⟩))
  choose t htt using fun ρ : M →ₐ[ℚ] ℂ => (hI.t0Ex cc δ hc).2 M ρ h2 h3
  obtain ⟨hu, hv⟩ := hmean D hI cc δ t0 hc ht L hL hrL hdL M h2 h3 h4 t htt
  refine (GlobalTheory.ArchMean.meanInf_posLog_le K σ x M (Cls D P.d P.J × Tup D P.a P.d P.n)
    (fun p => ((gam D P.J p.1.out : ℚ))⁻¹) (fun p => ⟨P.coord p.1.out p.2, hzM p⟩) hσ
    (fun p => by positivity) ?_).trans ?_
  · rw [hx, Pair.norm, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Pair.sq, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hs : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ 2 * fF D * B := by
    push_cast
    refine (Finset.sum_le_card_nsmul _ _ _ fun τ _ => hsm.2 τ).trans (le_of_eq ?_)
    rw [Finset.card_univ, hcard, nsmul_eq_mul]; ring
  have hf' : (1 : ℝ) ≤ fF D := by exact_mod_cast hf
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 ≤ Real.log (B * (2 * (N : ℝ))) := Real.log_nonneg (by nlinarith)
  have hfn : 1 ≤ (fF D : ℝ) * (2 * (N : ℝ)) := by nlinarith
  have hl0 : 0 ≤ Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := Real.log_nonneg (by nlinarith)
  have hq0 : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  set E₀ : ℝ := 1100 * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
      1100 * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) +
      1100 * (N : ℝ) ^ 2 * Real.log Q with hE₀
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (∑ p : Cls D P.d P.J × Tup D P.a P.d P.n,
        ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) * ‖ρ ⟨P.coord p.1.out p.2, hzM p⟩‖ ^ 2) ≤
      E₀ + (4 * fF D * (N : ℝ) ^ 2 * Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) +
        4 * fF D * N * B * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) := by
    intro ρ
    obtain ⟨ρ', hρ⟩ := exists_extension M ρ
    have hl : lamConj Qbar ρ' (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ) := by
      unfold lamConj
      rw [hρ _ h2, hρ _ h3]
    have hb := hcoord ρ' (t ρ) (hl ▸ htt ρ)
    rw [hl] at hb
    have h5 : 0 ≤ Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) := Real.posLog_nonneg
    have h6 : 0 ≤ Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := Real.posLog_nonneg
    refine posLog_le_of_le_exp (by positivity) (by positivity) (le_trans ?_
      (sizes (fF D) N P.a P.d (∑ τ, P.n τ) Q (Nat.card (Cls D P.d P.J)) (Fintype.card (Tup D P.a P.d P.n))
        _ _ B L D.host.rdE _ _ hf hN P.a_le hsm.1 hs hQ hB hL hr hrL (lattice_unitNormSq_nonneg _ _) (area_nonneg _)
        (hch.trans (Nat.mul_le_mul_left _ P.idx_le)) hcT hcd hca))
    refine sum_prod_le _ _ fun p => ?_
    · refine le_trans ?_ (hb p.1.out p.2).2
      have hg := (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le p.1.out).1
      have hg1 : ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 := by
        push_cast
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg)
      have he : cj Qbar ρ' (P.coord p.1.out p.2) = ρ ⟨P.coord p.1.out p.2, hzM p⟩ := by
        unfold cj
        rw [hρ _ (hzM p)]
        unfold TaylorLogMetric.liftM
        rw [dif_pos (hzM p)]
      rw [he]
      exact mul_le_of_le_one_left (by positivity) hg1
  clear_value E₀
  have hM0 : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun ρ _ => key ρ) hM0.le).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, AlgHom.card, nsmul_eq_mul, add_div, add_div, mul_div_cancel_left₀ _ hM0.ne',
    mul_div_assoc, mul_div_assoc]
  have p1 := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 * fF D * N * B by positivity)
  have p2 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 4 * fF D * (N : ℝ) ^ 2 by positivity)
  have p3 : 0 ≤ C₀ * fF D * N * B * L := by positivity
  have p4 : 0 ≤ C₀ * fF D * N * B * Real.log (B * (2 * (N : ℝ))) := by positivity
  have p5 : 0 ≤ C₀ * fF D * (N : ℝ) ^ 2 * Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := by positivity
  have p6 : 0 ≤ C₀ * (N : ℝ) ^ 2 * Real.log Q := by positivity
  rw [hE₀]
  linarith

end GlobalTheory.ArchNorm
