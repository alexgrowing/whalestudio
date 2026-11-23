import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalUniversalDenominator
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionCluster
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRootSumHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

namespace LocalUniversalDenominator

theorem differentiable_eval {ι : Type*} [Fintype ι] (q : MvPolynomial ι ℂ) :
    Differentiable ℂ (fun z : ι → ℂ => eval z q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem exists_eval_ne_zero {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0) {V : Set (Fin d → ℂ)}
    (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t P ≠ 0 := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t₀ ht₀
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  refine hP (MvPolynomial.funext_set (fun i => Metric.ball (t₀ i) ε)
    (fun i => infinite_of_mem_nhds (t₀ i) (Metric.ball_mem_nhds _ hε)) fun x hx => ?_)
  rw [map_zero]
  refine hall x (hball ?_)
  rw [ball_pi _ hε]
  exact hx

theorem exists_dim {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (hI : I.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d := by
  have := hI
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ (n : WithBot ℕ∞) := by
    have h := ringKrullDim_quotient_le I
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) :=
    ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = x at hle h0 ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe, top_le_iff] at hle
      exact ENat.natCast_ne_top n hle
    | coe k => exact ⟨k, rfl⟩

def divCoeff (P : Polynomial ℂ) (K j : ℕ) (τ : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (K + 1), if j < i then P.coeff i * τ ^ (i - 1 - j) else 0

theorem sum_divCoeff_mul (P : Polynomial ℂ) (K : ℕ) (τ s : ℂ) :
    ∑ j ∈ Finset.range K, divCoeff P K j τ * s ^ j =
      ∑ i ∈ Finset.range (K + 1), P.coeff i * ∑ j ∈ Finset.range i, s ^ j * τ ^ (i - 1 - j) := by
  simp only [divCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have hf : (Finset.range K).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_divCoeff_mul_sub (P : Polynomial ℂ) (K : ℕ) (hK : P.natDegree ≤ K) (τ s : ℂ) :
    (∑ j ∈ Finset.range K, divCoeff P K j τ * s ^ j) * (s - τ) = P.eval s - P.eval τ := by
  rw [sum_divCoeff_mul, Finset.sum_mul, P.eval_eq_sum_range' (n := K + 1) (by omega),
    P.eval_eq_sum_range' (n := K + 1) (by omega), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, geom_sum₂_mul, mul_sub]

theorem sum_divCoeff_diag (P : Polynomial ℂ) (K : ℕ) (hK : P.natDegree ≤ K) (τ : ℂ) :
    ∑ j ∈ Finset.range K, divCoeff P K j τ * τ ^ j = P.derivative.eval τ := by
  rw [sum_divCoeff_mul, Polynomial.derivative_eval,
    Polynomial.sum_over_range' _ (fun _ => by simp) (K + 1) (by omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ∑ j ∈ Finset.range i, τ ^ j * τ ^ (i - 1 - j) = i * τ ^ (i - 1) := by
    rw [Finset.sum_congr rfl fun j hj => by
      rw [← pow_add, show j + (i - 1 - j) = i - 1 by simp only [Finset.mem_range] at hj; omega]]
    simp
  rw [hs]
  ring

theorem rootSum_single (P : Polynomial ℂ) (K : ℕ) (hK : P.natDegree ≤ K) (hP0 : P ≠ 0) (b : ℂ → ℂ)
    (t : ℂ) (ht : P.IsRoot t) :
    ∑ τ ∈ P.roots.toFinset, b τ * ∑ j ∈ Finset.range K, divCoeff P K j τ * t ^ j =
      b t * P.derivative.eval t := by
  rw [Finset.sum_eq_single t]
  · rw [sum_divCoeff_diag P K hK]
  · intro τ hτ hτt
    have hτr : P.IsRoot τ := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.1 hτ)
    have h1 := sum_divCoeff_mul_sub P K hK τ t
    rw [ht.eq_zero, hτr.eq_zero, sub_zero] at h1
    have h2 : t - τ ≠ 0 := sub_ne_zero.2 (Ne.symm hτt)
    rw [(mul_eq_zero.1 h1).resolve_right h2, mul_zero]
  · intro hnot
    exact absurd (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hP0).2 ht)) hnot

theorem differentiable_polyEval {d : ℕ} (P : Polynomial (MvPolynomial (Fin d) ℂ)) :
    Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => (P.map (eval p.1)).eval p.2) := by
  have he : (fun p : (Fin d → ℂ) × ℂ => (P.map (eval p.1)).eval p.2) =
      fun p => ∑ i ∈ Finset.range (P.natDegree + 1), eval p.1 (P.coeff i) * p.2 ^ i := by
    funext p
    rw [Polynomial.eval_eq_sum_range' (n := P.natDegree + 1)
      (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _))]
    simp only [Polynomial.coeff_map]
  rw [he]
  refine Differentiable.fun_sum fun i _ => ?_
  have h1 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => eval p.1 (P.coeff i)) :=
    (differentiable_eval (P.coeff i)).comp differentiable_fst
  have h2 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => p.2 ^ i) := differentiable_snd.pow i
  exact h1.mul h2

theorem differentiable_divCoeff {d : ℕ} (m : Polynomial (MvPolynomial (Fin d) ℂ)) (K j : ℕ) :
    Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => divCoeff (m.map (eval p.1)) K j p.2) := by
  simp only [divCoeff, Polynomial.coeff_map]
  refine Differentiable.fun_sum fun i _ => ?_
  split_ifs
  · have h1 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => eval p.1 (m.coeff i)) :=
      (differentiable_eval (m.coeff i)).comp differentiable_fst
    have h2 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => p.2 ^ (i - 1 - j)) := differentiable_snd.pow _
    exact h1.mul h2
  · exact differentiable_const 0

theorem differentiable_mulVec {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A.mulVec x) := by
  refine differentiable_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Differentiable.fun_sum fun j _ => ?_
  exact (differentiable_const _).mul (differentiable_apply j)

theorem differentiable_linForm {n : ℕ} (c : Fin n → ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => ∑ j, c j * x j) := by
  refine Differentiable.fun_sum fun j _ => ?_
  exact (differentiable_const _).mul (differentiable_apply j)

end LocalUniversalDenominator

open LocalUniversalDenominator in

theorem LocalUniversalDenominator.fin_case
    (hcl : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster.Statement)
    (hrs : GroundTheory.Heights₂.Heights.ComplexSets.RootSumHolomorphic.Statement)
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (h : MvPolynomial (Fin n) ℂ) (w : Fin n → ℂ)
    (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ)
    (hI : I.IsPrime) (hh : h ∉ I) (hw : w ∈ zeroSetIn I) (hU : U ∈ 𝓝 w)
    (hf : HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}))
    (hb : Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0}))) :
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ I ∧ ∃ N : Set (Fin n → ℂ), IsOpen N ∧ w ∈ N ∧ N ⊆ U ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F N ∧
        ∀ z ∈ (zeroSetIn I ∩ N) \ {z | eval z h = 0}, eval z g * f z = F z := by
  classical
  obtain ⟨Mf, hMf⟩ := hb.exists_norm_le
  obtain ⟨d, hd⟩ := exists_dim I hI
  obtain ⟨Wz, -, ⟨A, hAW⟩, hWsub⟩ :=
    GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
      GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
      GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
        GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
        GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
        GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof)
      n d I hI hd
  have hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection I A := hWsub hAW
  obtain ⟨c, mp, Δ, Q, hmon, -, hΔ, hgood⟩ :=
    GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof n d I A hI hd hA
  have hevpb : ∀ (x : Fin n → ℂ) (P : MvPolynomial (Fin d) ℂ),
      eval x (GroundTheory.Heights₂.Heights.ComplexSets.pullback A P) = eval (A.mulVec x) P :=
    fun x P => GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.eval_pullback A x P
  have hpbI : ∀ P : MvPolynomial (Fin d) ℂ,
      GroundTheory.Heights₂.Heights.ComplexSets.pullback A P ∈ I → P = 0 := by
    intro P hP
    apply hA.injective
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hP

  obtain ⟨a, ha0, ha⟩ : ∃ a : MvPolynomial (Fin d) ℂ, a ≠ 0 ∧
      ∀ z ∈ zeroSetIn I, eval z h = 0 → eval (A.mulVec z) a = 0 := by
    let alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
      (GroundTheory.Heights₂.Heights.ComplexSets.projHom I A).toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := alg.toModule
    have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := hA.finite
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
      Algebra.IsIntegral.of_finite _ _
    have := hI
    have hx0 : Ideal.Quotient.mk I h ≠ 0 := fun e => hh (Ideal.Quotient.eq_zero_iff_mem.1 e)
    have hne := Ideal.comap_ne_bot_of_integral_mem hx0 (Ideal.mem_span_singleton_self _)
      (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk I h))
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine ⟨a, ha0, fun z hz hz0 => ?_⟩
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, hb⟩ := ha
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : GroundTheory.Heights₂.Heights.ComplexSets.pullback A a - b' * h ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul]
      exact hb.symm
    have h1 := hz _ hmem
    rw [map_sub, map_mul, hz0, mul_zero, sub_zero, hevpb] at h1
    exact h1

  obtain ⟨y₁, -, hy₁⟩ := exists_eval_ne_zero hΔ isOpen_univ Set.univ_nonempty
  have hK : mp.natDegree ≠ 0 := by
    intro hK0
    have h1 : mp = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hK0
    obtain ⟨x, hx⟩ := (GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof n d I A hI hd hA y₁).1
    have h2 := ((hgood y₁ hy₁).2.1 x hx).1
    rw [h1, Polynomial.map_one] at h2
    simp [Polynomial.IsRoot] at h2
  obtain ⟨p, q, -, -, hpq⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant mp
    (Polynomial.derivative mp) le_rfl le_rfl (Or.inl hK)
  set D := mp.resultant (Polynomial.derivative mp) with hDdef
  have hD : D ≠ 0 := by
    intro hD0
    have hsep := (hgood y₁ hy₁).1
    have e3 : ((Polynomial.derivative mp).map (eval y₁)).natDegree =
        (Polynomial.derivative mp).natDegree := by
      rw [← Polynomial.derivative_map, Polynomial.natDegree_derivative, Polynomial.natDegree_derivative,
        hmon.natDegree_map]
    have key : (mp.map (eval y₁)).resultant (Polynomial.derivative (mp.map (eval y₁))) = eval y₁ D := by
      rw [hDdef, ← Polynomial.resultant_map_map, Polynomial.derivative_map, hmon.natDegree_map, e3]
    exact Polynomial.resultant_ne_zero _ _ hsep (key.trans (by rw [hD0, map_zero]))

  obtain ⟨r, N0, M, hr, hN0, hM, hwN0, hN0U, hNM, hcov, hbdd⟩ := hcl n d I A w U hA hw hU
  have hE0 : Δ * a ≠ 0 := mul_ne_zero hΔ ha0
  set W : Set (Fin d → ℂ) := Metric.ball (A.mulVec w) r with hWdef
  set W' : Set (Fin d → ℂ) := W ∩ {y | eval y (Δ * a) ≠ 0} with hW'def
  have hW'o : IsOpen W' :=
    Metric.isOpen_ball.inter (isOpen_ne_fun (differentiable_eval _).continuous continuous_const)
  have hgoodW : ∀ y ∈ W', eval y Δ ≠ 0 ∧ eval y a ≠ 0 := fun y hy => by
    have h1 : eval y (Δ * a) ≠ 0 := hy.2
    rw [eval_mul] at h1
    exact ⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩
  obtain ⟨zpt, hzpt⟩ : ∃ zpt : (Fin d → ℂ) → ℂ → Fin n → ℂ,
      ∀ y τ j, zpt y τ j = ((Q j).map (eval y)).eval τ / eval y Δ := ⟨_, fun _ _ _ => rfl⟩
  have hfib : ∀ y ∈ W', ∀ τ : ℂ, (mp.map (eval y)).IsRoot τ →
      zpt y τ ∈ zeroSetIn I ∧ A.mulVec (zpt y τ) = y ∧ (∑ j, c j * zpt y τ j) = τ ∧
        eval (zpt y τ) h ≠ 0 ∧ zpt y τ ∈ N0 ∪ M := by
    intro y hy τ hτ
    obtain ⟨hΔy, hay⟩ := hgoodW y hy
    obtain ⟨x, hx, hxτ⟩ := (hgood y hΔy).2.2 τ hτ
    have hQx := ((hgood y hΔy).2.1 x hx).2
    obtain ⟨hx1, hx2⟩ := hx
    have hxz : zpt y τ = x := by
      funext j
      rw [hzpt, div_eq_iff hΔy, ← hxτ, ← hQx j, mul_comm]
    rw [hxz]
    refine ⟨hx1, hx2, hxτ, fun h0 => hay ?_, hcov ⟨hx1, ?_⟩⟩
    · have h1 := ha x hx1 h0
      rwa [hx2] at h1
    · show A.mulVec x ∈ W
      rw [hx2]
      exact hy.1

  set K := mp.natDegree with hKdef
  obtain ⟨ftil, hftil⟩ : ∃ ftil : (Fin n → ℂ) → ℂ, ∀ z, ftil z = if z ∈ N0 then f z else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → (Fin d → ℂ) → ℂ → ℂ, ∀ j y τ,
      Φ j y τ = ftil (zpt y τ) * ((q.map (eval y)).eval τ * divCoeff (mp.map (eval y)) K j τ) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hzptd : ∀ p : (Fin d → ℂ) × ℂ, eval p.1 Δ ≠ 0 →
      DifferentiableAt ℂ (fun p : (Fin d → ℂ) × ℂ => zpt p.1 p.2) p := by
    intro p hp
    have he : (fun p : (Fin d → ℂ) × ℂ => zpt p.1 p.2) =
        fun p j => ((Q j).map (eval p.1)).eval p.2 / eval p.1 Δ := by
      funext p j
      exact hzpt _ _ _
    rw [he, differentiableAt_pi]
    intro j
    have h1 : Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ => eval p.1 Δ) :=
      (differentiable_eval Δ).comp differentiable_fst
    have h2 : DifferentiableAt ℂ (fun p : (Fin d → ℂ) × ℂ => ((Q j).map (eval p.1)).eval p.2) p :=
      differentiable_polyEval (Q j) p
    simp only [div_eq_mul_inv]
    exact h2.mul ((h1 p).inv hp)
  have hrest : ∀ j, Differentiable ℂ (fun p : (Fin d → ℂ) × ℂ =>
      (q.map (eval p.1)).eval p.2 * divCoeff (mp.map (eval p.1)) K j p.2) :=
    fun j => (differentiable_polyEval q).mul (differentiable_divCoeff mp K j)
  have hcd : ∀ j, DifferentiableOn ℂ (fun y => ((mp.map (eval y)).roots.map (Φ j y)).sum) W' := by
    intro j
    refine hrs d mp W' (Φ j) hmon hW'o (fun y hy => (hgood y (hgoodW y hy).1).1) ?_
    intro y₀ hy₀ τ₀ hτ₀
    obtain ⟨hz₀I, -, -, hz₀h, hz₀NM⟩ := hfib y₀ hy₀ τ₀ hτ₀
    have hGo : IsOpen (W' ×ˢ (Set.univ : Set ℂ)) := hW'o.prod isOpen_univ
    have hzc : ContinuousOn (fun p : (Fin d → ℂ) × ℂ => zpt p.1 p.2) (W' ×ˢ Set.univ) :=
      fun p hp => (hzptd p (hgoodW p.1 hp.1).1).continuousAt.continuousWithinAt
    by_cases hz₀N : zpt y₀ τ₀ ∈ N0
    · obtain ⟨O', hO', hz₀O', Fl, hFl, hfFl⟩ := hf (zpt y₀ τ₀) ⟨⟨hz₀I, hN0U hz₀N⟩, hz₀h⟩
      refine ⟨(W' ×ˢ Set.univ) ∩ (fun p : (Fin d → ℂ) × ℂ => zpt p.1 p.2) ⁻¹' (O' ∩ N0),
        hzc.isOpen_inter_preimage hGo (hO'.inter hN0), ⟨⟨hy₀, Set.mem_univ _⟩, hz₀O', hz₀N⟩,
        fun p => Fl (zpt p.1 p.2) * ((q.map (eval p.1)).eval p.2 * divCoeff (mp.map (eval p.1)) K j p.2),
        ?_, ?_⟩
      · intro p hp
        have hp1 : zpt p.1 p.2 ∈ O' := hp.2.1
        have h1 : DifferentiableAt ℂ (fun p : (Fin d → ℂ) × ℂ => Fl (zpt p.1 p.2)) p :=
          (hFl.differentiableAt (hO'.mem_nhds hp1)).comp p (hzptd p (hgoodW p.1 hp.1.1).1)
        exact (h1.mul ((hrest j) p)).differentiableWithinAt
      · intro p hp hroot
        obtain ⟨hpI, -, -, hph, -⟩ := hfib p.1 hp.1.1 p.2 hroot
        have hp1 : zpt p.1 p.2 ∈ O' := hp.2.1
        have hp2 : zpt p.1 p.2 ∈ N0 := hp.2.2
        rw [hΦ, hftil, if_pos hp2, hfFl ⟨⟨⟨hpI, hN0U hp2⟩, hph⟩, hp1⟩]
    · have hz₀M : zpt y₀ τ₀ ∈ M := hz₀NM.resolve_left hz₀N
      refine ⟨(W' ×ˢ Set.univ) ∩ (fun p : (Fin d → ℂ) × ℂ => zpt p.1 p.2) ⁻¹' M,
        hzc.isOpen_inter_preimage hGo hM, ⟨⟨hy₀, Set.mem_univ _⟩, hz₀M⟩, fun _ => 0,
        differentiableOn_const 0, ?_⟩
      intro p hp _
      have hpM : zpt p.1 p.2 ∈ M := hp.2
      have hpN : zpt p.1 p.2 ∉ N0 := fun hN => Set.disjoint_left.1 hNM hN hpM
      rw [hΦ, hftil, if_neg hpN, zero_mul]

  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hτb : ∀ y ∈ W', ∀ τ, (mp.map (eval y)).IsRoot τ → ‖τ‖ ≤ ∑ j, ‖c j‖ * R := by
    intro y hy τ hτ
    obtain ⟨hzI, hzA, hzℓ, -, -⟩ := hfib y hy τ hτ
    have hzR : ‖zpt y τ‖ ≤ R := hR _ ⟨hzI, by show A.mulVec (zpt y τ) ∈ W; rw [hzA]; exact hy.1⟩
    rw [← hzℓ]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ j).trans hzR) (norm_nonneg _)
  have hKc : IsCompact (Metric.closedBall (A.mulVec w) r ×ˢ Metric.closedBall (0 : ℂ) (∑ j, ‖c j‖ * R)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hcb : ∀ j, ∃ C, ∀ y ∈ W', ‖((mp.map (eval y)).roots.map (Φ j y)).sum‖ ≤ C := by
    intro j
    obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn (hrest j).continuous.continuousOn
    refine ⟨(K : ℝ) * (max Mf 0 * max C₁ 0), fun y hy => ?_⟩
    have hterm : ∀ τ ∈ (mp.map (eval y)).roots, ‖Φ j y τ‖ ≤ max Mf 0 * max C₁ 0 := by
      intro τ hτ
      have hroot := Polynomial.isRoot_of_mem_roots hτ
      have hyτ : (y, τ) ∈ Metric.closedBall (A.mulVec w) r ×ˢ Metric.closedBall (0 : ℂ) (∑ j, ‖c j‖ * R) :=
        ⟨Metric.ball_subset_closedBall hy.1, by rw [mem_closedBall_zero_iff]; exact hτb y hy τ hroot⟩
      rw [hΦ, norm_mul]
      refine mul_le_mul ?_ ((hC₁ (y, τ) hyτ).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
      rw [hftil]
      split_ifs with hN
      · obtain ⟨hzI, -, -, hzh, -⟩ := hfib y hy τ hroot
        exact (hMf _ ⟨zpt y τ, ⟨⟨hzI, hN0U hN⟩, hzh⟩, rfl⟩).trans (le_max_left _ _)
      · rw [norm_zero]
        exact le_max_right _ _
    calc ‖((mp.map (eval y)).roots.map (Φ j y)).sum‖
        ≤ (((mp.map (eval y)).roots.map (Φ j y)).map (fun x => ‖x‖)).sum := norm_multiset_sum_le _
      _ ≤ Multiset.card (((mp.map (eval y)).roots.map (Φ j y)).map (fun x => ‖x‖)) •
            (max Mf 0 * max C₁ 0) := by
          refine Multiset.sum_le_card_nsmul _ _ fun x hx => ?_
          rw [Multiset.map_map, Multiset.mem_map] at hx
          obtain ⟨τ, hτ, rfl⟩ := hx
          exact hterm τ hτ
      _ ≤ (K : ℝ) * (max Mf 0 * max C₁ 0) := by
          rw [Multiset.card_map, Multiset.card_map, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_max_right _ _) (le_max_right _ _))
          exact_mod_cast (Polynomial.card_roots' _).trans Polynomial.natDegree_map_le

  have hEne : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ W → V.Nonempty → ∃ t ∈ V, eval t (Δ * a) ≠ 0 :=
    fun V hV _ hne => exists_eval_ne_zero hE0 hV hne
  have hext : ∀ j, ∃ Cj : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ Cj W ∧
      Set.EqOn Cj (fun y => ((mp.map (eval y)).roots.map (Φ j y)).sum)
        (W ∩ {t | eval t (Δ * a) ≠ 0}) := by
    intro j
    obtain ⟨C, hC⟩ := hcb j
    refine RiemannExtensionAnalytic.proof d W (fun t => eval t (Δ * a)) _ Metric.isOpen_ball
      (differentiable_eval _).differentiableOn hEne (hcd j) fun τ _ => ⟨Set.univ, Filter.univ_mem, ?_⟩
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := C)).subset ?_
    rintro _ ⟨y, ⟨⟨-, hyW⟩, hyE⟩, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hC y ⟨hyW, hyE⟩
  choose Cf hCf hCeq using hext
  have hCeq' : ∀ j, ∀ y ∈ W', Cf j y = ((mp.map (eval y)).roots.map (Φ j y)).sum :=
    fun j y hy => hCeq j hy

  set Nf : Set (Fin n → ℂ) := N0 ∩ {x | A.mulVec x ∈ W} with hNfdef
  have hNfo : IsOpen Nf :=
    hN0.inter (Metric.isOpen_ball.preimage (differentiable_mulVec A).continuous)
  obtain ⟨Fs, hFs⟩ : ∃ Fs : (Fin n → ℂ) → ℂ, ∀ z,
      Fs z = ∑ j ∈ Finset.range K, Cf j (A.mulVec z) * (∑ i, c i * z i) ^ j := ⟨_, fun _ => rfl⟩
  have hFd : DifferentiableOn ℂ Fs Nf := by
    have he : Fs = fun z => ∑ j ∈ Finset.range K, Cf j (A.mulVec z) * (∑ i, c i * z i) ^ j :=
      funext hFs
    rw [he]
    intro z hz
    refine DifferentiableWithinAt.fun_sum fun j _ => ?_
    have hzW : A.mulVec z ∈ W := hz.2
    have h1 : DifferentiableAt ℂ (fun z : Fin n → ℂ => Cf j (A.mulVec z)) z :=
      ((hCf j).differentiableAt (Metric.isOpen_ball.mem_nhds hzW)).comp z (differentiable_mulVec A z)
    have h2 : DifferentiableAt ℂ (fun z : Fin n → ℂ => (∑ i, c i * z i) ^ j) z :=
      (differentiable_linForm c z).pow j
    exact (h1.mul h2).differentiableWithinAt

  have hgoodId : ∀ z ∈ zeroSetIn I, A.mulVec z ∈ W' → z ∈ N0 →
      Fs z = eval (A.mulVec z) D * f z := by
    intro z hzI hy hzN
    obtain ⟨hΔy, -⟩ := hgoodW _ hy
    obtain ⟨hroot, hQz⟩ := (hgood (A.mulVec z) hΔy).2.1 z ⟨hzI, rfl⟩
    have hsep := (hgood (A.mulVec z) hΔy).1
    have hP0 : mp.map (eval (A.mulVec z)) ≠ 0 := (hmon.map _).ne_zero
    have hPdeg : (mp.map (eval (A.mulVec z))).natDegree ≤ K := Polynomial.natDegree_map_le
    have hnd := Polynomial.nodup_roots hsep
    have hms : ∀ g : ℂ → ℂ, ((mp.map (eval (A.mulVec z))).roots.map g).sum =
        ∑ τ ∈ (mp.map (eval (A.mulVec z))).roots.toFinset, g τ := fun g => by
      rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, hnd.dedup]
    have hzz : zpt (A.mulVec z) (∑ i, c i * z i) = z := by
      funext j
      rw [hzpt, div_eq_iff hΔy, ← hQz j, mul_comm]
    have hDq : (q.map (eval (A.mulVec z))).eval (∑ i, c i * z i) *
        (mp.map (eval (A.mulVec z))).derivative.eval (∑ i, c i * z i) = eval (A.mulVec z) D := by
      have h1 := congrArg (fun t => (t.map (eval (A.mulVec z))).eval (∑ i, c i * z i)) hpq
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C] at h1
      rw [← Polynomial.derivative_map, hroot.eq_zero, zero_mul, zero_add] at h1
      rw [mul_comm]
      exact h1
    rw [hFs]
    have e1 : ∀ j ∈ Finset.range K, Cf j (A.mulVec z) * (∑ i, c i * z i) ^ j =
        ∑ τ ∈ (mp.map (eval (A.mulVec z))).roots.toFinset,
          Φ j (A.mulVec z) τ * (∑ i, c i * z i) ^ j := by
      intro j _
      rw [hCeq' j _ hy, hms, Finset.sum_mul]
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    have e2 : ∀ τ ∈ (mp.map (eval (A.mulVec z))).roots.toFinset,
        ∑ j ∈ Finset.range K, Φ j (A.mulVec z) τ * (∑ i, c i * z i) ^ j =
          (ftil (zpt (A.mulVec z) τ) * (q.map (eval (A.mulVec z))).eval τ) *
            ∑ j ∈ Finset.range K,
              divCoeff (mp.map (eval (A.mulVec z))) K j τ * (∑ i, c i * z i) ^ j := by
      intro τ _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΦ]
      ring
    rw [Finset.sum_congr rfl e2, rootSum_single _ K hPdeg hP0
      (fun τ => ftil (zpt (A.mulVec z) τ) * (q.map (eval (A.mulVec z))).eval τ) _ hroot]
    rw [hzz, hftil, if_pos hzN, mul_assoc, hDq, mul_comm]

  refine ⟨GroundTheory.Heights₂.Heights.ComplexSets.pullback A D, fun hD' => hD (hpbI D hD'), Nf, hNfo,
    ⟨hwN0, Metric.mem_ball_self hr⟩, fun x hx => hN0U hx.1, Fs, hFd, ?_⟩
  rintro z ⟨⟨hzI, hzN⟩, hzh⟩
  have hzS : z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} := ⟨⟨hzI, hN0U hzN.1⟩, hzh⟩
  obtain ⟨O', hO', hzO', Fl, hFl, hfFl⟩ := hf z hzS
  set O'' : Set (Fin n → ℂ) := O' ∩ Nf ∩ {x | eval x h ≠ 0} with hO''def
  have hO''o : IsOpen O'' :=
    (hO'.inter hNfo).inter (isOpen_ne_fun (differentiable_eval h).continuous continuous_const)
  have hzO'' : z ∈ O'' := ⟨⟨hzO', hzN⟩, hzh⟩
  set T : Set (Fin n → ℂ) := O'' ∩ {x | x ∈ zeroSetIn I ∧ eval (A.mulVec x) (Δ * a) ≠ 0}
    with hTdef
  have hT : Set.EqOn (fun x => eval x (GroundTheory.Heights₂.Heights.ComplexSets.pullback A D) * Fl x) Fs T := by
    intro x hx
    obtain ⟨⟨⟨hxO', hxN⟩, hxh⟩, hxI, hxE⟩ := hx
    have hxS : x ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} := ⟨⟨hxI, hN0U hxN.1⟩, hxh⟩
    show eval x _ * Fl x = Fs x
    rw [← hfFl ⟨hxS, hxO'⟩, hgoodId x hxI ⟨hxN.2, hxE⟩ hxN.1, hevpb]
  have hzT : z ∈ closure T := by
    rw [mem_closure_iff_frequently]
    have hnv : ¬ ∀ᶠ x in 𝓝 z, x ∈ zeroLocus I →
        eval x (GroundTheory.Heights₂.Heights.ComplexSets.pullback A (Δ * a)) = 0 := fun hev =>
      hE0 (hpbI _ (VanishNearPoint.proof FiniteMapOpen.proof n I _ z hI hzI hev))
    rw [Filter.not_eventually] at hnv
    refine (hnv.and_eventually (hO''o.mem_nhds hzO'')).mono fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := hx
    rw [Classical.not_imp] at hx1
    refine ⟨hx2, hx1.1, ?_⟩
    rw [← hevpb]
    exact hx1.2
  have hc1 : ContinuousOn (fun x => eval x (GroundTheory.Heights₂.Heights.ComplexSets.pullback A D) * Fl x) O'' :=
    (differentiable_eval _).continuous.continuousOn.mul (hFl.continuousOn.mono fun x hx => hx.1.1)
  have hc2 : ContinuousOn Fs O'' := hFd.continuousOn.mono fun x hx => hx.1.2
  have hsub : insert z T ⊆ O'' := Set.insert_subset_iff.2 ⟨hzO'', fun x hx => hx.1⟩
  have hfin := hT.of_subset_closure (hc1.mono hsub) (hc2.mono hsub) (Set.subset_insert z T)
    (Set.insert_subset_iff.2 ⟨hzT, subset_closure⟩) (Set.mem_insert z T)
  rw [hfFl ⟨hzS, hzO'⟩]
  exact hfin

theorem LocalUniversalDenominator.proof
    (hcl : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster.Statement)
    (hrs : GroundTheory.Heights₂.Heights.ComplexSets.RootSumHolomorphic.Statement) :
    LocalUniversalDenominator.Statement := by
  intro σ _ I h w U f hI hh hw hU hf hb
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let ρ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ := MvPolynomial.renameEquiv ℂ e
  let T : (σ → ℂ) → (Fin (Fintype.card σ) → ℂ) := fun z => z ∘ e.symm
  let Ti : (Fin (Fintype.card σ) → ℂ) → (σ → ℂ) := fun x => x ∘ e
  have hTiT : ∀ z, Ti (T z) = z := fun z => funext fun i => by simp [T, Ti]
  have hev : ∀ (x : Fin (Fintype.card σ) → ℂ) (q : MvPolynomial σ ℂ), eval x (ρ q) = eval (Ti x) q :=
    fun x q => by
      show eval x (rename e q) = eval (x ∘ e) q
      exact MvPolynomial.eval_rename _ _ _
  have hev' : ∀ (z : σ → ℂ) (q' : MvPolynomial (Fin (Fintype.card σ)) ℂ),
      eval z (ρ.symm q') = eval (T z) q' := fun z q' => by
    have h1 := hev (T z) (ρ.symm q')
    rw [AlgEquiv.apply_symm_apply, hTiT] at h1
    exact h1.symm
  have hTic : Continuous Ti := continuous_pi fun i => continuous_apply (e i)
  have hTc : Continuous T := continuous_pi fun i => continuous_apply (e.symm i)
  have hTid : Differentiable ℂ Ti := differentiable_pi.2 fun i => differentiable_apply (e i)
  have hTd : Differentiable ℂ T := differentiable_pi.2 fun i => differentiable_apply (e.symm i)
  set I' : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap ρ.symm with hI'def
  have hI' : I'.IsPrime := by
    have := hI
    exact Ideal.comap_isPrime _ _
  have hZ : ∀ x, x ∈ zeroSetIn I' ↔ Ti x ∈ zeroSetIn I := by
    intro x
    constructor
    · intro hx q hq
      rw [← hev]
      exact hx _ (by rw [hI'def, Ideal.mem_comap, AlgEquiv.symm_apply_apply]; exact hq)
    · intro hx q' hq'
      rw [hI'def, Ideal.mem_comap] at hq'
      have h1 := hx _ hq'
      rwa [← hev, AlgEquiv.apply_symm_apply] at h1
  have hS : ∀ x, x ∈ (zeroSetIn I' ∩ Ti ⁻¹' U) \ {x | eval x (ρ h) = 0} →
      Ti x ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} := fun x hx =>
    ⟨⟨(hZ x).1 hx.1.1, hx.1.2⟩, fun h0 => hx.2 (by
      show eval x (ρ h) = 0
      rw [hev]
      exact h0)⟩
  have hf' : HolomorphicOnSubset (f ∘ Ti) ((zeroSetIn I' ∩ Ti ⁻¹' U) \ {x | eval x (ρ h) = 0}) := by
    intro x hx
    obtain ⟨O, hO, hxO, F, hF, hfF⟩ := hf (Ti x) (hS x hx)
    exact ⟨Ti ⁻¹' O, hO.preimage hTic, hxO, F ∘ Ti, hF.comp hTid.differentiableOn fun y hy => hy,
      fun y hy => hfF ⟨hS y hy.1, hy.2⟩⟩
  have hb' : Bornology.IsBounded ((f ∘ Ti) '' ((zeroSetIn I' ∩ Ti ⁻¹' U) \ {x | eval x (ρ h) = 0})) :=
    hb.subset (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨Ti x, hS x hx, rfl⟩)
  have hh' : ρ h ∉ I' := fun hm => hh (by
    rw [hI'def, Ideal.mem_comap, AlgEquiv.symm_apply_apply] at hm
    exact hm)
  have hw' : T w ∈ zeroSetIn I' := (hZ _).2 (by rw [hTiT]; exact hw)
  have hU' : Ti ⁻¹' U ∈ 𝓝 (T w) := hTic.continuousAt.preimage_mem_nhds (by rw [hTiT]; exact hU)
  obtain ⟨g', hg', N', hN'o, hwN', hN'U, F', hF', hid⟩ :=
    LocalUniversalDenominator.fin_case hcl hrs (Fintype.card σ) I' (ρ h) (T w) (Ti ⁻¹' U) (f ∘ Ti)
      hI' hh' hw' hU' hf' hb'
  refine ⟨ρ.symm g', fun hm => hg' (by rw [hI'def, Ideal.mem_comap]; exact hm), T ⁻¹' N',
    hN'o.preimage hTc, hwN', fun z hz => ?_, F' ∘ T, hF'.comp hTd.differentiableOn fun z hz => hz, ?_⟩
  · have h1 : Ti (T z) ∈ U := hN'U hz
    rwa [hTiT] at h1
  · rintro z ⟨⟨hzI, hzN⟩, hzh⟩
    have h1 := hid (T z) ⟨⟨(hZ _).2 (by rw [hTiT]; exact hzI), hzN⟩, fun h0 => hzh (by
      have h2 : eval (T z) (ρ h) = 0 := h0
      rw [hev, hTiT] at h2
      exact h2)⟩
    rw [hev']
    simpa only [Function.comp_apply, hTiT] using h1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
