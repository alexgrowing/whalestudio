import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftGrow

theorem reduction_unif {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) :
    ∃ M : ℕ, ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
      ∃ (S : Finset (GA D V)) (C : ℝ), 0 ≤ C ∧ ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧
        γ * g = x * a * k ∧ 1 + normInf θ V a ≤ C * (height θ V g : ℝ) ^ M := by
  obtain ⟨d, C, M, hd, h⟩ := GlobalTheory.T.unitary_reduction_polynomial_height_bound D θ V hθ
    (GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths _ (GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector _ (GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame _ (GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM _)))) (GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof D θ V)
  refine ⟨M + 1, fun U hU => ?_⟩
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator D V U hU d hd
  obtain ⟨hm, C', hC'⟩ := GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V
  obtain ⟨-, -, -, r4, r5, r6, r7, r8⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  refine ⟨S, 1 + |C * C'|, by positivity, fun g => ?_⟩
  obtain ⟨γ, hγ, h1, h2⟩ := h g
  obtain ⟨k, hk, a, ha, e⟩ := r7 (γ * g)
  have e' : (γ * g)⁻¹ = k⁻¹ * a⁻¹ := by rw [e, ← r6 a ha k hk, _root_.mul_inv_rev]
  obtain ⟨x, hx, h3, h4⟩ := hS k hk fun i j => by
    have := h1 i j
    rwa [e', e, r8 _ _ ha, r8 _ _ (inv_mem ha)] at this
  refine ⟨γ, hγ, x, hx, a, ha, _, h3, h4, ?_, ?_⟩
  · rw [mul_assoc, r6 a ha _ h4, e, ← mul_assoc, mul_inv_cancel_left]
  · have h5 : normInf θ V a = normInf θ V (γ * g) := by
      unfold normInf
      rw [e', e]
      simp only [r4, r5 k hk, r5 _ (inv_mem hk), one_mul]
    have h6 : normInf θ V a ≤ C * C' * (height θ V g : ℝ) ^ (M + 1) := by
      rw [h5]
      refine (hm γ g).trans ((mul_le_mul h2 (hC' g) (GlobalTheory.SmoothForms.normInf_nonneg g)
        ((GlobalTheory.SmoothForms.normInf_nonneg γ).trans h2)).trans_eq ?_)
      ring
    have h7 : (1 : ℝ) ≤ (height θ V g : ℝ) ^ (M + 1) :=
      one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g)
    rw [add_mul, one_mul]
    exact add_le_add h7 (h6.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h7)))

theorem growth_pair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  intro D θ hθ V W N
  obtain ⟨M, hM⟩ := reduction_unif hθ V
  obtain ⟨M', hM'⟩ := reduction_unif hθ W
  refine ⟨(M + M') * N, ?_⟩
  rintro K hL ⟨U, U', hU, hU', hR⟩ hG
  obtain ⟨S, A, hA, hS⟩ := hM U hU
  obtain ⟨S', A', hA', hS'⟩ := hM' U' hU'
  choose C hC using hG
  refine ⟨(∑ p ∈ S ×ˢ S', |C p.1 p.2|) * (A * A') ^ N, fun g h => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk2, e, hb⟩ := hS g
  obtain ⟨δ, hδ, y, hy, b, hb', k', hk', hk2', e', hb2⟩ := hS' h
  have g1 : (1 : ℝ) ≤ (height θ V g : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g
  have h1 : (1 : ℝ) ≤ (height θ W h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ W h
  have na : 0 ≤ 1 + normInf θ V a := add_nonneg zero_le_one (GlobalTheory.SmoothForms.normInf_nonneg a)
  have nb : 0 ≤ 1 + normInf θ W b := add_nonneg zero_le_one (GlobalTheory.SmoothForms.normInf_nonneg b)
  have key : (1 + normInf θ V a) * (1 + normInf θ W b) ≤
      A * A' * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ (M + M') := by
    have p1 : (height θ V g : ℝ) ^ M ≤ (height θ V g : ℝ) ^ (M + M') := pow_le_pow_right₀ g1 (Nat.le_add_right _ _)
    have p2 : (height θ W h : ℝ) ^ M' ≤ (height θ W h : ℝ) ^ (M + M') := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    have q1 := hb.trans (mul_le_mul_of_nonneg_left p1 hA)
    have q2 := hb2.trans (mul_le_mul_of_nonneg_left p2 hA')
    refine (mul_le_mul q1 q2 nb (na.trans q1)).trans_eq ?_
    rw [mul_pow]; ring
  rw [← hL γ hγ δ hδ g h, e, e', hR k hk hk2 k' hk' hk2', pow_mul, mul_assoc, ← mul_pow]
  refine (hC x y a ha b hb').trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun p : GA D V × GA D W => |C p.1 p.2|) (fun _ _ => abs_nonneg _)
      (Finset.mk_mem_product hx hy)))
    (pow_le_pow_left₀ (mul_nonneg na nb) key N) (pow_nonneg (mul_nonneg na nb) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

end GlobalTheory.Mem.LiftGrow

end
