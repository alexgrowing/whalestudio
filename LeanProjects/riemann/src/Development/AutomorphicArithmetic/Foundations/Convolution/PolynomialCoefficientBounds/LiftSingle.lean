import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem shift_sum (g : ℕ → ℕ → ℂ) (s : ℕ → ℂ) (d : ℕ) (h0 : ∀ a, d < a → ∀ b, g a b = 0) (h : ∀ a, HasSum (g a) (s a)) :
    HasSum (fun k => ∑ b ∈ Finset.range (k + 1), g (k - b) b) (∑ a ∈ Finset.range (d + 1), s a) := by
  have h1 : ∀ a, HasSum (fun k => if a ≤ k then g a (k - a) else 0) (s a) := fun a => by
    rw [← hasSum_nat_add_iff' a, Finset.sum_eq_zero fun i hi => if_neg (not_le.2 (Finset.mem_range.1 hi)), sub_zero]
    simpa using h a
  convert hasSum_sum (s := Finset.range (d + 1)) fun a _ => h1 a using 2 with k
  rw [← Finset.sum_range_reflect, ← Finset.sum_filter]
  have e : ∀ j ∈ Finset.range (k + 1), g (k - (k + 1 - 1 - j)) (k + 1 - 1 - j) = g j (k - j) := fun j hj => by
    have := Finset.mem_range.1 hj
    congr 1
    omega
  rw [Finset.sum_congr rfl e]
  symm
  refine Finset.sum_subset (fun a ha => ?_) fun a ha hn => h0 a ?_ _
  · simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · simp only [Finset.mem_filter, Finset.mem_range] at ha hn
    omega

private theorem exp_sum {A M : Type} [CommRing A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    (φ : M →ₗ[ℂ] ℂ) (l : A) (c s : ℂ) (m : M) (h : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ (l ^ k • m)) s) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ ((algebraMap ℂ A c + l) ^ k • m)) (Complex.exp c * s) := by
  have e1 : HasSum (fun b : ℕ => (b.factorial : ℂ)⁻¹ * c ^ b) (Complex.exp c) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp c
  have s1 := (summable_norm_sum_mul_range_of_summable_norm e1.summable.norm h.summable.norm).of_norm
  have t := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm e1.summable.norm h.summable.norm
  rw [e1.tsum_eq, h.tsum_eq] at t
  rw [t]
  refine (congrArg (HasSum · _) (funext fun k => ?_)).mpr s1.hasSum
  rw [add_pow, Finset.sum_smul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
  have e : algebraMap ℂ A c ^ b * l ^ (k - b) * (k.choose b : A) = (c ^ b * k.choose b : ℂ) • l ^ (k - b) := by
    rw [Algebra.smul_def, map_mul, map_pow, map_natCast]
    ring
  have h4 : (k.factorial : ℂ) = k.choose b * b.factorial * (k - b).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hbk).symm
  have hb0 : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hc0 : (k.choose b : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hbk).ne'
  have he0 : ((k - b).factorial : ℂ) ≠ 0 := by exact_mod_cast (k - b).factorial_ne_zero
  rw [e, smul_assoc, map_smul, smul_eq_mul, h4]
  field_simp

theorem UpperTheory.ConvolutionTheory.FX.rearrange :
    PositivityTheory.Rg.Fx.Rearrange := by
  intro ι κ _ b A M _ _ _ _ _ _ D τ φ hT F m
  set ξ : ι → A := fun i => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • D j with hξ
  have hA : ∀ (f : EP ι) (m : M), HasSum (fun k => φ (aeval ξ (piece k f) • m)) (φ (lift D τ (aff b.Λ b.emb f) • m)) := by
    intro f m
    induction f using AddMonoidAlgebra.induction_linear with
    | zero =>
      simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, map_zero, zero_smul]
      exact hasSum_zero
    | add f g hf hg =>
      simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).1 f g, map_add, add_smul]
      exact hf.add hg
    | single v p =>
      set c : ℂ := ∑ i, (v i : ℂ) * b.Λ i with hc
      set t := τ (Multiplicative.ofAdd (Matrix.vecMul v b.emb)) with ht
      have hl : aeval ξ (lin v) = algebraMap ℂ A c + ∑ j, ((Matrix.vecMul v b.emb j : ℝ) : ℂ) • D j := by
        simp only [lin, map_sum, map_mul, aeval_C, aeval_X, hξ, hc, mul_add, Finset.sum_add_distrib, Matrix.vecMul, dotProduct,
          Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.mul_sum, Algebra.smul_def, mul_assoc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul, mul_assoc]
      have hp : ∀ q : MvPolynomial ι ℂ, lift D τ (aeval (fun i => (AddMonoidAlgebra.single 0 (C (b.Λ i) + lin (b.emb i)) : EP (Fin b.r))) q) =
          aeval ξ q := fun q => by
        induction q using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap, lift_single]
        | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
        | mul_X p j hp =>
          rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, lift_single]
          simp [hξ, lin, Algebra.smul_def]
      have hv : lift D τ (aff b.Λ b.emb (AddMonoidAlgebra.single v p)) = aeval ξ p * (Complex.exp c • t) := by
        rw [aff, lift_single, map_mul, hp]
        simp [affChar, expChar, lift_single, Algebra.smul_def, hc, ht]
      have h1 := shift_sum (fun a k => (k.factorial : ℂ)⁻¹ * φ (aeval ξ (lin v) ^ k • aeval ξ (homogeneousComponent a p) • m))
        (fun a => Complex.exp c * φ (t • aeval ξ (homogeneousComponent a p) • m)) p.totalDegree
        (fun a ha k => by rw [homogeneousComponent_eq_zero a p ha]; simp)
        (fun a => by rw [hl]; exact exp_sum φ _ c _ _ (hT _ _))
      convert h1 using 1
      · funext k
        rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2, map_sum, Finset.sum_smul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, aeval_C, map_pow, mul_comm, ← Algebra.smul_def, smul_mul_assoc, smul_assoc, map_smul, mul_smul,
          smul_eq_mul]
      · rw [hv, ← Finset.mul_sum, ← map_sum, ← Finset.smul_sum, ← Finset.sum_smul, ← map_sum, sum_homogeneousComponent,
          mul_comm, smul_mul_assoc, smul_assoc, map_smul, mul_smul, smul_eq_mul]
  have h2 := hasSum_sum (s := F.support) fun β _ => hA (F.coeff β) ((β.prod fun k e => lift D τ (b.h k) ^ e) • m)
  convert h2 using 1
  · funext k
    rw [pieceK, eval₂_sum, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eval₂_monomial, mul_smul]
    rfl
  · conv_lhs => rw [F.as_sum]
    rw [map_sum, map_sum, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Fam.sub, eval₂Hom_monomial, map_mul, mul_smul, map_finsuppProd]
    simp only [map_pow]
