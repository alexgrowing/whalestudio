import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.WhittakerHecke.IntegrableMulConjOfModerateGrowthOfCuspidal
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralQuotientDerivativeOneParameterEqZero
import Development.AutomorphicArithmetic.WhittakerHecke.OneParameterSubgroupNormOne
import Development.AutomorphicArithmetic.WhittakerHecke.FunctionalVanishesInvariant
import Development.AutomorphicArithmetic.WhittakerHecke.ConstantTermLeviRestrictionModerateGrowth
import Development.AutomorphicArithmetic.WhittakerHecke.FunctionalQdetEqAevalShiftedPolynomial
import Development.AutomorphicArithmetic.WhittakerHecke.IntegrableTranslateMulConjAndInnerSelfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulIncl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW UpperTheory.V.Cm

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r : ℕ}

private theorem tr_one (τ : E →+* ℂ) : ∑ σ : E →+* ℂ, coord σ (atEmb τ 1) = 2 := by
  classical
  have h1 : ∀ σ : E →+* ℂ, coord σ (atEmb τ 1) = if InfinitePlace.mk σ = InfinitePlace.mk τ then 1 else 0 := fun σ => by
    split_ifs with h
    · rw [GlobalTheory.CompanionTheory.CapelliTrace.atEmb_one]
      unfold coord
      split_ifs <;> simp [h]
    · exact GlobalTheory.IsoPull.coord_atEmb_of_ne h 1
  simp only [h1]
  rw [Finset.sum_boole, InfinitePlace.card_filter_mk_eq]
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)]

private theorem tr_I (τ : E →+* ℂ) : ∑ σ : E →+* ℂ, coord σ (atEmb τ Complex.I) = 0 := by
  classical
  have h1 : ∀ σ : E →+* ℂ, coord (ComplexEmbedding.conjugate σ) (atEmb τ Complex.I) = -coord σ (atEmb τ Complex.I) := fun σ => by
    rw [GlobalTheory.IsoPull.coord_conj]
    by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
    · unfold coord atEmb
      split_ifs <;> simp [h]
    · rw [GlobalTheory.IsoPull.coord_atEmb_of_ne h]; simp
  have hc := Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate E))
    fun σ => coord σ (atEmb τ Complex.I)
  simp only [Function.Involutive.coe_toPerm, h1, Finset.sum_neg_distrib] at hc
  linear_combination (-1 / 2 : ℂ) * hc

private theorem umg_lie (X : Lie E r) {φ : Sm E r} (h : Umg φ) : Umg (lie E r X φ) := by
  rw [← uC_ιC]; exact ((umgOps E r).2 φ h).2.2.2.1 _

private theorem cusp_uC (u : UC E r) {φ : Sm E r} (h : Umg φ) (hc : Cusp φ.1) : Cusp (uC E r u φ).1 := by
  intro a ha har g
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le har.le
  obtain ⟨F, hF, -, -, hu⟩ := ctOps E a s φ h
  have : F = 0 := Subtype.ext (hF.trans (funext (hc a ha har)))
  rw [← hu, this, map_zero]
  rfl

private theorem skew_real (hr : 0 < r) (X : Lie E r) (hX : ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) = 0) {Φ ψ : Sm E r}
    (hΦ : Umg Φ) (hψ : Umg ψ) (hc : Cusp ψ.1) : pr (lie E r X Φ).1 ψ.1 = -pr Φ.1 (lie E r X ψ).1 := by
  obtain ⟨c, c0, cadd, ccont, cder, c1⟩ := UpperTheory.one_parameter_subgroup_norm_one E r X hX
  have hΦ' := umg_lie X hΦ
  have hψ' := umg_lie X hψ
  have hc' : Cusp (lie E r X ψ).1 := by rw [← uC_ιC]; exact cusp_uC _ hψ hc
  have i1 := UpperTheory.integrable_mul_conj_of_moderateGrowth_of_cuspidal E r _ _ hr hΦ' hψ hc
  have i2 := UpperTheory.integrable_mul_conj_of_moderateGrowth_of_cuspidal E r _ _ hr hΦ hψ' hc'
  have cont : ∀ θ : Sm E r, Umg θ → Continuous θ.1 := fun θ h => ((umgOps E r).2 θ h).1
  have key := UpperTheory.integral_quotient_derivative_oneParameter_eq_zero E r (fun g => Φ.1 g * starRingEnd ℂ (ψ.1 g))
    (fun g => (lie E r X Φ).1 g * starRingEnd ℂ (ψ.1 g) + Φ.1 g * starRingEnd ℂ ((lie E r X ψ).1 g))
    (fun s => infGL E r (c s)) (fun γ g => by simp only [hΦ.left γ g, hψ.left γ g])
    (fun γ g => by simp only [hΦ.left γ g, hψ.left γ g, hΦ'.left γ g, hψ'.left γ g])
    (((cont _ hΦ').mul (Complex.continuous_conj.comp (cont _ hψ))).add
      ((cont _ hΦ).mul (Complex.continuous_conj.comp (cont _ hψ'))))
    ccont (by simp [c0]) (fun s t => by simp only [cadd, map_mul]) c1 (fun g => by
      have := (hasDerivAt_curve Φ g c X c0 cder).mul (hasDerivAt_curve ψ g c X c0 cder).star
      simp only [c0, map_one, mul_one] at this
      exact this) (UpperTheory.integrable_mul_conj_of_moderateGrowth_of_cuspidal E r _ _ hr hΦ hψ hc) (i1.add i2)
  exact eq_neg_of_add_eq_zero_left ((integral_add i1 i2).symm.trans key)

private theorem exists_form (hr : 0 < r) {Φ ψ : Sm E r} (hΦ : Umg Φ) (hψ : Umg ψ) (hc : Cusp ψ.1) :
    ∃ B : UC E r →ₗ[ℂ] UC E r →ₗ⋆[ℂ] ℂ, ∀ a a', B a a' = pr (uC E r a Φ).1 (uC E r a' ψ).1 := by
  have hi : ∀ a a', Integrable (fun y => onQ (uC E r a Φ).1 y * starRingEnd ℂ (onQ (uC E r a' ψ).1 y)) (muQ E r) :=
    fun a a' => UpperTheory.integrable_mul_conj_of_moderateGrowth_of_cuspidal E r _ _ hr (((umgOps E r).2 Φ hΦ).2.2.2.1 a) (((umgOps E r).2 ψ hψ).2.2.2.1 a') (cusp_uC a' hψ hc)
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a a' => pr (uC E r a Φ).1 (uC E r a' ψ).1)
    (fun a b a' => ?_) (fun c a a' => ?_) (fun a a' b' => ?_) (fun c a a' => ?_), fun _ _ => rfl⟩
  · refine Eq.trans ?_ (integral_add (hi a a') (hi b a'))
    simp only [pr, onQ, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, add_mul]
  · refine Eq.trans ?_ (integral_const_mul c _)
    simp only [pr, onQ, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · refine Eq.trans ?_ (integral_add (hi a a') (hi a b'))
    simp only [pr, onQ, map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, mul_add]
  · refine Eq.trans ?_ (integral_const_mul (starRingEnd ℂ c) _)
    simp only [pr, onQ, map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]

variable (E r) in

private noncomputable def zL : Lie E r := ((r * Module.finrank ℚ E : ℕ) : ℝ)⁻¹ • oneL E r

omit [IsTotallyComplex E] in
private theorem coord_zL (τ : E →+* ℂ) (i k : Fin r) :
    coord τ (zL E r i k) = if i = k then ((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ else 0 := by
  have : zL E r i k = ((r * Module.finrank ℚ E : ℕ) : ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) (Cinf E)) i k := rfl
  rw [this, GlobalTheory.IsoPull.coord_smul, Matrix.one_apply]
  split_ifs <;> simp

private theorem uC_zL : uC E r (ιC E r (zL E r)) = j0 E r := by
  rw [uC_ιC, lie_eq_sum, j0]
  simp only [coord_zL, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.smul_sum]

private theorem tr_zL (hr : 0 < r) : ∑ τ : E →+* ℂ, ∑ i, coord τ (zL E r i i) = 1 := by
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  simp only [coord_zL, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, NumberField.Embeddings.card, nsmul_eq_mul]
  have h1 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have h2 : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  push_cast
  field_simp

private theorem comm_zL (X : Lie E r) : Commute (ιC E r X) (ιC E r (zL E r)) := by
  have h := isLieHom_ιC (E := E) (a := r) (Matrix.of X) 1
  rw [mul_one, one_mul, sub_self] at h
  have h0 : ιC E r (toL 0) = 0 := map_zero _
  rw [h0, sub_eq_zero] at h
  rw [zL, map_smul]
  exact Commute.smul_right h _

private theorem comm_gen (τ : E →+* ℂ) (i k : Fin r) : Commute (genC τ i k) (ιC E r (zL E r)) :=
  ((comm_zL _).sub_left ((comm_zL _).smul_left _)).smul_left _

private noncomputable def gz (τ : E →+* ℂ) (i k : Fin r) : UC E r := genC τ i k - if i = k then ιC E r (zL E r) else 0

private theorem gz_eq (hr : 0 < r) (τ : E →+* ℂ) (i k : Fin r) : ∃ X Y : Lie E r,
    ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) = 0 ∧ ∑ τ : E →+* ℂ, ∑ i, coord τ (Y i i) = 0 ∧
    gz τ i k = (1 / 2 : ℂ) • (ιC E r X - Complex.I • ιC E r Y) ∧
    gz (ComplexEmbedding.conjugate τ) i k = (1 / 2 : ℂ) • (ιC E r X + Complex.I • ιC E r Y) := by
  have hs : ∀ x : Cinf E, ∑ σ : E →+* ℂ, ∑ l, coord σ (toL (Matrix.single i k x) l l) =
      if i = k then ∑ σ : E →+* ℂ, coord σ x else 0 := fun x => by
    have : ∀ l, toL (Matrix.single i k x) l l = if i = l ∧ k = l then x else 0 := fun l => rfl
    simp only [this]
    split_ifs with h
    · subst h; simp [apply_ite]
    · have : ∀ l, ¬(i = l ∧ k = l) := fun l hl => h (hl.1.trans hl.2.symm)
      simp [this]
  have e : toL (Matrix.single i k (atEmb τ (-Complex.I))) = -toL (Matrix.single i k (atEmb τ Complex.I)) := by
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
    rw [e, ← Matrix.single_neg]; rfl
  refine ⟨toL (Matrix.single i k (atEmb τ 1)) - if i = k then zL E r + zL E r else 0,
    toL (Matrix.single i k (atEmb τ Complex.I)), ?_, ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib, hs, tr_one]
    split_ifs
    · simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, tr_zL hr]; norm_num
    · simp
  · rw [hs, tr_I, ite_self]
  · rw [gz, genC, UpperTheory.V.AlgRepEndIrreducible.eL, map_sub]
    split_ifs
    · rw [map_add]; module
    · simp
  · rw [gz, genC, UpperTheory.V.AlgRepEndIrreducible.eL, map_sub, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
    split_ifs
    · rw [map_add]; module
    · simp

private theorem glRel_gz (τ : E →+* ℂ) : Formalism.REAL.GlRel (gz (r := r) τ) := by
  intro a b c d
  have h := glRel_genC (a := r) τ a b c d
  have hz : ∀ (p : Prop) [Decidable p] (i k : Fin r), Commute (genC τ i k) (if p then ιC E r (zL E r) else 0) := fun p _ i k => by
    split_ifs
    exacts [comm_gen τ i k, Commute.zero_right _]
  have h3 : Commute (if a = b then ιC E r (zL E r) else 0) (if c = d then ιC E r (zL E r) else 0) := by
    split_ifs <;> simp
  unfold gz
  simp only [mul_sub, sub_mul, (hz (c = d) a b).eq, (hz (a = b) c d).eq, h3.eq]
  rw [show ∀ x y p q s : UC E r, x - p - (q - s) - (y - q - (p - s)) = x - y from fun _ _ _ _ _ => by abel, h]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, eq_comm, Ne.symm]

private theorem qdet_gz (τ : E →+* ℂ) (v : ℂ) {f : Sm E r} (hf : j0 E r f = 0) :
    uC E r (Formalism.REAL.qdet (gz τ) v) f = cap τ (v - ((r : ℂ) - 1) / 2) f := by
  have h := GlobalTheory.GLSlice.rel_aeval_qdet
    (LinearMap.ker (LinearMap.fst ℂ (Sm E r) (Sm E r) - LinearMap.snd ℂ _ _) ⊓ (LinearMap.ker (j0 E r)).comap (LinearMap.snd ℂ _ _))
    (fun i k => uC E r (gz τ i k)) (Eop τ) (fun i k x hx => ?_) v Polynomial.X (f, f) ⟨by simp, hf⟩
  · have h1 := h.1
    simp only [Polynomial.aeval_X, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, sub_eq_zero] at h1
    rw [UpperTheory.V.Fb.map_qdet, h1, cap, sub_add_cancel]
  · obtain ⟨x, y⟩ := x
    obtain ⟨h1, h2⟩ := hx
    obtain rfl : x = y := sub_eq_zero.1 h1
    have h2 : j0 E r x = 0 := h2
    refine ⟨sub_eq_zero.2 ?_, ?_⟩
    · change uC E r (gz τ i k) x = Eop τ i k x
      rw [gz, map_sub, uC_genC, apply_ite (uC E r), uC_zL, map_zero, LinearMap.sub_apply]
      split_ifs <;> simp [h2]
    · change j0 E r (Eop τ i k x) = 0
      rw [← uC_zL, ← uC_genC, ← Module.End.mul_apply, ← map_mul, ← (comm_gen τ i k).eq, map_mul, Module.End.mul_apply, uC_zL,
        h2, map_zero]

private theorem adj {S : Set (Pl E)} (b : Blo S r) (τ : E →+* ℂ) (c : ℂ) : ∃ κ : ℂ, ∀ Φ : Sm E r, Umg Φ → ∀ a : UC E r,
    pr (uC E r (Formalism.REAL.qdet (gz τ) c * a) Φ).1 b.f.1 = κ * pr (uC E r a Φ).1 b.f.1 := by
  obtain ⟨hf, hc⟩ := cuspUmg E r b.f b.cusp
  refine ⟨starRingEnd ℂ ((-1) ^ r * ∏ i, ((r : ℂ) - 1 - starRingEnd ℂ c - ((r : ℂ) - 1) / 2 +
    b.Λ (ComplexEmbedding.conjugate τ) i)), fun Φ hΦ a => ?_⟩
  obtain ⟨B, hB⟩ := exists_form b.pos hΦ hf hc
  have hreal : ∀ X : Lie E r, ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) = 0 → ∀ a a',
      B (ιC E r X * a) a' = -B a (ιC E r X * a') := fun X hX a a' => by
    rw [hB, hB, map_mul, map_mul, uC_ιC]
    exact skew_real b.pos X hX (((umgOps E r).2 Φ hΦ).2.2.2.1 a) (((umgOps E r).2 _ hf).2.2.2.1 a') (cusp_uC a' hf hc)
  have h := GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet (UC E r) B r (fun i k => Algebra.lmul ℂ _ (gz τ i k))
    (fun i k => Algebra.lmul ℂ _ (gz (ComplexEmbedding.conjugate τ) i k)) (fun i k l m => by
      have := congrArg (Algebra.lmul ℂ (UC E r)) (glRel_gz (ComplexEmbedding.conjugate τ) i k l m)
      simpa only [map_sub, map_mul, apply_ite (Algebra.lmul ℂ (UC E r)), map_zero] using this) (fun i k a a' => by
      obtain ⟨X, Y, hX, hY, e1, e2⟩ := gz_eq b.pos τ i k
      change B (gz τ i k * a) a' = -B a (gz (ComplexEmbedding.conjugate τ) i k * a')
      rw [e1, e2]
      simp only [smul_mul_assoc, sub_mul, add_mul, map_smul, map_sub, map_add, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        LinearMap.sub_apply, hreal X hX, hreal Y hY, smul_eq_mul, Complex.conj_I, map_div₀, map_one, Complex.conj_ofNat]
      ring) c a 1
  rw [← UpperTheory.V.Fb.map_qdet, ← UpperTheory.V.Fb.map_qdet, hB, hB, map_one] at h
  refine h.trans ?_
  have e : ∀ (z : ℂ) (x : UC E r), (z • Algebra.lmul ℂ (UC E r) x) 1 = z • x := fun z x => congrArg (z • ·) (mul_one x)
  rw [e, map_smul, LinearMap.smul_apply, qdet_gz _ _ (UpperTheory.functional_vanishes_invariant E r b.f b.cen), b.inf, smul_smul]
  refine Eq.trans ?_ (integral_const_mul _ _)
  simp only [pr, onQ, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]

private theorem core {S : Set (Pl E)} (b : Blo S r) (τ : E →+* ℂ) (u : ℂ) {Φ : Sm E r} (hΦ : Umg Φ) :
    pr (cap τ u Φ).1 b.f.1 =
      pr (Polynomial.aeval (j0 E r) (∏ i, (Polynomial.X + Polynomial.C (u + b.Λ τ i))) Φ).1 b.f.1 := by
  obtain ⟨hf, hc⟩ := cuspUmg E r b.f b.cusp
  obtain ⟨B, hB⟩ := exists_form b.pos hΦ hf hc
  have hl : ∀ a, B.flip 1 a = pr (uC E r a Φ).1 b.f.1 := fun a => by
    rw [LinearMap.flip_apply, hB, map_one]; rfl
  have h := UpperTheory.functional_qdet_eq_aeval_shifted_polynomial (UC E r) r (genC τ) (ιC E r (zL E r)) (B.flip 1)
    (∏ i, (Polynomial.X + Polynomial.C (b.Λ τ i - ((r : ℂ) - 1) / 2))) (comm_gen τ) (fun c a => by
      obtain ⟨κ, hκ⟩ := adj b τ c
      have h1 := hκ b.f hf 1
      rw [mul_one, map_one, qdet_gz _ _ (UpperTheory.functional_vanishes_invariant E r b.f b.cen), b.inf] at h1
      have h2 : ∀ z : ℂ, pr (z • b.f).1 b.f.1 = z * pr b.f.1 b.f.1 := fun z => by
        refine Eq.trans ?_ (integral_const_mul _ _)
        simp only [pr, onQ, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [h2] at h1
      have h3 := mul_right_cancel₀ (UpperTheory.integrable_translate_mul_conj_and_inner_self_ne_zero E S r b).2 h1
      rw [hl, hl]
      refine (hκ Φ hΦ a).trans ?_
      rw [← h3, Polynomial.eval_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      ring) (u + ((r : ℂ) - 1) / 2)
  rw [hl, hl, ← Polynomial.aeval_algHom_apply, uC_zL] at h
  have e : (∏ i, (Polynomial.X + Polynomial.C (b.Λ τ i - ((r : ℂ) - 1) / 2))).comp
      (Polynomial.X + Polynomial.C (u + ((r : ℂ) - 1) / 2)) = ∏ i, (Polynomial.X + Polynomial.C (u + b.Λ τ i)) := by
    rw [Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, add_assoc, ← Polynomial.C_add]
    congr 2
    ring
  rw [e] at h
  rw [← uC_capC]
  exact h

private theorem embGL_eq {R : Type} [CommRing R] (r s : ℕ) (g : GL (Fin r) R) :
    GlobalTheory.GLSlice.embGL (Fin.castAddEmb s) g = lev R r s (g, 1) := by
  have hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  have hne : ∀ (b : Fin s) (a : Fin r), Fin.castAddEmb s a ≠ Fin.natAdd r b := fun b a h => by
    have := congrArg Fin.val h
    have := a.isLt
    simp at *
    omega
  refine Units.ext ?_
  rw [GlobalTheory.GLSlice.embGL_val, lev, GlobalTheory.SmGL.val_emb₂, hs]
  ext a b
  induction a using Fin.addCases with
  | left a =>
    induction b using Fin.addCases with
    | left b =>
      have h := fun X => GlobalTheory.GLSlice.extN_apply_apply (R := R) (Fin.castAddEmb s) X a b
      simp only [Fin.castAddEmb_apply] at h
      simp [h, Matrix.one_apply]
    | right b =>
      have h := fun X => GlobalTheory.GLSlice.extN_apply_right (R := R) (Fin.castAddEmb s) X (Fin.castAdd s a) (hne b)
      have := hne b a
      simp only [Fin.castAddEmb_apply] at this
      simp [h, Matrix.one_apply, this]
  | right a =>
    have h := fun X => GlobalTheory.GLSlice.extN_apply_left (R := R) (Fin.castAddEmb s) X (hne a) b
    induction b using Fin.addCases with
    | left b =>
      have := (hne a b).symm
      simp only [Fin.castAddEmb_apply] at this
      simp [h, Matrix.one_apply, this]
    | right b => simp [h, Matrix.one_apply]

end

theorem UpperTheory.ConvolutionTheory.BW.sliceCapR :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceCapR E := by
  intro E _ _ _ S r s b t φ τ u hφ
  funext m
  obtain ⟨F, hF, -, -, hu⟩ := ctOps E r s φ hφ
  set ρ := GlobalTheory.GLSlice.slice (Fin.castAddEmb s) (lev (Ad E) r s (zt E r t, m))
  have hρ : ∀ (G : Sm E (r + s)) g, (ρ G).1 g = G.1 (lev (Ad E) r s (zt E r t * g, m)) := fun G g => by
    rw [GlobalTheory.GLSlice.slice_apply, embGL_eq, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hs : ∀ a, slice b.f.1 t (uC E (r + s) a φ).1 m = pr (ρ (uC E (r + s) a F)).1 b.f.1 := fun a => by
    simp only [slice, pr, onQ, hρ, hu]
  have hΦ : Umg (ρ F) := UpperTheory.constantTerm_leviRestriction_moderateGrowth E r s φ _ (zt E r t) m b.pos hφ (fun γ => centralSection_mul_comm _ _)
    fun g => by rw [hρ, hF]
  have e1 : capR r s τ u = uC E (r + s) (Formalism.REAL.qdet (fun i k : Fin r => genC τ (Fin.castAdd s i) (Fin.castAdd s k))
      (u + ((r : ℂ) - 1) / 2)) := by
    rw [UpperTheory.V.Fb.map_qdet]; simp only [uC_genC]; rfl
  have e2 : j1 E r s = uC E (r + s) (((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ •
      ∑ τ : E →+* ℂ, ∑ i : Fin r, genC τ (Fin.castAdd s i) (Fin.castAdd s i)) := by
    simp only [map_smul, map_sum, uC_genC]; rfl
  have h1 : ρ (capR r s τ u F) = cap τ u (ρ F) := by
    have := GlobalTheory.GLSlice.aeval_qdet_slice (Fin.castAddEmb s) (lev (Ad E) r s (zt E r t, m)) F τ (u + ((r : ℂ) - 1) / 2) Polynomial.X
    simp only [Polynomial.aeval_X] at this
    exact this.symm
  have h2 : ∀ G, ρ (j1 E r s G) = j0 E r (ρ G) := fun G => by
    simp only [j1, j0, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, ρ, GlobalTheory.GLSlice.Eop_slice,
      Fin.castAddEmb_apply]
  have h3 : ∀ (P : Polynomial ℂ) G, ρ (Polynomial.aeval (j1 E r s) P G) = Polynomial.aeval (j0 E r) P (ρ G) := fun P => by
    induction P using Polynomial.induction_on with
    | C a => intro G; simp
    | add p q hp hq => intro G; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n a h =>
      intro G
      simp only [pow_succ, ← mul_assoc, map_mul _ _ Polynomial.X, Polynomial.aeval_X, Module.End.mul_apply, h, h2]
  have h4 := hs (Polynomial.aeval (((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ •
      ∑ τ : E →+* ℂ, ∑ i : Fin r, genC τ (Fin.castAdd s i) (Fin.castAdd s i))
      (∏ i, (Polynomial.X + Polynomial.C (u + b.Λ τ i))))
  rw [← Polynomial.aeval_algHom_apply, ← e2, h3] at h4
  rw [h4, ← core b τ u hΦ, ← h1, e1, hs]
