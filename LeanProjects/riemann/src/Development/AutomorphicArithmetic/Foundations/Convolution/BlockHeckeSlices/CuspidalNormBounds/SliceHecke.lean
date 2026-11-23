import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
import Development.AutomorphicArithmetic.WhittakerHecke.IntegrableConstantTermLeviEmbeddingMulConjCuspFo
import Development.AutomorphicArithmetic.WhittakerHecke.DetModuleSatakeTsetEqInvPow
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsSatakeTsetSumEigenvector
import Development.AutomorphicArithmetic.WhittakerHecke.IntegrableTranslateMulConjAndInnerSelfNeZero
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralQuotientRightTranslateEqAndIntegrableIff
import Development.AutomorphicArithmetic.WhittakerHecke.BlockDiagonalEqLeviEmbedding
import Development.AutomorphicArithmetic.WhittakerHecke.ConstantTermHeckeOperatorEqSumSatake

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
variable {E : Type} [Field E] [NumberField E] {r : ℕ}

private theorem zt_add (t v : ℝ) : zt E r (t + v) = zt E r t * zt E r v := by
  unfold zt
  rw [← map_mul]
  congr 1
  exact Subtype.ext (Real.exp_add t v)

private theorem zt_comm (t : ℝ) (g : GA E r) : zt E r t * g = g * zt E r t := centralSection_mul_comm _ g

private theorem tset_rel {w : Pl E} {ϖ : w.adicCompletion E} {a : ℕ} {x x' : GL (Fin r) (w.adicCompletion E)}
    (h : x ∈ satakeTset w ϖ a) (h' : x' ∈ satakeTset w ϖ a) : ∃ k ∈ KGL w r, ∃ k' ∈ KGL w r, x' = k * x * k' := by
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h
  obtain ⟨l₁, g₁, l₂, g₂, e'⟩ := h'
  refine ⟨l₁ * k₁⁻¹, mul_mem g₁ (inv_mem h₁), k₂⁻¹ * l₂, mul_mem (inv_mem h₂) g₂, Units.ext ?_⟩
  simp only [Units.val_mul, e, e', mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]

variable [IsTotallyComplex E] {S : Set (Pl E)}

private theorem move (b : Blo S r) {w : Pl E} {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {a : ℕ} (ha : a ≤ r)
    {Φ : GA E r → ℂ} (hΦ : AutomorphicForm.IsLeftInvariant Φ) (t : ℝ) {x : GL (Fin r) (w.adicCompletion E)}
    (hx : x ∈ satakeTset w ϖ a) :
    (∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) *
        finGL E r (locGL E r w x)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) =
      ∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r (t - a * Real.log (qV E w)) *
        ((Quotient.out y : normOneGL E r) : GA E r)) *
        starRingEnd ℂ (b.f.1 (((Quotient.out y : normOneGL E r) : GA E r) * finGL E r (locGL E r w x⁻¹)))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r))) ∧
    (Integrable (fun y : RightCosetSpace (rationalGLOne E r) => Φ (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) *
        finGL E r (locGL E r w x)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)))
        (quotientMeasure (rationalGLOne E r) (mu1 E r)) ↔
      Integrable (fun y : RightCosetSpace (rationalGLOne E r) => Φ (zt E r (t - a * Real.log (qV E w)) *
        ((Quotient.out y : normOneGL E r) : GA E r)) *
        starRingEnd ℂ (b.f.1 (((Quotient.out y : normOneGL E r) : GA E r) * finGL E r (locGL E r w x⁻¹))))
        (quotientMeasure (rationalGLOne E r) (mu1 E r))) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast Nat.pos_of_ne_zero (qV_ne_zero w)
  have hg : zt E r (a * Real.log (qV E w)) * finGL E r (locGL E r w x) ∈ normOneGL E r := by
    rw [mem_normOneGL_iff_detModule, map_mul, zt, detModule_centralSection b.pos]
    refine Subtype.ext ?_
    rw [Positive.val_mul, UpperTheory.detModule_satakeTset_eq_inv_pow E w r a ϖ hu ha x hx]
    change Real.exp _ * _ = 1
    rw [Real.exp_nat_mul, Real.exp_log hq]
    exact mul_inv_cancel₀ (pow_ne_zero _ hq.ne')
  have hl : AutomorphicForm.IsLeftInvariant b.f.1 := b.cusp.1.isLeftInvariant
  have := UpperTheory.integral_quotient_rightTranslate_eq_and_integrable_iff E r (fun y => Φ (zt E r (t - a * Real.log (qV E w)) * y) *
    starRingEnd ℂ (b.f.1 (y * finGL E r (locGL E r w x⁻¹)))) (fun γ g => by
      beta_reduce
      rw [← mul_assoc, zt_comm, mul_assoc, hΦ, mul_assoc, hl]) _ hg
  have e1 : ∀ y : GA E r, zt E r (t - a * Real.log (qV E w)) * (y * (zt E r (a * Real.log (qV E w)) *
      finGL E r (locGL E r w x))) = zt E r t * y * finGL E r (locGL E r w x) := fun y => by
    rw [← mul_assoc y, ← zt_comm, ← mul_assoc, ← mul_assoc, ← zt_add, sub_add_cancel]
  have e2 : ∀ y : GA E r, b.f.1 (y * (zt E r (a * Real.log (qV E w)) * finGL E r (locGL E r w x)) *
      finGL E r (locGL E r w x⁻¹)) = b.f.1 y := fun y => by
    rw [map_inv, map_inv, ← mul_assoc y, ← zt_comm, mul_inv_cancel_right, b.cen]
  simpa only [e1, e2] using this

private theorem kappa (b : Blo S r) {w : Pl E} (hw : w ∉ S) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {a : ℕ}
    (ha : a ≤ r) : ∃ κ : ℂ, ∀ Φ : GA E r → ℂ, AutomorphicForm.IsLeftInvariant Φ →
    (∀ k ∈ KGL w r, ∀ g, Φ (g * finGL E r (locGL E r w k)) = Φ g) →
    (∀ g : GA E r, Integrable (fun y : RightCosetSpace (rationalGLOne E r) =>
      Φ (((Quotient.out y : normOneGL E r) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)))
      (quotientMeasure (rationalGLOne E r) (mu1 E r))) → ∀ t : ℝ, ∀ x ∈ satakeTset (n := r) w ϖ a,
    ∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) *
        finGL E r (locGL E r w x)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) =
      κ * ∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r (t - a * Real.log (qV E w)) *
        ((Quotient.out y : normOneGL E r) : GA E r)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) := by
  obtain ⟨n, c, μ, hn, hc, hs⟩ := UpperTheory.exists_satakeTset_sum_eigenvector E w r a ϖ hu ha _ (rw r w) b.f _ (b.isSat w hw)
  have hf : ∀ k ∈ KGL w r, ∀ g, b.f.1 (g * finGL E r (locGL E r w k)) = b.f.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 (b.isSat w hw).2.1 k hk)) g
  have hs' : ∀ g, ∑ i, b.f.1 (g * finGL E r (locGL E r w (c i))) = μ * b.f.1 g := fun g => by
    have := congrFun (congrArg Subtype.val hs) g
    rw [Submodule.coe_sum, Finset.sum_apply] at this
    exact this
  refine ⟨(n : ℂ)⁻¹ * starRingEnd ℂ μ, fun Φ hΦ hK hI t x hx => ?_⟩
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : ∀ i, ∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) *
        finGL E r (locGL E r w x)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) =
      ∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r (t - a * Real.log (qV E w)) *
        ((Quotient.out y : normOneGL E r) : GA E r)) *
        starRingEnd ℂ (b.f.1 (((Quotient.out y : normOneGL E r) : GA E r) * finGL E r (locGL E r w (c i))))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) := fun i => by
    obtain ⟨k, hk, k', hk', rfl⟩ := tset_rel (hc i) hx
    have := (move b hu ha hΦ t (satake_Tset_left w (hc i) hk)).1
    simp only [mul_inv_rev, inv_inv, map_mul _ (c i), map_mul _ (locGL E r w (c i)), ← mul_assoc, hf _ (inv_mem hk)] at this
    simp only [map_mul _ _ k', map_mul _ _ (locGL E r w k'), ← mul_assoc, hK _ hk']
    exact this
  have h2 : ∀ i, Integrable (fun y : RightCosetSpace (rationalGLOne E r) => Φ (zt E r (t - a * Real.log (qV E w)) *
        ((Quotient.out y : normOneGL E r) : GA E r)) *
        starRingEnd ℂ (b.f.1 (((Quotient.out y : normOneGL E r) : GA E r) * finGL E r (locGL E r w (c i)))))
        (quotientMeasure (rationalGLOne E r) (mu1 E r)) := fun i => by
    have := (move b hu ha hΦ t (hc i)).2.1 (by
      simpa only [zt_comm t, mul_assoc] using hI (zt E r t * finGL E r (locGL E r w (c i)⁻¹)))
    simpa only [inv_inv] using this
  have h3 := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n)) = _) fun i _ => h1 i
  rw [← integral_finset_sum _ fun i _ => h2 i] at h3
  simp only [← Finset.mul_sum, ← map_sum, hs', map_mul, mul_left_comm _ (starRingEnd ℂ μ), integral_const_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  rw [mul_assoc, ← h3, inv_mul_cancel_left₀ hn']

private theorem adj (b : Blo S r) {w : Pl E} (hw : w ∉ S) {ϖ : w.adicCompletion E} (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ)
    [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] {a : ℕ} (ha : a ≤ r) (Φ : GA E r → ℂ) (hΦ : AutomorphicForm.IsLeftInvariant Φ)
    (hK : ∀ k ∈ KGL w r, ∀ g, Φ (g * finGL E r (locGL E r w k)) = Φ g)
    (hI : ∀ g : GA E r, Integrable (fun y : RightCosetSpace (rationalGLOne E r) =>
      Φ (((Quotient.out y : normOneGL E r) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)))
      (quotientMeasure (rationalGLOne E r) (mu1 E r))) (t : ℝ) :
    ∑ i : SatakeIdx w hϖ (n := r) a, ∫ y : RightCosetSpace (rationalGLOne E r),
        Φ (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) * finGL E r (locGL E r w (satakeB w hϖ hu i))) *
        starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)) ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) =
      satEig (qV E w) r (b.sat w) a * ∫ y : RightCosetSpace (rationalGLOne E r), Φ (zt E r (t - a * Real.log (qV E w)) *
        ((Quotient.out y : normOneGL E r) : GA E r)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))
        ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) := by
  obtain ⟨κ, hκ⟩ := kappa b hw hu ha
  obtain ⟨hi, h0⟩ := UpperTheory.integrable_translate_mul_conj_and_inner_self_ne_zero E S r b
  obtain ⟨-, hfix, -, heig⟩ := b.isSat w hw
  have hf : ∀ k ∈ KGL w r, ∀ g, b.f.1 (g * finGL E r (locGL E r w k)) = b.f.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hfix k hk)) g
  have hs : ∀ g, ∑ i : SatakeIdx w hϖ (n := r) a, b.f.1 (g * finGL E r (locGL E r w (satakeB w hϖ hu i))) =
      satEig (qV E w) r (b.sat w) a * b.f.1 g := fun g => by
    have := congrFun (congrArg Subtype.val
      ((UpperTheory.V.Cj.S.hkSum E w r _ (rw r w) ϖ hϖ hu a ha b.f hfix).symm.trans (heig ϖ hu a ha))) g
    rw [Submodule.coe_sum, Finset.sum_apply] at this
    exact this
  have h1 := Finset.sum_congr (rfl : (Finset.univ : Finset (SatakeIdx w hϖ (n := r) a)) = _) fun i _ =>
    hκ b.f.1 b.cusp.1.isLeftInvariant hf hi 0 _ (satakeB_mem w hϖ hu i)
  simp only [mul_assoc, b.cen] at h1
  rw [← integral_finset_sum _ fun i _ => hi _] at h1
  simp only [← Finset.sum_mul, hs, mul_assoc, integral_const_mul] at h1
  rw [Finset.sum_congr rfl fun i _ => hκ Φ hΦ hK hI t _ (satakeB_mem w hϖ hu i), ← Finset.sum_mul,
    ← mul_right_cancel₀ h0 h1]

end

private theorem reidx (r s j : ℕ) (G : ℕ → ℕ → ℂ) (hG : ∀ a, r < a → ∀ c, G a c = 0) :
    ∑ p : Fin (r + 1) × Fin (s + 1), (if (p.1 : ℕ) + p.2 = j then G p.1 p.2 else 0) =
      ∑ a ∈ (Finset.range (j + 1)).filter fun a => j - a ≤ s, G a (j - a) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter_of_ne (s := (Finset.range (j + 1)).filter fun a => j - a ≤ s)
    (p := fun a => a ≤ r) fun a _ h => not_lt.1 fun h' => h (hG a h' _)]
  refine Finset.sum_bij (fun p _ => (p.1 : ℕ)) (fun p hp => ?_) (fun p hp p' hp' e => ?_) (fun a ha => ?_) fun p hp => ?_
  · have := p.1.2
    have := p.2.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hp ⊢
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp' e
    exact Prod.ext (Fin.ext e) (Fin.ext (by omega))
  · simp only [Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨(⟨a, by omega⟩, ⟨j - a, by omega⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [← hp, Nat.add_sub_cancel_left]

theorem UpperTheory.ConvolutionTheory.BW.sliceHecke :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceHecke E := by
  intro E _ _ _ S r s b t φ ψ w j hU hS hw hj hψ
  have hu := (exists_isUnifV w).choose_spec
  have hϖ := mem_Ov_of_isUnifV hu
  have := satake_res_finite w hϖ hu
  letI : Fintype (satakeRes (Ov E w) ⟨_, hϖ⟩) := Fintype.ofFinite _
  have hq : (qV E w : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (qV_ne_zero w)
  obtain ⟨F, hF, -, hL, -⟩ := ctOps E r s φ hU
  have hψS : ∀ v, ψ v ∈ GlobalTheory.PRep.fixed (rw s w) (KGL w s) := fun v => by
    obtain ⟨ψ', h1, -, -, -, h2, -⟩ := sliceUmg E S r s b v φ hU
    rw [Subtype.ext ((hψ v).trans h1.symm)]
    exact GlobalTheory.LGrp.mem_fixed.2 (h2 hS w hw)
  have hl : ∀ m : GA E s, AutomorphicForm.IsLeftInvariant
      fun g : GA E r => AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (g, m)) := fun m γ g => by
    have := hL (γ, 1) (lev (Ad E) r s (g, m))
    rw [← map_mul, hF, map_one, Prod.mk_mul_mk, one_mul] at this
    exact this
  have hK : ∀ m : GA E s, ∀ k ∈ KGL w r, ∀ g : GA E r,
      AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (g * finGL E r (locGL E r w k), m)) =
        AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (g, m)) := fun m k hk g => by
    obtain ⟨b1, -, -, b4⟩ := UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding E w r s
    have e : ∀ x, φ.1 (x * finGL E _ (locGL E _ w (UpperTheory.V.Af.Fin.blk k 1))) = φ.1 x :=
      congrFun (congrArg Subtype.val (hS w hw _ (b4 k hk 1 (one_mem _))))
    rw [b1, map_one, map_one, UpperTheory.blockDiagonal_eq_leviEmbedding] at e
    have e' : lev (Ad E) r s (g * finGL E r (locGL E r w k), m) =
        lev (Ad E) r s (g, m) * lev (Ad E) r s (finGL E r (locGL E r w k), 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [AutomorphicForm.constantTerm, e', ← mul_assoc, e]
  funext m
  have hI : ∀ (g : GA E r) (m : GA E s), Integrable (fun y : RightCosetSpace (rationalGLOne E r) =>
      AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) * g, m)) *
        starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r)))
      (quotientMeasure (rationalGLOne E r) (mu1 E r)) := fun g m => by
    simpa only [zt_comm t, mul_assoc] using UpperTheory.integrable_constantTerm_leviEmbedding_mul_conj_cuspForm E S r s b φ hU (zt E r t * g) m
  have h1 : ∀ p : Fin (r + 1) × Fin (s + 1), ∫ y : RightCosetSpace (rationalGLOne E r),
      (∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
        AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r) *
          finGL E r (locGL E r w (satakeB w hϖ hu i₁)), m * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))) *
        starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))) ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) =
      satEig (qV E w) r (b.sat w) p.1 * (qc w ^ ((((p.2 : ℕ) : ℂ) * ((s : ℂ) - (p.2 : ℕ))) / 2) *
        (hk s w p.2 (ψ (t - (p.1 : ℕ) * Real.log (qV E w)))).1 m) := fun p => by
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun i' _ => hI _ _]
    simp only [fun i => integral_finset_sum (Finset.univ : Finset (SatakeIdx w hϖ (n := s) p.2))
      fun i' _ => hI (finGL E r (locGL E r w (satakeB w hϖ hu (j := p.1) i)))
        (m * finGL E s (locGL E s w (satakeB w hϖ hu i')))]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => adj b hw hϖ hu (Nat.lt_succ_iff.1 p.1.2) _ (hl _) (hK _)
      (fun g => UpperTheory.integrable_constantTerm_leviEmbedding_mul_conj_cuspForm E S r s b φ hU g _) t, ← Finset.mul_sum, (hkOps E s w p.2).1,
      UpperTheory.V.Cj.S.hkSum E w s _ (rw s w) _ hϖ hu _ (Nat.lt_succ_iff.1 p.2.2) _ (hψS _), Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, mul_inv_cancel_left₀ (fun h => hq ((Complex.cpow_eq_zero_iff _ _).1 h).1), Submodule.coe_sum,
      Finset.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    exact (congrFun (hψ _) _).symm
  rw [(hkOps E (r + s) w j).1, Submodule.coe_smul, slice]
  simp only [AutomorphicForm.constantTerm_smul, UpperTheory.constantTerm_heckeOperator_eq_sum_satake E r s w _ hϖ hu j hj φ hU (hS w hw), smul_eq_mul, mul_assoc,
    Finset.sum_mul, integral_const_mul]
  rw [integral_finset_sum _ fun p _ => (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun i' _ => by
    simpa only [mul_assoc] using hI _ _).const_mul _]
  simp only [integral_const_mul, ← mul_assoc (zt E r t), h1]
  rw [Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun p _ => ?_) ((reidx r s j (fun a c =>
    (((b.sat w).map fun x : ℂˣ => (x : ℂ)).esymm a * qc w ^ (((s : ℂ) * a - (r : ℂ) * ((j : ℂ) - a)) / 2)) *
      (hk s w c (ψ (t - a * Real.log (qV E w)))).1 m) fun a ha c => ?_).trans rfl)
  · rw [UpperTheory.V.Cj.S.coef]
    split_ifs with h
    · have key : qc w ^ (((s : ℂ) * (p.1 : ℕ) - (r : ℂ) * ((j : ℂ) - (p.1 : ℕ))) / 2) =
          (qc w ^ (((j : ℂ) * (((r + s : ℕ) : ℂ) - j)) / 2))⁻¹ * (qV E w : ℂ) ^ ((p.1 : ℕ) * (s - p.2)) *
          qc w ^ ((((p.1 : ℕ) : ℂ) * ((r : ℂ) - (p.1 : ℕ))) / 2) * qc w ^ ((((p.2 : ℕ) : ℂ) * ((s : ℂ) - (p.2 : ℕ))) / 2) := by
        rw [← Complex.cpow_neg, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq,
          ← Complex.cpow_add _ _ hq, ← h]
        congr 1
        push_cast [Nat.cast_sub (Nat.lt_succ_iff.1 p.2.2)]
        ring
      rw [key, satEig]
      ring
    · simp
  · rw [Multiset.esymm, Multiset.powersetCard_eq_empty, Multiset.map_zero, Multiset.sum_zero, zero_mul, zero_mul]
    rw [Multiset.card_map, (b.isSat w hw).2.2.1]
    exact ha
