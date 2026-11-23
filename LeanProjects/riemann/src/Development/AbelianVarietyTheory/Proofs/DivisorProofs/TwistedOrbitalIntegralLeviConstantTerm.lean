import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvesterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSupporStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantNeZeroOfSeparableMulStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem absHalf_mul : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x y : w.adicCompletion E), x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y := by
  intro E _ _ w x y hx hy
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  have ho : Formalism.UG.ordL (x * y) = Formalism.UG.ordL x + Formalism.UG.ordL y := by
    unfold Formalism.UG.ordL
    have h1 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h2 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h3 : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
    rw [dif_neg h1, dif_neg h2, dif_neg h3]
    have : WithZero.unzero h3 = WithZero.unzero h1 * WithZero.unzero h2 := by
      apply WithZero.coe_injective
      simp [map_mul]
    rw [this, toAdd_mul]
    ring
  unfold absHalf
  rw [ho, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_pos hq _).le]
  push_cast
  ring

theorem isClosed_parP : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E), IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  intro E _ _ a n w
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

theorem blk_mem_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), blk h w m X ∈ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m X
  unfold blk
  simp only []
  split_ifs with hM
  · change (hM.unit : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular _
    rw [IsUnit.unit_spec]
    intro i j hij
    have hj : (j : ℕ) < a := by
      by_contra hc
      push_neg at hc
      simp only [hc, decide_true] at hij
      exact (by decide : ∀ c : Bool, ¬ (true < c)) _ hij
    have hi : a ≤ (i : ℕ) := by
      by_contra hc
      push_neg at hc
      simp only [not_le.2 hc, decide_false] at hij
      exact (by decide : ∀ c : Bool, ¬ (c < false)) _ hij
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases hi' : (finSumFinEquiv.trans (finCongr h)).symm i with i' | i'
    · exfalso
      have := congrArg (finSumFinEquiv.trans (finCongr h)) hi'
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp at hv
      omega
    · rcases hj' : (finSumFinEquiv.trans (finCongr h)).symm j with j' | j'
      · simp
      · exfalso
        have := congrArg (finSumFinEquiv.trans (finCongr h)) hj'
        rw [Equiv.apply_symm_apply] at this
        have hv := congrArg Fin.val this
        simp at hv
        omega
  · exact (parP a n w).one_mem

theorem avg_const_mul {H : Type} [Group H] (u : H → ℂ) {c : ℂ} (hc : c ≠ 0) :
    avg (fun x => c * u x) = c * avg u := by
  have hs : rStab (fun x => c * u x) = rStab u := by
    ext k
    change (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
    exact ⟨fun h x => mul_left_cancel₀ hc (h x), fun h x => by rw [h x]⟩
  unfold avg
  rw [hs, ← mul_finsum]
  ring

theorem absHalf_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) : absHalf w x ≠ 0 := by
  unfold absHalf
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  exact_mod_cast (Real.sqrt_pos.2 (zpow_pos hq _)).ne'

theorem ct_eq_mul_orbN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ct (Nat.add_sub_cancel' ha) w f m = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f m := by
  intro E _ _ _ n a ha w f hf m hsep
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m
  have hR := GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul (w.adicCompletion E) _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hsep
  have hD := GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq (w.adicCompletion E) a (n - a) m.1 m.2.val
  have hd1 : m.1.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).ne_zero
  have hd2 : m.2.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit).ne_zero
  have hL : LinearMap.det (adL m.1 m.2.val) ≠ 0 := by
    intro h0
    rw [h0] at hD
    apply hR
    have : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 = 0 := by rw [← hD]; ring
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hJ := GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a (n - a) (adL m.1 m.2.val)
    (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m X)) hL hU hcs
  have hI : orbN (Nat.add_sub_cancel' ha) w f m = hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m (adL m.1 m.2.val (Multiplicative.toAdd X)))) := by
    unfold orbN
    simp only [GlobalTheory.T.unipotent_conj_levi_eq_blockUpperTwistedSylvester]
  rw [hI, hJ]
  change absHalf w (m.1.val.det ^ (n - a) / m.2.val.det ^ a) * hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w n) f (blk (Nat.add_sub_cancel' ha) w m (Multiplicative.toAdd X))) = _
  have hq : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a) =
      LinearMap.det (adL m.1 m.2.val) * (LinearMap.det (adL m.1 m.2.val) * (m.1.val.det ^ (n - a) / m.2.val.det ^ a)) := by
    rw [← hD]
    field_simp
    ring
  have hq0 : m.1.val.det ^ (n - a) / m.2.val.det ^ a ≠ 0 := div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  rw [hq, absHalf_mul E w _ _ hL (mul_ne_zero hL hq0), absHalf_mul E w _ _ hL hq0]
  have h0 := absHalf_ne_zero' w (LinearMap.det (adL m.1 m.2.val))
  field_simp

theorem conjP_charpoly {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.charpoly = m.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g m.val

theorem conjP_det {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.det = m.val.det := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj' g m.val

theorem orbInt_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w n) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w n) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  intro E _ _ _ n a ha w f hf m hsep
  have hf' : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f := by
    rcases hf with h | h
    · exact ⟨_, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, h⟩
    · exact h
  have hc0 := absHalf_ne_zero' w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a))
  have h1 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (ct (Nat.add_sub_cancel' ha) w f) =
      twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 2
    funext k
    have e1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.charpoly = m.1.val.charpoly :=
      fun g => conjP_charpoly g.1 m.1
    have e2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.charpoly = m.2.val.charpoly :=
      fun g => conjP_charpoly g.2 m.2
    have d1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.det = m.1.val.det :=
      fun g => conjP_det g.1 m.1
    have d2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.det = m.2.val.det :=
      fun g => conjP_det g.2 m.2
    set g := Quotient.out q * (k : GLw a w × GLw (n - a) w)
    rw [ct_eq_mul_orbN E n a ha w f hf' _ (by rw [e1, e2]; exact hsep), e1, e2, d1, d2]
  have h2 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') =
      absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
        twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (orbN (Nat.add_sub_cancel' ha) w f) := by
    unfold twOrb
    rw [mul_finsum]
    refine finsum_congr fun q => ?_
    rw [avg_const_mul _ hc0]
    ring
  have hγ := blk_mem_parP E n a (n - a) (Nat.add_sub_cancel' ha) w m 0
  have hKG := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [h1, h2, ← GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi E n a ha w f hf' m hsep hγ,
    ← GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage (GLw n w) (GlobalTheory.LFun.KGL w n) (parP a n w) hKG.1 hKG.2 (isClosed_parP E a n w) (GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL E a n w) _ hγ
      (GlobalTheory.T.twisted_centralizer_block_le_parabolic E n a (n - a) _ w m hsep) f hf']

end GlobalTheory.LeviDesc
