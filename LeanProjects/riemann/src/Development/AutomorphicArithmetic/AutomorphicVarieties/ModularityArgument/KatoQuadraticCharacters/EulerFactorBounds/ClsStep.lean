import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.XiAction

private theorem vc {M k : ℕ} [NeZero M] (h : k ∣ M) (a : ZMod M) :
    ((a.val : ℕ) : ZMod k) = ZMod.castHom h (ZMod k) a := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem cnd_iff (l N M : ℕ) [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g δ : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0) (hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod l) = 1)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • m') :
    Cnd l N g m ↔ Cnd l N g m' := by
  have e : ∀ i, m i 0 * (en δ 0 0 : ZMod M) + m i 1 * (en δ 1 0 : ZMod M) = (ν : ZMod M) * m' i 0 := by
    intro i
    have := congrFun (congrFun h i) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, en] using this
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  have uN : (en δ 0 0 : ZMod N) * (en δ 1 1 : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hδN] at this; simpa using this
  have ul : (en δ 0 0 : ZMod l) * (en δ 1 1 : ZMod l) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at this
    rw [hδl] at this; simpa using this
  have eN : ∀ i, ((m i 0).val : ZMod N) = ((m' i 0).val : ZMod N) := by
    intro i
    have := congrArg (ZMod.castHom hN (ZMod N)) (e i)
    rw [map_add, map_mul, map_mul, map_mul, map_intCast, map_intCast, hδN, ← vc hN, ← vc hN, ← vc hN, ← vc hN, h1] at this
    linear_combination (en δ 1 1 : ZMod N) * this - (((m i 0).val : ZMod N) - ((m' i 0).val : ZMod N)) * uN
  have el : ∀ i, ((m i 0).val : ZMod l) * (en δ 0 0 : ZMod l) = ((m' i 0).val : ZMod l) := by
    intro i
    have := congrArg (ZMod.castHom hl (ZMod l)) (e i)
    rw [map_add, map_mul, map_mul, map_mul, map_intCast, map_intCast, hδl, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2] at this
    linear_combination this
  unfold Cnd
  rw [eN 0, eN 1, ← el 0, ← el 1]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h3 => ?_, fun h3 => ?_⟩)
  · linear_combination (en δ 0 0 : ZMod l) * h3
  · linear_combination (en δ 1 1 : ZMod l) * h3 -
      ((en g 1 0 : ZMod l) * ((m 0 0).val : ZMod l) - (en g 0 0 : ZMod l) * ((m 1 0).val : ZMod l)) * ul

private theorem wt_dvd (l n M w : ℕ) [Fact l.Prime] [NeZero M] (hl : l ^ n ∣ M) (δ : Matrix (Fin 2) (Fin 2) ℤ)
    (ν : ZMod M) (h2 : (ν.val : ZMod (l ^ n)) = 1) (d d' : ZMod M) (hd : d' = ν ^ 2 * d)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * δ.map (Int.castRingHom (ZMod M)) = ν • m') (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ (d.val : ℤ_[l]) * (((m 0 0).val : ℤ_[l]) * (mZl l δ *ᵥ u) 0 + ((m 0 1).val : ℤ_[l]) * (mZl l δ *ᵥ u) 1) ^ w -
      (d'.val : ℤ_[l]) * (((m' 0 0).val : ℤ_[l]) * u 0 + ((m' 0 1).val : ℤ_[l]) * u 1) ^ w := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have e : ∀ j, ((m 0 0).val : ZMod (l ^ n)) * (δ 0 j : ZMod (l ^ n)) + ((m 0 1).val : ZMod (l ^ n)) * (δ 1 j : ZMod (l ^ n)) =
      ((m' 0 j).val : ZMod (l ^ n)) := by
    intro j
    have h0 : m 0 0 * (δ 0 j : ZMod M) + m 0 1 * (δ 1 j : ZMod M) = ν * m' 0 j := by
      have := congrFun (congrFun h 0) j
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have := congrArg (ZMod.castHom hl (ZMod (l ^ n))) h0
    rw [map_add, map_mul, map_mul, map_mul, map_intCast, map_intCast, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2, one_mul] at this
    exact this
  have ed : (d'.val : ZMod (l ^ n)) = (d.val : ZMod (l ^ n)) := by
    rw [vc hl d', hd, map_mul, map_pow, ← vc hl, ← vc hl, h2, one_pow, one_mul]
  have ev : ∀ i, (mZl l δ *ᵥ u) i = (δ i 0 : ℤ_[l]) * u 0 + (δ i 1 : ℤ_[l]) * u 1 := by
    intro i
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ev, ev]
  simp only [map_sub, map_mul, map_pow, map_add, map_natCast, map_intCast]
  rw [ed, ← e 0, ← e 1, sub_eq_zero]
  congr 2
  ring

private theorem cls_step {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (n N : ℕ) (hN : 0 < N) (δ δ' : SL(2, ℤ))
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (f f' : X.Kˣ) (hf : Cgr (l ^ n) (slU X (ofSL δ') f) f') (k k' : ℤ_[l]) (hk : (l : ℤ_[l]) ^ n ∣ k - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (k • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        k' • clsK X l n (slD X N (f' : X.K))) = 0 := by
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨-, s2, s3, -⟩ := sSlD Ω ε X N hN
  have r1 := c5 (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f')
  have r3 := c4 _ _ _ _ r1 r2 (by
    obtain ⟨h, hh⟩ := hf
    refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩
    rw [← map_pow, ← map_mul, ← hh]
    apply Units.ext
    have := s2 _ _ (by rw [δ.det_coe]; exact one_pos) hc (f : X.K)
    rw [s3 δ'] at this
    exact this)
  have r4 := a5 k k' (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))) hk
  have r5 : AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        clsK X l n (slD X N (f' : X.K))) = 0 := r3
  rw [← sub_add_sub_cancel _ (k' • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))),
    map_add, r4, ← smul_sub, map_smul, r5, smul_zero, add_zero]

private theorem conj_ex (N : ℕ) (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ en δ 1 0) : ∃ δ' : SL(2, ℤ),
    !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨c, hc⟩ := h
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  refine ⟨⟨!![en δ 0 0, N * en δ 0 1; c, en δ 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of, ← hdet, hc]; ring
  · unfold en at hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, en, hc, mul_comm]

private theorem cd_row (N M₀ M : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (δ δ' : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0)
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (ν : ZMod M) (m m' : Matrix (Fin 2) (Fin 2) (ZMod M)) (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0)
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = ν • m') (x : Row M₀) :
    rt (x ᵥ* cD N M₀ m) δ' = ((ν.val : ZMod M₀) • x) ᵥ* cD N M₀ m' := by
  obtain ⟨d1, -, -, d4⟩ := sCdFacts N M₀ M hM
  have hN : N ∣ M := hM ▸ dvd_mul_right N M₀
  have e1 : ν • m' = !![ν, 0; 0, ν] * m' := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : x ᵥ* cD N M₀ (!![ν, 0; 0, ν] : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν.val : ZMod M₀) • x := by
    funext j
    fin_cases j <;> simp [cD, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  unfold rt
  rw [← d4 _ _ hc, Matrix.vecMul_vecMul, ← d1 _ _ hm ?_, h, e1, d1 _ _ ?_ hm', ← Matrix.vecMul_vecMul, e2]
  · simp
  · rw [vc hN, Matrix.map_apply, eq_intCast, map_intCast]; exact hδN

end UpperTheory.V.Z.Kato.Nb.XiAction

open UpperTheory.V.Z.Kato.Nb.XiAction in
theorem UpperTheory.V.Z.Kato.Nb.sXiAct :
    UpperTheory.V.Z.Kato.Nb.SXiAct := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy P a ha δ hδ ν h1 h2 hP u
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl1 : l ∣ l ^ n := dvd_pow_self l (by have := L.pos; omega)
  have hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.1
  have hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.2
  have h2' : ((ν : ZMod M).val : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hl1 (ZMod l)) h2
    rwa [map_natCast, map_one] at this
  obtain ⟨δ', hc⟩ := conj_ex N δ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hδN)
  let D : GL (Fin 2) (ZMod M) := Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ)
  let S : GL (Fin 2) (ZMod M) := Matrix.GeneralLinearGroup.scalar (Fin 2) ν
  let e : GL (Fin 2) (ZMod M) ≃ GL (Fin 2) (ZMod M) := (Equiv.mulRight D).trans (Equiv.mulLeft S⁻¹)
  have he : ∀ m, m * D = S * e m := fun m => by simp [e]
  have hrel : ∀ m : GL (Fin 2) (ZMod M), (m : Matrix (Fin 2) (Fin 2) (ZMod M)) *
      (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • (e m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro m
    have := congrArg (fun z : GL (Fin 2) (ZMod M) => (z : Matrix (Fin 2) (Fin 2) (ZMod M))) (he m)
    simp only [Units.val_mul] at this
    rw [Matrix.smul_eq_diagonal_mul]
    exact this
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det (e m) * ν ^ 2 := by
    intro m
    apply Units.ext
    have := congrArg Matrix.det (hrel m)
    rw [Matrix.det_mul, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, δ.det_coe, map_one, mul_one] at this
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this, mul_comm]; simp
  have hcnd := fun m : GL (Fin 2) (ZMod M) => cnd_iff l N M hN (hl1.trans hln) g δ hδN hδl ν h1 h2' _ _ (hrel m)
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l _ (Xi X l n N M₀ M w g x y P a _) - _) = 0
  unfold Xi
  rw [map_sum, map_sub, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_equiv e (fun m => ?_) (fun m hm => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcnd m, hdet m, hP]
  · have hm1 := (Finset.mem_filter.1 hm).2.1
    have hm2 := (hcnd m).1 hm1
    rw [← sub_eq_zero, ← map_sub, map_smul]
    refine cls_step X l n N (NeZero.pos N) δ δ' hc _ _ ?_ _ _ ?_
    · rw [← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m), ← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m)]
      exact (ha _ _ ((sCdFacts N M₀ M L.eq).2.2.1 m hm1.1 x y hxy)).2 δ'
    · refine wt_dvd l n M w hln _ ν h2 _ _ ?_ _ _ (hrel m) u
      rw [hdet m, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      congr 1
      rw [mul_inv, mul_comm _ (ν ^ 2)⁻¹, mul_inv_cancel_left]
