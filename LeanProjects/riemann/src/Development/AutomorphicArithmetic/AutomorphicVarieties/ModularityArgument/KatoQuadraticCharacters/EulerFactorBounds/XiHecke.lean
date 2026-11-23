import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.XiHecke

private theorem vc {M k : ℕ} [NeZero M] (h : k ∣ M) (a : ZMod M) :
    ((a.val : ℕ) : ZMod k) = ZMod.castHom h (ZMod k) a := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem ent {M k : ℕ} [NeZero M] (hk : k ∣ M) (h : Matrix (Fin 2) (Fin 2) ℤ) (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (i j : Fin 2) : (((m * h.map (Int.castRingHom (ZMod M))) i j).val : ZMod k) =
      ((m i 0).val : ZMod k) * (h 0 j : ZMod k) + ((m i 1).val : ZMod k) * (h 1 j : ZMod k) := by
  have h0 : (m * h.map (Int.castRingHom (ZMod M))) i j = m i 0 * (h 0 j : ZMod M) + m i 1 * (h 1 j : ZMod M) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h0, vc hk, vc hk, vc hk, map_add, map_mul, map_mul, map_intCast, map_intCast]

private theorem cnd_iff (l N M : ℕ) [Fact l.Prime] [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ))
    (h : Matrix (Fin 2) (Fin 2) ℤ) (hN1 : ((h 1 0 : ℤ) : ZMod N) = 0) (hl1 : ((h 1 0 : ℤ) : ZMod l) = 0)
    (hN0 : ((h 0 0 : ℤ) : ZMod N) = 1) (hl0 : ((h 0 0 : ℤ) : ZMod l) ≠ 0) (m : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    Cnd l N g m ↔ Cnd l N g (m * h.map (Int.castRingHom (ZMod M))) := by
  unfold Cnd
  rw [ent hN, ent hN, ent hl, ent hl, hN1, hl1, hN0]
  simp only [mul_zero, add_zero, mul_one]
  rw [← mul_assoc, ← mul_assoc, mul_left_inj' hl0]

private theorem wt_dvd (l n M w p : ℕ) [Fact l.Prime] [NeZero M] (hl : l ^ n ∣ M) (h : Matrix (Fin 2) (Fin 2) ℤ)
    (d d' : ZMod M) (hd : d = p * d') (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ (d.val : ℤ_[l]) * (((m 0 0).val : ℤ_[l]) * (mZl l h *ᵥ u) 0 + ((m 0 1).val : ℤ_[l]) * (mZl l h *ᵥ u) 1) ^ w -
      (p : ℤ_[l]) * ((d'.val : ℤ_[l]) * ((((m * h.map (Int.castRingHom (ZMod M))) 0 0).val : ℤ_[l]) * u 0 +
        (((m * h.map (Int.castRingHom (ZMod M))) 0 1).val : ℤ_[l]) * u 1) ^ w) := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have ed : (d.val : ZMod (l ^ n)) = p * (d'.val : ZMod (l ^ n)) := by
    rw [vc hl d, hd, map_mul, map_natCast, ← vc hl]
  have ev : ∀ i, (mZl l h *ᵥ u) i = (h i 0 : ℤ_[l]) * u 0 + (h i 1 : ℤ_[l]) * u 1 := by
    intro i
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ev, ev]
  simp only [map_sub, map_mul, map_pow, map_add, map_natCast, map_intCast]
  rw [ed, ent hl, ent hl, sub_eq_zero, mul_assoc]
  congr 3
  ring

private theorem cd_row (N M₀ M p : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (h h' : Matrix (Fin 2) (Fin 2) ℤ)
    (hN1 : ((h 1 0 : ℤ) : ZMod N) = 0) (hc : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (hd : h'.det = p)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (hm : ((m 1 0).val : ZMod N) = 0) (x : Row M₀) :
    (x ᵥ* cD N M₀ (m * h.map (Int.castRingHom (ZMod M)))) ᵥ* h'.adjugate.map (Int.castRingHom (ZMod M₀)) =
      ((p : ZMod M₀) • x) ᵥ* cD N M₀ m := by
  obtain ⟨d1, -, -, d4⟩ := sCdFacts N M₀ M hM
  have hN : N ∣ M := hM ▸ dvd_mul_right N M₀
  rw [d1 _ _ hm ?_, d4 _ _ hc, Matrix.vecMul_vecMul, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_adjugate, hd]
  · have : ((p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom (ZMod M₀)) = (p : ZMod M₀) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.natCast_apply]
    rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.vecMul_smul, Matrix.smul_vecMul]
  · rw [vc hN, Matrix.map_apply, eq_intCast, map_intCast]; exact hN1

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N : ℕ)

private theorem cls_step (hN : 0 < N) (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hd : 0 < h.det)
    (hc : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1])
    (f : X.Kˣ) (k k' : ℤ_[l]) (hk : (l : ℤ_[l]) ^ n ∣ k - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (k • X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        k' • clsK X l n (slD X N (slU X (toGQ h') f : X.K))) = 0 := by
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨-, s2, -⟩ := sSlD Ω ε X N hN
  have r1 := c5 (X.sl (toGQ h)).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (slU X (toGQ h') f))
  have r3 := c4 _ _ _ _ r1 r2 (by
    refine ⟨1, ?_⟩
    rw [one_pow, mul_one]
    apply Units.ext
    exact s2 _ _ hd hc (f : X.K))
  have r4 := a5 k k' (X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K)))) hk
  have r5 : AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        clsK X l n (slD X N (slU X (toGQ h') f : X.K))) = 0 := r3
  rw [← sub_add_sub_cancel _ (k' • X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K)))),
    map_add, r4, ← smul_sub, map_smul, r5, smul_zero, add_zero]

private theorem cls_prod {ι : Type} (S : Finset ι) (f : ι → X.Kˣ) :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (∑ i ∈ S, clsK X l n (slD X N (f i : X.K)) - clsK X l n (slD X N ((∏ i ∈ S, f i : X.Kˣ) : X.K))) = 0 := by
  obtain ⟨c1, c2, c3, c4, -⟩ := sCls Ω ε X l n
  have r : Rep X l n (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (∏ i ∈ S, f i)) (∑ i ∈ S, clsK X l n (slD X N (f i : X.K))) := by
    induction S using Finset.induction_on with
    | empty => simpa using c3 1 _ 0 (c1 1)
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul]
      exact (c2 _ _ _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (f i))) ih).1
  exact c4 _ _ _ _ r (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (∏ i ∈ S, f i))) ⟨1, by simp⟩

private theorem xi_prod (M₀ M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x y : Row M₀) (P : (ZMod M)ˣ → Prop) {ι : Type} (S : Finset ι)
    (f : ι → Fam X M₀) : CgF X l n (∑ i ∈ S, Xi X l n N M₀ M w g x y P (f i))
      (Xi X l n N M₀ M w g x y P fun x y => ∏ i ∈ S, f i x y) := by
  intro u
  rw [Finset.sum_apply]
  unfold Xi
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← Finset.smul_sum, ← smul_sub, map_smul, cls_prod, smul_zero]

private theorem step (M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)) (L : Lev l n N M₀ M g) (p : ℕ) (hp : 0 < p)
    (q : (ZMod M)ˣ) (hq : (q : ZMod M) = p) (x y : Row M₀) (P : (ZMod M)ˣ → Prop) (a : Fam X M₀)
    (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hc : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (hd : h.det = p)
    (hN1 : ((h 1 0 : ℤ) : ZMod N) = 0) (hl1 : ((h 1 0 : ℤ) : ZMod l) = 0) (hN0 : ((h 0 0 : ℤ) : ZMod N) = 1) :
    CgF X l n (X.act l h (Xi X l n N M₀ M w g ((p : ZMod M₀) • x) ((p : ZMod M₀) • y) (fun z => P (z * q)) a))
      ((p : ℤ_[l]) • Xi X l n N M₀ M w g x y P fun x y => slU X (toGQ h')
        (a (x ᵥ* h'.adjugate.map (Int.castRingHom (ZMod M₀))) (y ᵥ* h'.adjugate.map (Int.castRingHom (ZMod M₀))))) := by
  intro u
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl : l ∣ M := (dvd_pow_self l (by have := L.pos; omega)).trans hln
  have hd' : h'.det = p := by
    have := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hd] at this
    refine (mul_right_cancel₀ ?_ this).symm
    simpa using NeZero.ne N
  have hl0 : ((h 0 0 : ℤ) : ZMod l) ≠ 0 := by
    intro h0
    have e := congrArg (Int.cast : ℤ → ZMod l) hd
    rw [Matrix.det_fin_two] at e
    push_cast at e
    rw [h0, hl1, zero_mul, mul_zero, sub_zero] at e
    have := (q.isUnit.map (ZMod.castHom hl (ZMod l))).ne_zero
    rw [hq, map_natCast] at this
    exact this e.symm
  have hdm : (h.map (Int.castRingHom (ZMod M))).det = q := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, hq, map_natCast]
  let D : GL (Fin 2) (ZMod M) := Matrix.GeneralLinearGroup.mk'' (h.map (Int.castRingHom (ZMod M))) (hdm ▸ q.isUnit)
  have hrel : ∀ m : GL (Fin 2) (ZMod M), ((Equiv.mulRight D m : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) * h.map (Int.castRingHom (ZMod M)) := fun m => rfl
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det (Equiv.mulRight D m) = Matrix.GeneralLinearGroup.det m * q := by
    intro m
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hrel, Matrix.det_mul, hdm]
    rfl
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l _ (Xi X l n N M₀ M w g _ _ _ a _) - (p : ℤ_[l]) • Xi X l n N M₀ M w g x y P _ u) = 0
  unfold Xi
  rw [Finset.smul_sum, map_sum, map_sub, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_equiv (Equiv.mulRight D) (fun m => ?_) (fun m hm => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdet m, hrel, ← cnd_iff l N M hN hl g h hN1 hl1 hN0 hl0]
  · have hm1 := (Finset.mem_filter.1 hm).2.1
    rw [← sub_eq_zero, ← map_sub, map_smul, smul_smul, hrel]
    beta_reduce
    rw [cd_row N M₀ M p L.eq h h' hN1 hc hd' _ hm1.1, cd_row N M₀ M p L.eq h h' hN1 hc hd' _ hm1.1]
    refine cls_step X l n N (NeZero.pos N) h h' (by rw [hd]; exact_mod_cast hp) hc _ _ _ ?_
    refine wt_dvd l n M w p hln h _ _ ?_ _ u
    rw [hdet m, ← hq, ← Units.val_mul]
    congr 1
    rw [mul_inv, mul_left_comm, mul_inv_cancel, mul_one]

end

private theorem diam_spec (N l p : ℕ) (h : Nat.Coprime p (N * l)) : IsDiam N l p (sgD N l p) := by
  apply Classical.epsilon_spec
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  refine ⟨⟨!![a, -b; ((N * l : ℕ) : ℤ), p], ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hab
  · exact CongruenceSubgroup.Gamma0_mem.2 (by simp)
  · exact CongruenceSubgroup.Gamma0_mem.2 (by simp)
  · simp [en]

end UpperTheory.V.Z.Kato.Nb.XiHecke

open UpperTheory.V.Z.Kato.Nb.XiHecke in
theorem UpperTheory.V.Z.Kato.Nb.sXiHecke :
    UpperTheory.V.Z.Kato.Nb.SXiHecke := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L p hp q hq x y P a
  obtain ⟨aE, a2, a3, a4, -⟩ := sApi Ω ε X l n
  have hco : Nat.Coprime p (N * l) := by
    have h1 : Nat.Coprime p M := (ZMod.isUnit_iff_coprime p M).1 (hq ▸ q.isUnit)
    refine Nat.Coprime.coprime_dvd_right ?_ h1
    rw [L.eq]
    exact Nat.mul_dvd_mul_left N ((dvd_pow_self l (by have := L.pos; omega)).trans L.dl)
  obtain ⟨⟨s1, s2⟩, s3⟩ := diam_spec N l p hco
  have hsN : ((en (sgD N l p) 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 s1
  have hsl : ((en (sgD N l p) 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 s2
  have hdet : en (sgD N l p) 0 0 * en (sgD N l p) 1 1 - en (sgD N l p) 0 1 * en (sgD N l p) 1 0 = 1 := by
    have := (sgD N l p).det_coe
    rwa [Matrix.det_fin_two] at this
  have hs : (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1] =
      !![en (sgD N l p) 0 0 * p, en (sgD N l p) 0 1; en (sgD N l p) 1 0 * p, en (sgD N l p) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, en]
  refine aE.trans ?_ (a3 (p : ℤ_[l]) _ _ (xi_prod X l n N M₀ M w g x y P Finset.univ fun o x y => slU X (toGQ (hP l p N o))
    (a (x ᵥ* (hP l p N o).adjugate.map (Int.castRingHom (ZMod M₀))) (y ᵥ* (hP l p N o).adjugate.map (Int.castRingHom (ZMod M₀))))))
  rw [Finset.smul_sum, Fintype.sum_option, add_comm, Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply,
    Finset.sum_range, hs]
  refine (a2 _ _ _ _ (a4 _ _ _ _ fun j _ => ?_) ?_).1
  · refine step X l n N M₀ M w g L p hp.out.pos q hq x y P a _ _ ?_ ?_ ?_ ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals simp [Matrix.det_fin_two]
  · refine step X l n N M₀ M w g L p hp.out.pos q hq x y P a _ _ ?_ ?_ ?_ ?_ ?_
    · have := Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hsN)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
      · ring
      · linear_combination -(p : ℤ) * this
    · rw [Matrix.det_fin_two_of]; linear_combination (p : ℤ) * hdet
    · simp [hsN]
    · simp [hsl]
    · have := congrArg (Int.cast : ℤ → ZMod N) hdet
      push_cast at this
      rw [hsN, s3] at this
      simpa using this
