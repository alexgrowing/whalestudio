import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.UnitLemma.ShiftRes

def shiftPoly {F : Type} [Field F] (t s : F) (p : F[X]) : F[X] :=
  C (t ^ p.natDegree)⁻¹ * p.comp (C t * X + C s)

theorem natDegree_lin {F : Type} [Field F] (t s : F) (ht : t ≠ 0) : (C t * X + C s).natDegree = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X t ht]

theorem natDegree_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) :
    (shiftPoly t s p).natDegree = p.natDegree := by
  unfold shiftPoly
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ht)), natDegree_comp, natDegree_lin t s ht, mul_one]

theorem monic_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Monic) :
    (shiftPoly t s p).Monic := by
  unfold shiftPoly Monic
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [natDegree_lin t s ht]; exact one_ne_zero),
    hp.leadingCoeff, one_mul]
  have : (C t * X + C s).leadingCoeff = t := by
    rw [leadingCoeff, natDegree_lin t s ht]; simp
  rw [this, inv_mul_cancel₀ (pow_ne_zero _ ht)]

theorem map_shiftPoly {F L : Type} [Field F] [Field L] (φ : F →+* L) (t s : F) (p : F[X]) :
    (shiftPoly t s p).map φ = shiftPoly (φ t) (φ s) (p.map φ) := by
  unfold shiftPoly
  rw [Polynomial.map_mul, map_C, Polynomial.map_comp, natDegree_map]
  simp

theorem shiftPoly_mul {F : Type} [Field F] (t s : F) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    shiftPoly t s (p * q) = shiftPoly t s p * shiftPoly t s q := by
  unfold shiftPoly
  rw [hp.natDegree_mul hq, mul_comp, pow_add, mul_inv, C_mul]
  ring

theorem shiftPoly_eq_prod {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p : L[X]) (hp : p.Monic) :
    shiftPoly t s p = ((p.roots.map fun α => (α - s) / t).map fun a => X - C a).prod := by
  have hsp := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = p.natDegree := hsp.natDegree_eq_card_roots.symm
  unfold shiftPoly
  conv_lhs => arg 2; rw [hsp.eq_prod_roots_of_monic hp]
  rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  have key : ∀ α : L, (X - C α).comp (C t * X + C s) = C t * (X - C ((α - s) / t)) := by
    intro α
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ ht, C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard, ← C_pow, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (pow_ne_zero _ ht), C_1, one_mul]

theorem resultant_shiftPoly_alg {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p q : L[X])
    (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  have hcp : Multiset.card p.roots = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hcq : Multiset.card q.roots = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  rw [resultant_eq_prod_roots_sub _ _ (monic_shiftPoly t s ht p hp) (monic_shiftPoly t s ht q hq)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _), resultant_eq_prod_roots_sub p q hp hq (IsAlgClosed.splits p)
    (IsAlgClosed.splits q), shiftPoly_eq_prod t s ht p hp, shiftPoly_eq_prod t s ht q hq,
    roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C, Multiset.prod_map_product_eq_prod_prod,
    Multiset.prod_map_product_eq_prod_prod]
  simp only [Multiset.map_map, Function.comp_def]
  have key : ∀ α β : L, (α - s) / t - (β - s) / t = t⁻¹ * (α - β) := by
    intro α β; field_simp; ring
  simp only [key]
  simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcq]
  rw [hcp, ← pow_mul, inv_pow, mul_comm q.natDegree p.natDegree]

theorem resultant_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  let φ := algebraMap F (AlgebraicClosure F)
  apply φ.injective
  have e1 : φ (resultant (shiftPoly t s p) (shiftPoly t s q)) =
      resultant ((shiftPoly t s p).map φ) ((shiftPoly t s q).map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  have e2 : φ (resultant p q) = resultant (p.map φ) (q.map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  rw [e1, map_mul, e2, map_shiftPoly, map_shiftPoly,
    resultant_shiftPoly_alg _ _ ((_root_.map_ne_zero φ).2 ht) _ _ (hp.map φ) (hq.map φ), natDegree_map, natDegree_map,
    map_inv₀, map_pow]

theorem separable_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Separable) :
    (shiftPoly t s p).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (C t * X + C s))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (C t * X + C s)) (C t) :=
    ⟨0, C t⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ ht, C_1]⟩
  have h3 : derivative (p.comp (C t * X + C s)) = (derivative p).comp (C t * X + C s) * C t := by
    rw [derivative_comp, derivative_add, derivative_C_mul_X, derivative_C, add_zero, mul_comm]
  have hc : (p.comp (C t * X + C s)).Separable := by
    show IsCoprime _ _
    rw [h3]
    exact h1.mul_right h2
  unfold shiftPoly
  have hu : IsUnit (C (t ^ p.natDegree)⁻¹ : F[X]) := isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  show IsCoprime _ _
  rw [derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hc

theorem charpoly_eq_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] (x : A)
    (hx : Algebra.adjoin F ({x} : Set A) = ⊤) (p : F[X]) (hp : p.Monic) (hpx : aeval x p = 0)
    (hd : p.natDegree = Module.finrank F A) : (LinearMap.mulLeft F x).charpoly = p := by
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have hCH : aeval x (LinearMap.mulLeft F x).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F x)
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul F A) x (LinearMap.mulLeft F x).charpoly
    have h3 : (Algebra.lmul F A) (aeval x (LinearMap.mulLeft F x).charpoly) = 0 := by rw [← h2]; exact h
    simpa using congrArg (fun f => f 1) h3
  have hcd : (LinearMap.mulLeft F x).charpoly.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree _
  have hle : Module.finrank F A ≤ (minpoly F x).natDegree := by
    let pb := AdjoinRoot.powerBasis' hmon
    haveI : Module.Finite F (AdjoinRoot (minpoly F x)) := pb.finite
    let f := AdjoinRoot.liftAlgHom (minpoly F x) (Algebra.ofId F A) x
      (by rw [← minpoly.aeval F x, aeval_def]; rfl)
    have hs : Function.Surjective f := by
      intro y
      have hy : y ∈ Algebra.adjoin F ({x} : Set A) := hx ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨r, rfl⟩ := hy
      exact ⟨AdjoinRoot.mk _ r, by rw [AdjoinRoot.liftAlgHom_mk]; rfl⟩
    have h1 := LinearMap.finrank_range_le f.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, pb.finrank, AdjoinRoot.powerBasis'_dim] at h1
    exact h1
  have h1 : p = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon hp (minpoly.dvd F x hpx) (by omega)
  have h2 : (LinearMap.mulLeft F x).charpoly = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon (LinearMap.charpoly_monic _) (minpoly.dvd F x hCH) (by omega)
  rw [h2, h1]

theorem val_inv_pow_mul {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    val K.O ((x ^ n)⁻¹ * y) = val K.O y - n * val K.O x := by
  unfold val
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E ((x ^ n)⁻¹) ≠ 0 := by simp [hx]
  have h2 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E y ≠ 0 := by simp [hy]
  rw [map_mul, WithZero.log_mul h1 h2, map_inv₀, map_pow, WithZero.log_inv, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem val_resultant_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (k : ℕ) (t : K.O), t ≠ 0 → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (B₁.P * B₂.P).Separable ∧ GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) - ((k * a * b : ℕ) : ℤ) := by
  intro E _ _ _ w K e hval k t ht hk a b Q₁ Q₂ B₁ B₂ hm₁ hm₂ ha hb hsep hadj₁ hQ₁ hf₁ hadj₂ hQ₂ hf₂
  set t' : K.E := algebraMap K.O K.E t with ht'def
  have ht' : t' ≠ 0 := by
    rw [ht'def]; exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ht
  have hP : ∀ (B : InvAlg K) (Q : (w.adicCompletion E)[X]), Q.Monic →
      Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ →
      aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 →
      Module.finrank K.E B.A = Q.natDegree → B.P = shiftPoly t' 1 (Q.map e.symm.toRingHom) := by
    intro B Q hQm hadj hQ hfin
    have hd : (Q.map e.symm.toRingHom).natDegree = Q.natDegree := natDegree_map _
    have hu : aeval B.g (C t' * X + C 1) = 1 + algebraMap K.O B.A t * B.g := by
      rw [map_add, map_mul, aeval_C, aeval_X, aeval_C, map_one, ht'def, ← IsScalarTower.algebraMap_apply]
      ring
    unfold InvAlg.P
    apply charpoly_eq_of_adjoin
    · rw [eq_top_iff, ← hadj]
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff, ← hu]
      exact aeval_mem_adjoin_singleton _ _
    · exact monic_shiftPoly t' 1 ht' _ (hQm.map _)
    · unfold shiftPoly
      rw [map_mul, aeval_C, aeval_comp, hu, hQ, mul_zero]
    · rw [natDegree_shiftPoly t' 1 ht', hd, hfin]
  have e₁ := hP B₁ Q₁ hm₁ hadj₁ hQ₁ hf₁
  have e₂ := hP B₂ Q₂ hm₂ hadj₂ hQ₂ hf₂
  have hm₁' : (Q₁.map e.symm.toRingHom).Monic := hm₁.map _
  have hm₂' : (Q₂.map e.symm.toRingHom).Monic := hm₂.map _
  refine ⟨?_, ?_⟩
  · rw [e₁, e₂, ← shiftPoly_mul t' 1 _ _ hm₁' hm₂', ← Polynomial.map_mul]
    exact separable_shiftPoly t' 1 ht' _ hsep.map
  · rw [e₁, e₂, resultant_shiftPoly t' 1 ht' _ _ hm₁' hm₂']
    have hR : resultant (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) = e.symm (resultant Q₁ Q₂) := by
      rw [resultant_map_map, natDegree_map, natDegree_map]; rfl
    have hR0 : resultant Q₁ Q₂ ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
    rw [hR, natDegree_map, natDegree_map, val_inv_pow_mul ht' ((_root_.map_ne_zero _).2 hR0), hval, RingEquiv.apply_symm_apply, hk, ha, hb]
    push_cast; ring

end GlobalTheory.UnitLemma.ShiftRes
