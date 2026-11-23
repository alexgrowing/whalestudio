import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def uP (q n : ℕ) (j : Fin q) : Polynomial (MvPolynomial (Fin q × Fin n) ℤ) :=
  Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (MvPolynomial.X (j, k)) * Polynomial.X ^ (k : ℕ)

private theorem prod_coeff (R : Type) [CommRing R] (q n : ℕ) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).coeff k =
      (-1) ^ (n - k) * emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k)) := by
  have hh : (emb ℤ R j : MvPolynomial (Fin n) ℤ →+* PU R q n) =
      (MvPolynomial.aeval (fun i : Fin n => (MvPolynomial.X (j, i) : PU R q n))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => by simp [emb])
  rw [show emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k)) = _ from RingHom.congr_fun hh _]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have key := Multiset.prod_X_sub_C_coeff
    (Finset.univ.val.map (fun i : Fin n => (MvPolynomial.X (j, i) : PU R q n))) (k := k) (by simpa using hk)
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.map_map] at key
  rw [← key]
  rfl

private theorem exists_mvPolynomial_action_extending_inc (R B M V : Type) [CommRing R] [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup V] [Module R V] (σ : Type) (β : R →+* B) (act : MvPolynomial σ R →ₐ[R] Module.End R V)
    (inc : M →+ V) (hinc : ∀ (t : R) m, inc (β t • m) = t • inc m) :
    ∃ G : MvPolynomial σ B →+ M →+ V, (∀ m, G 1 m = inc m) ∧
      (∀ u h m, G (MvPolynomial.map β u * h) m = act u (G h m)) ∧
      (∀ b h m, G (MvPolynomial.C b * h) m = G h (b • m)) := by
  let X : (σ →₀ ℕ) → B →+ M →+ V := fun e =>
    { toFun := fun b =>
        { toFun := fun m => act (MvPolynomial.monomial e 1) (inc (b • m))
          map_zero' := by simp
          map_add' := fun x y => by simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := fun x y => by ext m; simp [add_smul] }
  let G : MvPolynomial σ B →+ M →+ V :=
    (Finsupp.liftAddHom X).comp (AddMonoidAlgebra.coeffAddEquiv (R := B) (M := σ →₀ ℕ)).toAddMonoidHom
  have hG : ∀ e b m, G (MvPolynomial.monomial e b) m = act (MvPolynomial.monomial e 1) (inc (b • m)) := by
    intro e b m
    show (Finsupp.liftAddHom X (Finsupp.single e b)) m = _
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  refine ⟨G, ?_, ?_, ?_⟩
  · intro m
    rw [← MvPolynomial.C_1, MvPolynomial.C_apply, hG, one_smul, ← MvPolynomial.C_apply, MvPolynomial.C_1, map_one]
    rfl
  · intro u h m
    induction u using MvPolynomial.induction_on' with
    | monomial e r =>
      induction h using MvPolynomial.induction_on' with
      | monomial e' c =>
        have h1 : MvPolynomial.monomial (e + e') (1 : R) =
            MvPolynomial.monomial e 1 * MvPolynomial.monomial e' 1 := by
          rw [MvPolynomial.monomial_mul, one_mul]
        have h2 : MvPolynomial.monomial e r = r • MvPolynomial.monomial e (1 : R) := by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [MvPolynomial.map_monomial, MvPolynomial.monomial_mul, hG, hG, mul_smul, hinc]
        generalize inc (c • m) = v
        rw [h1, h2]
        simp only [map_smul, map_mul, Module.End.mul_apply, LinearMap.smul_apply]
      | add p q hp hq =>
        simp only [mul_add, map_add, AddMonoidHom.add_apply, hp, hq]
    | add p q hp hq =>
      simp only [map_add, add_mul, AddMonoidHom.add_apply, hp, hq, LinearMap.add_apply]
  · intro b h m
    induction h using MvPolynomial.induction_on' with
    | monomial e c =>
      rw [MvPolynomial.C_mul_monomial, hG, hG, mul_comm, mul_smul]
    | add p q hp hq =>
      simp only [mul_add, map_add, AddMonoidHom.add_apply, hp, hq]

theorem UpperTheory.V.Pa.Lev.multiPhi :
    ∀ (R B M V : Type) [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (inc : M →+ V), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) m, inc (β t • m) = t • inc m) → (∀ j k, k ≤ n → ∀ m, act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) (inc m) = inc (((-1) ^ k * (P j).coeff (n - k)) • m)) → ∃ φ : MSplitAlg P n ⊗[B] M →+ V, (∀ m, φ (1 ⊗ₜ m) = inc m) ∧ ∀ (t : PU R q n) z, φ (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • z) = act t (φ z) := by
  intro R B M V _ _ _ _ _ _ q n β P act inc hmon hdeg hinc hact
  obtain ⟨G, h1, hL, hC⟩ := exists_mvPolynomial_action_extending_inc R B M V (Fin q × Fin n) β act inc hinc
  have hgen : ∀ jk : Fin q × ℕ, ∀ m, G ((∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (jk.1, i))) -
      Polynomial.map MvPolynomial.C (P jk.1)).coeff jk.2) m = 0 := by
    rintro ⟨j, k⟩ m
    dsimp only
    have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : MvPolynomial (Fin q × Fin n) B))) =
        (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).map (MvPolynomial.map β) := by
      simp [Polynomial.map_prod]
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, hprod, Polynomial.coeff_map]
    rcases le_or_gt k n with hk | hk
    · rw [prod_coeff R q n j k hk, map_sub, AddMonoidHom.sub_apply]
      have e1 := hL ((-1) ^ (n - k) * emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k))) 1 m
      rw [mul_one, h1] at e1
      have e2 := hC ((P j).coeff k) 1 m
      rw [mul_one, h1] at e2
      rw [e1, e2, map_mul, map_pow, map_neg, map_one, Module.End.mul_apply, hact j (n - k) (Nat.sub_le n k) m,
        Nat.sub_sub_self hk]
      rcases Nat.even_or_odd (n - k) with hp | hp
      · simp [hp.neg_one_pow]
      · simp [hp.neg_one_pow, neg_smul]
    · have hd : (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).natDegree ≤ n :=
        (Polynomial.natDegree_prod_le _ _).trans
          ((Finset.sum_le_sum fun i _ => Polynomial.natDegree_X_sub_C_le _).trans (by simp))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_lt hk)]
      simp
  have hI : ∀ x ∈ mSplitIdeal P n, ∀ a m, G (a * x) m = 0 := by
    intro x hx
    unfold mSplitIdeal Ideal.span at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨jk, rfl⟩ := hx
      intro a m
      induction a using MvPolynomial.induction_on' with
      | monomial e b =>
        have hm : MvPolynomial.monomial e b = MvPolynomial.C b * MvPolynomial.map β (MvPolynomial.monomial e 1) := by
          rw [MvPolynomial.map_monomial, map_one, MvPolynomial.C_mul_monomial, mul_one]
        rw [hm, mul_assoc, hC, hL, hgen jk (b • m), map_zero]
      | add p q hp hq => simp only [add_mul, map_add, AddMonoidHom.add_apply, hp, hq, add_zero]
    | zero => intro a m; simp
    | add x y _ _ hx hy => intro a m; simp only [mul_add, map_add, AddMonoidHom.add_apply, hx, hy, add_zero]
    | smul c x _ hx => intro a m; rw [smul_eq_mul, ← mul_assoc, hx]
  have hvan : (mSplitIdeal P n).toAddSubgroup ≤ G.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    ext m
    simpa using hI x hx 1 m
  let F : MSplitAlg P n →+ M →+ V := QuotientAddGroup.lift (mSplitIdeal P n).toAddSubgroup G hvan
  have hF : ∀ f, F (Ideal.Quotient.mk (mSplitIdeal P n) f) = G f := fun f => rfl
  have hbal : ∀ (b : B) (x : MSplitAlg P n) (m : M), F (b • x) m = F x (b • m) := by
    intro b x m
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hF, hF, MvPolynomial.algebraMap_eq, hC]
  refine ⟨TensorProduct.liftAddHom F hbal, ?_, ?_⟩
  · intro m
    rw [TensorProduct.liftAddHom_tmul, ← map_one (Ideal.Quotient.mk (mSplitIdeal P n)), hF, h1]
  · intro t z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul, smul_eq_mul,
        ← map_mul, hF, hF, hL]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]
