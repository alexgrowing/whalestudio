import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualExp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem one_place {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n : ℕ}
    (e : MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ s t z, z.IsSymmetric → Φ s (t * e z) = Φ (s * e z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (x : MvPolynomial (Fin n) O) (s t : A) :
    ∑ k, Φ (e (a k) * s) (e (c k) * t * e x) = ∑ k, Φ (e x * (e (a k) * s)) (e (c k) * t) := by
  have hd := UpperTheory.V.AlgebraTools.hkDualExp O n ι a c h
  have hs := (UpperTheory.V.AlgebraTools.hkDdProps O n).2.2.1
  have e1 : ∀ k, Φ (e (a k) * s) (e (c k) * t * e x)
      = ∑ m, Φ (e (a k * Hk.dd (c k * (x * a m))) * s) (e (c m) * t) := by
    intro k
    have : e (c k) * t * e x = ∑ m, e (c m) * t * e (Hk.dd (c k * (x * a m))) := by
      rw [mul_right_comm, ← map_mul, ← (hd (c k * x)).2, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_right_comm, show a m * (c k * x) = c k * (x * a m) by ring]
    rw [this, h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h3 _ _ _ (hs _), map_mul, mul_right_comm]
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← h2, ← Finset.sum_mul, ← map_sum, (hd _).1, map_mul, mul_assoc]

private theorem many_places {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n q : ℕ}
    (e : Fin q → MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ j s t z, z.IsSymmetric → Φ s (t * e j z) = Φ (s * e j z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (j : Fin q) (x : MvPolynomial (Fin n) O) :
    ∑ i : Fin q → ι, Φ (∏ j, e j (a (i j))) ((∏ j, e j (c (i j))) * e j x)
      = ∑ i : Fin q → ι, Φ (e j x * ∏ j, e j (a (i j))) (∏ j, e j (c (i j))) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := j.pos; omega⟩
  rw [← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp, ← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp,
    Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.prod_univ_succAbove _ j, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact one_place (e j) Φ h1 h2 (h3 j) h x _ _

private theorem esymm_root {O R B : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing B] {q n : ℕ} (β : R →+* B)
    (P : Fin q → Polynomial B) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (emb O R j (MvPolynomial.esymm (Fin n) O k)))
      = algebraMap B (MSplitAlg P n) ((-1) ^ k * (P j).coeff (n - k)) := by
  have h0 := congrArg (fun p => p.coeff (n - k)) (MSplitAlg.prod_root P n j)
  have hc : Multiset.card (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i) = n := by simp
  have h1 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i)
    (k := n - k) (by rw [hc]; omega)
  rw [hc, Multiset.map_map, show n - (n - k) = k by omega, Finset.esymm_map_val] at h1
  simp only [Polynomial.coeff_map] at h0
  rw [map_mul, ← h0, Finset.prod_eq_multiset_prod]
  simp only [Function.comp_def] at h1
  rw [h1, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp [emb, MvPolynomial.esymm, MSplitAlg.root, map_sum, map_prod]

theorem UpperTheory.V.Pa.Lev.multiPsi :
    ∀ (O R B M V : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (tr : V →+ M) (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c → (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) v, tr (t • v) = β t • tr v) → (∀ j k, k ≤ n → ∀ v, tr (act (emb O R j (MvPolynomial.esymm (Fin n) O k)) v) = ((-1) ^ k * (P j).coeff (n - k)) • tr v) → ∀ ψ : V →+ MSplitAlg P n ⊗[B] M, (∀ v, ψ v = ∑ i : Fin q → ι, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ tr (act (∏ j, emb O R j (c (i j))) v)) → ∀ (t : PU R q n) v, ψ (act t v) = Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • ψ v := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β P act tr ι _ a c hd _ _ hβ he ψ hψ
  let π : PU R q n →+* MSplitAlg P n := (Ideal.Quotient.mk (mSplitIdeal P n)).comp (MvPolynomial.map β)
  have hπ : ∀ t, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) = π t := fun _ => rfl
  simp only [hπ] at hψ ⊢
  have sc : ∀ (b : B) (y : MSplitAlg P n) (m : M), y ⊗ₜ[B] (b • m) = (y * algebraMap B _ b) ⊗ₜ[B] m := by
    intro b y m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  have hC : ∀ (r : R) (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (MvPolynomial.C r) w) = (y * π (MvPolynomial.C r)) ⊗ₜ[B] tr w := by
    intro r y w
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply, hβ, sc, ← hπ,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl
  have bal : ∀ j (z : MvPolynomial (Fin n) O), z.IsSymmetric → ∀ (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (emb O R j z) w) = (y * π (emb O R j z)) ⊗ₜ[B] tr w := by
    intro j z hz
    obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective O (σ := Fin n) (n := n) (by simp) ⟨z, hz⟩
    obtain rfl : z = (MvPolynomial.esymmAlgHom (Fin n) O n p : MvPolynomial (Fin n) O) := by rw [hp]
    clear hp hz
    rw [MvPolynomial.esymmAlgHom_apply]
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : emb O R j (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) O (i + 1))
          (MvPolynomial.C r : MvPolynomial (Fin n) O)) = MvPolynomial.C (algebraMap O R r) := by simp [emb]
      rw [this]
      exact hC _
    | add p p' hp hp' =>
      intro y w
      rw [map_add, map_add, map_add, map_add, LinearMap.add_apply, map_add, TensorProduct.tmul_add, hp, hp', mul_add,
        TensorProduct.add_tmul]
    | mul_X p i hp =>
      intro y w
      rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, hp, MvPolynomial.aeval_X, he j _ i.2, sc,
        ← esymm_root (O := O) β P j _ i.2, hπ, mul_assoc]
  intro t
  induction t using MvPolynomial.induction_on with
  | C r =>
    intro v
    rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hC, TensorProduct.smul_tmul',
      smul_eq_mul, mul_comm]
  | add p p' hp hp' =>
    intro v
    rw [map_add, map_add, LinearMap.add_apply, map_add, hp, hp', add_smul]
  | mul_X p ji hp =>
    intro v
    obtain ⟨j, i⟩ := ji
    have hX : (MvPolynomial.X (j, i) : PU R q n) = emb O R j (MvPolynomial.X i) := by simp [emb]
    rw [map_mul, map_mul, Module.End.mul_apply, hp, mul_smul, hX, hψ, hψ, Finset.smul_sum (r := π (emb O R j _))]
    congr 1
    have := many_places (emb O R) (fun s t => π s ⊗ₜ[B] tr (act t v))
      (fun s f => by simp only [map_sum, LinearMap.sum_apply, TensorProduct.tmul_sum])
      (fun s f => by simp only [map_sum, TensorProduct.sum_tmul])
      (fun j s t z hz => by
        show π s ⊗ₜ[B] tr (act (t * emb O R j z) v) = π (s * emb O R j z) ⊗ₜ[B] tr (act t v)
        rw [mul_comm t, map_mul, Module.End.mul_apply, bal j z hz, map_mul]) hd j (MvPolynomial.X i)
    simp only [map_mul, Module.End.mul_apply] at this
    rw [this]
    simp only [TensorProduct.smul_tmul', smul_eq_mul]
