import ReciprocityTheory.DualLattices.ProdDvdOfIso

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

section

variable {R : Type} [CommRing R]

lemma single_smul_self {m : ℕ} (c : Fin m → R) (i : Fin m) :
    c i • (Pi.single i (1 : R ⧸ Ideal.span {c i}) : (i : Fin m) → R ⧸ Ideal.span {c i}) = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
  · simp [Pi.single_eq_of_ne hk]

lemma eq_sum_single {m : ℕ} (c : Fin m → R) (x : (i : Fin m) → R ⧸ Ideal.span {c i}) :
    x = ∑ i, (Quotient.out (x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)]
  simp [Algebra.smul_def]

lemma mem_of_sum_single_eq_zero {m : ℕ} (c : Fin m → R) (r : Fin m → R)
    (h : ∑ k, r k • (Pi.single k (1 : R ⧸ Ideal.span {c k}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) = 0) : ∀ i, r i ∈ Ideal.span {c i} := by
  intro i
  have h1 := congrFun h i
  rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h1
  simp [Algebra.smul_def] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

end

theorem hasLen_ext {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) := by
  classical
  obtain ⟨m, α, ⟨eA⟩, hαa⟩ := ha
  obtain ⟨m', δ, ⟨eD⟩, hδc⟩ := hc
  set gA : Fin m → A := fun i => eA.symm (Pi.single i 1) with hgA
  set gD : Fin m' → D := fun j => eD.symm (Pi.single j 1) with hgD
  have hgA0 : ∀ i, α i • gA i = 0 := fun i => by
    simp only [hgA]
    rw [← map_smul, single_smul_self, map_zero]
  have hgD0 : ∀ j, δ j • gD j = 0 := fun j => by
    simp only [hgD]
    rw [← map_smul, single_smul_self, map_zero]
  have reprA : ∀ y : A, y = ∑ i, (Quotient.out (eA y i) : R) • gA i := fun y => by
    conv_lhs => rw [← eA.symm_apply_apply y, eq_sum_single α (eA y)]
    simp only [hgA, map_sum, map_smul]
  have reprD : ∀ y : D, y = ∑ j, (Quotient.out (eD y j) : R) • gD j := fun y => by
    conv_lhs => rw [← eD.symm_apply_apply y, eq_sum_single δ (eD y)]
    simp only [hgD, map_sum, map_smul]
  have memA : ∀ r : Fin m → R, ∑ i, r i • gA i = 0 → ∀ i, r i ∈ Ideal.span {α i} := by
    intro r hr i
    have h1 : eA (∑ i, r i • gA i) = 0 := by rw [hr, map_zero]
    simp only [hgA, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have memD : ∀ r : Fin m' → R, ∑ j, r j • gD j = 0 → ∀ j, r j ∈ Ideal.span {δ j} := by
    intro r hr i
    have h1 : eD (∑ j, r j • gD j) = 0 := by rw [hr, map_zero]
    simp only [hgD, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have hπι : ∀ y : A, π (ι y) = 0 := fun y => by
    have h1 : ι y ∈ LinearMap.range ι := ⟨y, rfl⟩
    rw [hex] at h1
    exact h1
  choose b hb using fun j => hπ (gD j)
  have hdb : ∀ j, ∃ y : A, ι y = δ j • b j := fun j => by
    have h1 : δ j • b j ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_smul, hb, hgD0]
    rw [← hex] at h1
    exact h1
  choose aj haj using hdb
  set x : Fin m' → Fin m → R := fun j i => (Quotient.out (eA (aj j) i) : R) with hxdef
  have hx : ∀ j, aj j = ∑ i, x j i • gA i := fun j => reprA (aj j)
  set gen : Fin m ⊕ Fin m' → B := Sum.elim (fun i => ι (gA i)) b with hgen
  let Φ : (Fin m ⊕ Fin m' → R) →ₗ[R] B :=
    { toFun := fun p => ∑ k, p k • gen k
      map_add' := fun p q => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c p => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ p, Φ p = ∑ i, p (Sum.inl i) • ι (gA i) + ∑ j, p (Sum.inr j) • b j := fun p => by
    show ∑ k, p k • gen k = _
    rw [Fintype.sum_sum_type]
    rfl
  let X : Matrix (Fin m ⊕ Fin m') (Fin m ⊕ Fin m') R :=
    Matrix.fromBlocks (Matrix.diagonal α) (Matrix.of fun i j => -x j i) 0 (Matrix.diagonal δ)
  have hdet : X.det = (∏ i, α i) * ∏ j, δ j := by
    simp [X, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  have hXl : ∀ w i, X.mulVec w (Sum.inl i) = α i * w (Sum.inl i) - ∑ j, x j i * w (Sum.inr j) := by
    intro w i
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hXr : ∀ w j, X.mulVec w (Sum.inr j) = δ j * w (Sum.inr j) := by
    intro w j
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply]
  have hιx : ∀ j, ι (aj j) = ∑ i, x j i • ι (gA i) := fun j => by
    rw [hx j, map_sum]
    simp only [map_smul]
  have hΦX : ∀ w, Φ (X.mulVec w) = 0 := by
    intro w
    rw [hΦ]
    simp only [hXl, hXr, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∀ i, (α i * w (Sum.inl i)) • ι (gA i) = 0 := by
      intro i
      rw [mul_comm, mul_smul, ← map_smul, hgA0, map_zero, smul_zero]
    have e2 : ∀ j, (δ j * w (Sum.inr j)) • b j = w (Sum.inr j) • ι (aj j) := by
      intro j
      rw [mul_comm, mul_smul, haj]
    have e3 : ∑ i, (∑ j, x j i * w (Sum.inr j)) • ι (gA i) = ∑ j, w (Sum.inr j) • ι (aj j) := by
      simp only [hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    simp only [e1, e2, Finset.sum_const_zero, zero_sub, e3, neg_add_cancel]
  have hker : LinearMap.ker Φ = LinearMap.range X.mulVecLin := by
    ext p
    constructor
    · intro hp
      rw [LinearMap.mem_ker, hΦ] at hp
      have hπs : ∑ j, p (Sum.inr j) • gD j = 0 := by
        have h1 := congrArg π hp
        simpa [map_add, map_sum, map_smul, hb, hπι] using h1
      choose t ht using fun j => Ideal.mem_span_singleton'.1 (memD _ hπs j)
      have hsb : ∑ j, p (Sum.inr j) • b j = ι (∑ i, (∑ j, t j * x j i) • gA i) := by
        rw [map_sum]
        simp only [map_smul]
        have e4 : ∀ j, p (Sum.inr j) • b j = t j • ι (aj j) := by
          intro j
          rw [← ht j, mul_smul, haj]
        simp only [e4, hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hι0 : ι (∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i) = 0 := by
        rw [← hp, hsb]
        simp only [add_smul, Finset.sum_add_distrib, map_add, map_sum, map_smul]
      have hA0 : ∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i = 0 :=
        hι (hι0.trans (map_zero ι).symm)
      choose q hq using fun i => Ideal.mem_span_singleton'.1 (memA _ hA0 i)
      refine ⟨Sum.elim q t, ?_⟩
      funext k
      cases k with
      | inl i =>
        show X.mulVec (Sum.elim q t) (Sum.inl i) = p (Sum.inl i)
        rw [hXl]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have hqi := hq i
        rw [show ∑ j, x j i * t j = ∑ j, t j * x j i from Finset.sum_congr rfl fun j _ => mul_comm _ _]
        linear_combination hqi
      | inr j =>
        show X.mulVec (Sum.elim q t) (Sum.inr j) = p (Sum.inr j)
        rw [hXr]
        simp only [Sum.elim_inr]
        rw [mul_comm]
        exact ht j
    · rintro ⟨w, rfl⟩
      exact hΦX w
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin m' → R := fun j => (Quotient.out (eD (π y) j) : R) with hs
    have hys : y - ∑ j, s j • b j ∈ LinearMap.range ι := by
      rw [hex, LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hb]
      rw [← reprD (π y), sub_self]
    obtain ⟨zA, hzA⟩ := hys
    refine ⟨Sum.elim (fun i => (Quotient.out (eA zA i) : R)) s, ?_⟩
    rw [hΦ]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have e5 : ∑ i, (Quotient.out (eA zA i) : R) • ι (gA i) = ι zA := by
      conv_rhs => rw [reprA zA]
      rw [map_sum]
      simp only [map_smul]
    rw [e5, hzA, sub_add_cancel]
  let e1 : ((Fin m ⊕ Fin m' → R) ⧸ LinearMap.range X.mulVecLin) ≃ₗ[R] B :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  obtain ⟨k, cc, ⟨e2⟩, hcc⟩ := hS2 (Fin m ⊕ Fin m') X
  refine ⟨k, cc, ⟨e1.symm.trans e2⟩, ?_⟩
  rw [hcc, hdet, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod, hαa, hδc]

end ReciprocityTheory.PGsh.Up
