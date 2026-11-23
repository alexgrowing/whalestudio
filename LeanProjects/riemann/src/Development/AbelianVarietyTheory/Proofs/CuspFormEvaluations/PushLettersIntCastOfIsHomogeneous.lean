import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo

open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.Harm

section Free

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ ι : Type*}

noncomputable def basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (b.repr (coeff m P) i)

theorem coeff_basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S)
    (m : σ →₀ ℕ) : coeff m (basisComponent b i P) = b.repr (coeff m P) i := by
  classical
  rw [basisComponent, coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro m' _ h; simp [coeff_monomial, h]
  · intro h; simp [notMem_support_iff.1 h]

theorem exists_eq_sum_basisComponent (b : Module.Basis ι R S) (P : MvPolynomial σ S) :
    ∃ J : Finset ι, P = ∑ i ∈ J, b i • MvPolynomial.map (algebraMap R S) (basisComponent b i P) := by
  classical
  refine ⟨P.support.biUnion fun m => (b.repr (coeff m P)).support, ?_⟩
  ext m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_basisComponent, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (coeff m P), Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset (s := P.support.biUnion fun m => (b.repr (coeff m P)).support)]
  · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
  · by_cases hm : m ∈ P.support
    · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m P)).support) hm
    · simp [notMem_support_iff.1 hm]
  · simp

theorem basisComponent_sum (b : Module.Basis ι R S) (J : Finset ι) (Q : ι → MvPolynomial σ R)
    {i : ι} (hi : i ∈ J) :
    basisComponent b i (∑ j ∈ J, b j • MvPolynomial.map (algebraMap R S) (Q j)) = Q i := by
  classical
  ext m
  simp only [coeff_basisComponent, coeff_sum, coeff_smul, coeff_map, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i] <;> simp +contextual [hi]

variable {T : Type*} {p q : ℕ} {κ : Type*} [Fintype κ] {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}

theorem basisComponent_mem_rowHighest (b : Module.Basis ι R S) (i : ι) {P : Poly S T p q κ}
    (hP : P ∈ rowHighest S c c') : basisComponent b i P ∈ rowHighest R c c' := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
  by_cases hi : i ∈ J
  swap
  · have : basisComponent b i P = 0 := by
      rw [← basisComponent_sum b (insert i J)
        (fun j => if j = i then 0 else basisComponent b j P) (Finset.mem_insert_self i J)
        |>.trans (if_pos rfl)]
      congr 1
      rw [Finset.sum_insert hi, if_pos rfl, map_zero, smul_zero, zero_add]
      refine hJ.trans (Finset.sum_congr rfl fun j hj => ?_)
      rw [if_neg (by rintro rfl; exact hi hj)]
    rw [this]; exact zero_mem _
  refine mem_rowHighest_iff_rowAdd.2 ⟨fun t a b' => ?_, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => ?_⟩
  · have := h₁ t a b'
    rw [hJ, map_sum] at this
    simp only [map_smul, ← map_laplacian] at this
    rw [← basisComponent_sum b J (fun j => laplacian t a b' (basisComponent b j P)) hi, this]
    simp [basisComponent]
  · rw [coeff_basisComponent, e]; simp
  · have := h₃ t r r' hr s
    conv_lhs at this => rw [hJ, map_sum]
    simp only [map_smul, ← map_intCast (algebraMap R S), ← map_rowAdd] at this
    rw [← basisComponent_sum b J (fun j => rowAdd t r r' (s : R) (basisComponent b j P)) hi, this]

variable (R S c c') in

theorem span_map_rowHighest [Module.Free R S] :
    Submodule.span S (MvPolynomial.map (algebraMap R S) ''
      (rowHighest R (κ := κ) c c' : Set (Poly R T p q κ))) = rowHighest S c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    exact map_mem_rowHighest _ hP
  · intro P hP
    let b := Module.Free.chooseBasis R S
    obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
    rw [hJ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, basisComponent_mem_rowHighest b i hP, rfl⟩)

end Free

section Scale

variable {R : Type*} [CommRing R] {T : Type*} {p q : ℕ} {κ : Type*}

theorem aeval_C_mul_X_of_isHomogeneous {σ : Type*} (r : R) {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) : aeval (fun v => (C r * X v : MvPolynomial σ R)) P = r ^ d • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ v ∈ m.support, m v = d := by
    rw [← hP (mem_support_iff.1 hm), Finsupp.weight_apply]; simp [Finsupp.sum]
  rw [aeval_monomial, monomial_eq, smul_eq_C_mul, ← hd]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow,
    algebraMap_eq]
  ring

end Scale

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type*} [Field K]
  {T : Type*} {p q n : ℕ}

noncomputable abbrev ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E ≃ₐ[_] E)

theorem ccHom_apply (x : E) : ccHom E x = cc x := rfl

theorem herm_one_eq_sum (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

variable (p q) in

noncomputable def symO (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Subalgebra (𝓞 K) (Poly K T p q (Fin n)) :=
  Algebra.adjoin (𝓞 K)
    ({P | ∃ t a, ∃ v ∈ Λ, P = xForm t a fun k => τ t (v k)} ∪
      {P | ∃ t b, ∃ v ∈ Λ, P = yForm t b fun k => τ t (cc (v k))})

noncomputable def Ha (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Poly K T p q (Fin n)) :=
  (rowHighest K c c').restrictScalars (𝓞 K) ⊓ Subalgebra.toSubmodule (symO p q τ Λ)

variable (τ : T → E →+* K) {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
  {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {P : Poly K T p q (Fin n)}

theorem mem_Ha : P ∈ Ha τ c c' Λ ↔ P ∈ rowHighest K c c' ∧ P ∈ symO p q τ Λ := Iff.rfl

theorem xForm_mem_symO (t : T) (a : Fin p) {v : Fin n → E} (hv : v ∈ Λ) :
    (xForm t a fun k => τ t (v k)) ∈ symO p q τ Λ :=
  Algebra.subset_adjoin (Or.inl ⟨t, a, v, hv, rfl⟩)

theorem yForm_mem_symO (t : T) (b : Fin q) {v : Fin n → E} (hv : v ∈ Λ) :
    (yForm t b fun k => τ t (cc (v k))) ∈ symO p q τ Λ :=
  Algebra.subset_adjoin (Or.inr ⟨t, b, v, hv, rfl⟩)

theorem symO_le_iff {A : Subalgebra (𝓞 K) (Poly K T p q (Fin n))} :
    symO p q τ Λ ≤ A ↔ (∀ t a, ∀ v ∈ Λ, (xForm t a fun k => τ t (v k)) ∈ A) ∧
      ∀ t b, ∀ v ∈ Λ, (yForm t b fun k => τ t (cc (v k))) ∈ A := by
  rw [symO, Algebra.adjoin_le_iff, Set.union_subset_iff]
  refine and_congr ⟨fun h t a v hv => h ⟨t, a, v, hv, rfl⟩, ?_⟩
    ⟨fun h t a v hv => h ⟨t, a, v, hv, rfl⟩, ?_⟩
  all_goals rintro h _ ⟨t, a, v, hv, rfl⟩; exact h t a v hv

theorem symO_mono (h : Λ ≤ Λ') : symO p q τ Λ ≤ symO p q τ Λ' :=
  (symO_le_iff τ).2 ⟨fun t a _ hv => xForm_mem_symO τ t a (h hv),
    fun t b _ hv => yForm_mem_symO τ t b (h hv)⟩

theorem Ha_mono (h : Λ ≤ Λ') : Ha τ c c' Λ ≤ Ha τ c c' Λ' :=
  fun _ hP => ⟨hP.1, symO_mono τ h hP.2⟩

theorem det_mem_subalgebra {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    [DecidableEq ι] (B : Subalgebra R A) {M : Matrix ι ι A} (h : ∀ i j, M i j ∈ B) : M.det ∈ B := by
  rw [det_apply']
  exact B.sum_mem fun s _ => B.mul_mem (intCast_mem B _) (B.prod_mem fun i _ => h _ _)

variable (c c') in

theorem minorProd_mem_symO [Fintype T] {e : T → Fin p → Fin n → E} {f : T → Fin q → Fin n → E}
    (he : ∀ t a, e t a ∈ Λ) (hf : ∀ t b, f t b ∈ Λ) :
    minorProd c c' (fun t a k => τ t (e t a k)) (fun t b k => τ t (cc (f t b k))) ∈
      symO p q τ Λ :=
  Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
    (Subalgebra.prod_mem _ fun _ _ => Subalgebra.pow_mem _
      (det_mem_subalgebra _ fun _ _ => xForm_mem_symO τ t _ (he t _)) _)
    (Subalgebra.prod_mem _ fun _ _ => Subalgebra.pow_mem _
      (det_mem_subalgebra _ fun _ _ => yForm_mem_symO τ t _ (hf t _)) _)

variable (c c') in

theorem minorProd_mem_Ha [Fintype T] {e : T → Fin p → Fin n → E} {f : T → Fin q → Fin n → E}
    (he : ∀ t a, e t a ∈ Λ) (hf : ∀ t b, f t b ∈ Λ) (h : ∀ t a b, herm 1 (e t a) (f t b) = 0) :
    minorProd c c' (fun t a k => τ t (e t a k)) (fun t b k => τ t (cc (f t b k))) ∈ Ha τ c c' Λ :=
  ⟨minorProd_mem_rowHighest c c' fun t a b => by
    have := congrArg (τ t) (h t a b)
    rw [herm_one_eq_sum] at this
    simpa [dotProduct] using this, minorProd_mem_symO τ c c' he hf⟩

variable (c c') in

theorem minorProd_conj_mem_Ha [Fintype T] (hΛ : ∀ v ∈ Λ, (fun k => cc (v k)) ∈ Λ')
    {e : T → Fin p → Fin n → E} {f : T → Fin q → Fin n → E}
    (he : ∀ t a, e t a ∈ Λ) (hf : ∀ t b, f t b ∈ Λ) (h : ∀ t a b, herm 1 (f t b) (e t a) = 0) :
    minorProd c c' (fun t a k => τ t (cc (e t a k))) (fun t b k => τ t (f t b k)) ∈
      Ha τ c c' Λ' := by
  have hcc (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
  have := minorProd_mem_Ha τ c c' (e := fun t a k => cc (e t a k)) (f := fun t b k => cc (f t b k))
    (fun t a => hΛ _ (he t a)) (fun t b => hΛ _ (hf t b)) fun t a b => by
      rw [← h t a b, herm_one_eq_sum, herm_one_eq_sum]
      simp only [hcc, mul_comm]
  simpa only [hcc] using this

variable (p q) in

noncomputable def pushLetters (A : Matrix (Fin n) (Fin n) E) :
    Poly K T p q (Fin n) →ₐ[K] Poly K T p q (Fin n) :=
  colSubst (fun t => (A.map (τ t))ᵀ) fun t => A.map ((τ t).comp (ccHom E))

theorem pushLetters_xForm (A : Matrix (Fin n) (Fin n) E) (t : T) (a : Fin p) (v : Fin n → E) :
    pushLetters p q τ A (xForm t a fun k => τ t (v k)) = xForm t a fun k => τ t ((A *ᵥ v) k) := by
  rw [pushLetters, colSubst_xForm, vecMul_transpose]
  congr 1; funext k; simp [mulVec, dotProduct]

theorem pushLetters_yForm (A : Matrix (Fin n) (Fin n) E) (t : T) (b : Fin q) (v : Fin n → E) :
    pushLetters p q τ A (yForm t b fun k => τ t (cc (v k))) =
      yForm t b fun k => τ t (cc ((A *ᵥ v) k)) := by
  rw [pushLetters, colSubst_yForm]
  congr 1; funext k; simp [mulVec, dotProduct, ← ccHom_apply]

theorem eq_pushLetters (A : Matrix (Fin n) (Fin n) E)
    (F : Poly K T p q (Fin n) →ₐ[K] Poly K T p q (Fin n))
    (hx : ∀ t a (v : Fin n → E), F (xForm t a fun k => τ t (v k)) =
      xForm t a fun k => τ t ((A *ᵥ v) k))
    (hy : ∀ t b (v : Fin n → E), F (yForm t b fun k => τ t (cc (v k))) =
      yForm t b fun k => τ t (cc ((A *ᵥ v) k))) : F = pushLetters p q τ A := by
  refine MvPolynomial.algHom_ext fun ⟨t, r, k⟩ => ?_
  have h₁ : (fun l => τ t ((Pi.single k 1 : Fin n → E) l)) = Pi.single k 1 := by
    funext l; simp [Pi.single_apply, apply_ite (τ t)]
  have h₂ : (fun l => τ t (cc ((Pi.single k 1 : Fin n → E) l))) = Pi.single k 1 := by
    funext l; rw [← ccHom_apply]; by_cases h : l = k <;> simp [h]
  rcases r with a | b
  · rw [← xForm_single, ← h₁, hx, pushLetters_xForm]
  · rw [← yForm_single, ← h₂, hy, pushLetters_yForm]

theorem pushLetters_mul (A B : Matrix (Fin n) (Fin n) E) :
    pushLetters p q τ (A * B) = (pushLetters p q τ A).comp (pushLetters p q τ B) :=
  (eq_pushLetters τ _ _
    (fun t a v => by rw [AlgHom.comp_apply, pushLetters_xForm, pushLetters_xForm, mulVec_mulVec])
    fun t b v => by rw [AlgHom.comp_apply, pushLetters_yForm, pushLetters_yForm, mulVec_mulVec]).symm

theorem map_pushLetters_symO (A : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    (symO p q τ Λ).map ((pushLetters p q τ A).restrictScalars (𝓞 K)) =
      symO p q τ (Λ.map (A.mulVecLin.restrictScalars (𝓞 E))) := by
  apply le_antisymm
  · rw [Subalgebra.map_le, symO_le_iff]
    refine ⟨fun t a v hv => ?_, fun t b v hv => ?_⟩
    · rw [Subalgebra.mem_comap, AlgHom.restrictScalars_apply, pushLetters_xForm]
      exact xForm_mem_symO τ t a (Submodule.mem_map_of_mem hv)
    · rw [Subalgebra.mem_comap, AlgHom.restrictScalars_apply, pushLetters_yForm]
      exact yForm_mem_symO τ t b (Submodule.mem_map_of_mem hv)
  · rw [symO_le_iff]
    constructor
    · rintro t a _ ⟨v, hv, rfl⟩
      exact ⟨_, xForm_mem_symO τ t a hv, pushLetters_xForm τ A t a v⟩
    · rintro t b _ ⟨v, hv, rfl⟩
      exact ⟨_, yForm_mem_symO τ t b hv, pushLetters_yForm τ A t b v⟩

theorem pushLetters_mem_symO {A : Matrix (Fin n) (Fin n) E} (h : ∀ v ∈ Λ, A *ᵥ v ∈ Λ')
    (hP : P ∈ symO p q τ Λ) : pushLetters p q τ A P ∈ symO p q τ Λ' := by
  refine symO_mono τ (Λ := Λ.map (A.mulVecLin.restrictScalars (𝓞 E))) ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩; exact h v hv
  · rw [← map_pushLetters_symO]; exact ⟨P, hP, rfl⟩

theorem pushLetters_intCast_of_isHomogeneous (M : ℤ) {d : ℕ} (hP : P.IsHomogeneous d) :
    pushLetters p q τ ((M : E) • 1) P = (M : 𝓞 K) ^ d • P := by
  have : (aeval fun v => C (M : K) * X v) =
      pushLetters p q τ ((M : E) • (1 : Matrix (Fin n) (Fin n) E)) := by
    refine eq_pushLetters τ _ _ (fun t a v => ?_) fun t b v => ?_
    · simp [xForm_apply, smul_mulVec, mul_left_comm, mul_assoc]
    · simp [yForm_apply, smul_mulVec, mul_left_comm, mul_assoc, ← ccHom_apply]
  rw [← this, aeval_C_mul_X_of_isHomogeneous _ hP]
  change _ = algebraMap (𝓞 K) K ((M : 𝓞 K) ^ d) • P
  rw [map_pow, map_intCast]

theorem pow_smul_mem_symO {M : ℤ} (h : ∀ v ∈ Λ, M • v ∈ Λ') {d : ℕ} (hd : P.IsHomogeneous d)
    (hP : P ∈ symO p q τ Λ) : (M : 𝓞 K) ^ d • P ∈ symO p q τ Λ' := by
  rw [← pushLetters_intCast_of_isHomogeneous τ M hd]
  refine pushLetters_mem_symO τ (fun v hv => ?_) hP
  rw [smul_mulVec, one_mulVec, Int.cast_smul_eq_zsmul]; exact h v hv

theorem pow_smul_mem_Ha [Fintype T] {M : ℤ} (h : ∀ v ∈ Λ, M • v ∈ Λ') (hP : P ∈ Ha τ c c' Λ) :
    (M : 𝓞 K) ^ typeDegree c c' • P ∈ Ha τ c c' Λ' :=
  ⟨((rowHighest K c c').restrictScalars (𝓞 K)).smul_mem _ hP.1,
    pow_smul_mem_symO τ h (isHomogeneous_of_mem_rowHighest hP.1) hP.2⟩

theorem pow_zsmul_mem_Ha [Fintype T] {M : ℤ} (h : ∀ v ∈ Λ, M • v ∈ Λ') (hP : P ∈ Ha τ c c' Λ) :
    M ^ typeDegree c c' • P ∈ Ha τ c c' Λ' := by
  have := pow_smul_mem_Ha τ h hP
  rw [← Int.cast_pow] at this
  exact (Int.cast_smul_eq_zsmul (𝓞 K) (M ^ typeDegree c c') P) ▸ this

theorem transpose_mul_map_ccHom_eq_one {A : Matrix (Fin n) (Fin n) E}
    (hA : ∀ x y, herm 1 (A *ᵥ x) (A *ᵥ y) = herm 1 x y) : Aᵀ * A.map (ccHom E) = 1 := by
  ext i j
  have := hA (Pi.single i 1) (Pi.single j 1)
  rw [herm_one_eq_sum, herm_one_eq_sum] at this
  simp only [mulVec_single_one, col_apply, ← ccHom_apply] at this
  rw [mul_apply]
  refine this.trans ?_
  by_cases h : i = j <;> simp [Pi.single_apply, one_apply, h, eq_comm]

theorem pushLetters_eq_colAct {γ : GL (Fin n) E}
    (hγ : ∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y) (P : Poly K T p q (Fin n)) :
    pushLetters p q τ γ.val P = colAct K T p q (Fin n)
      (fun t => Matrix.GeneralLinearGroup.map ((τ t).comp (ccHom E)) γ) P := by
  rw [colAct_apply, pushLetters]
  congr 2
  funext t
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  have := congrArg (fun B => B.map (τ t)) (transpose_mul_map_ccHom_eq_one hγ)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem pushLetters_mem_rowHighest_iff {γ : GL (Fin n) E}
    (hγ : ∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y) :
    pushLetters p q τ γ.val P ∈ rowHighest K c c' ↔ P ∈ rowHighest K c c' := by
  rw [pushLetters_eq_colAct τ hγ, colAct_mem_rowHighest_iff]

variable (c c') in

theorem map_pushLetters_Ha {γ : GL (Fin n) E}
    (hγ : ∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y)
    (Λ : Submodule (𝓞 E) (Fin n → E)) :
    (Ha τ c c' Λ).map ((pushLetters p q τ γ.val).toLinearMap.restrictScalars (𝓞 K)) =
      Ha τ c c' (Λ.map (γ.val.mulVecLin.restrictScalars (𝓞 E))) := by
  ext Q
  rw [mem_Ha, ← map_pushLetters_symO]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨(pushLetters_mem_rowHighest_iff τ hγ).2 hP.1, P, hP.2, rfl⟩
  · rintro ⟨hQ, P, hP, rfl⟩
    exact ⟨P, ⟨(pushLetters_mem_rowHighest_iff τ hγ).1 hQ, hP⟩, rfl⟩

omit [IsCMField E] in

theorem exists_zsmul_mem_of_mem_span {v : Fin n → E} (hv : v ∈ Submodule.span E (Λ : Set _)) :
    ∃ N : ℤ, N ≠ 0 ∧ N • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_ne_zero, by simpa using hv⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨M, hM, hv⟩ := hv
    obtain ⟨N, hN, hw⟩ := hw
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hv N
    · rw [mul_smul]; exact zsmul_mem hw M
  | smul r v _ hv =>
    obtain ⟨N, hN, hv⟩ := hv
    have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
    obtain ⟨M, hM, hr⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) r).exists_integral_multiple
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have := Λ.smul_mem (⟨M • r, hr⟩ : 𝓞 E) hv
    convert this using 1
    change _ = (M • r) • N • v
    rw [smul_assoc, smul_comm r N v, mul_smul]

omit [IsCMField E] in

theorem exists_zsmul_le (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ v ∈ Λ, N • v ∈ Λ' := by
  classical
  obtain ⟨s, rfl⟩ := hΛ
  choose N hN hN' using fun v => exists_zsmul_mem_of_mem_span (Λ := Λ') (v := v) (hΛ' ▸ trivial)
  refine ⟨∏ w ∈ s, N w, Finset.prod_ne_zero_iff.2 fun w _ => hN w, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv => rw [← Finset.prod_erase_mul s N hv, mul_smul]; exact zsmul_mem (hN' v) _
  | zero => simp
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | smul r v _ hv => rw [smul_comm]; exact Λ'.smul_mem r hv

omit [NumberField E] [IsCMField E] in

theorem mem_pi_one_iff {v : Fin n → E} :
    v ∈ Submodule.pi Set.univ (fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (v k) := by
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [NumberField E] [IsCMField E] in

theorem span_range_single_eq_pi_one :
    Submodule.span (𝓞 E) (Set.range fun k : Fin n => (Pi.single k 1 : Fin n → E)) =
      Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine mem_pi_one_iff.2 fun l => ?_
    by_cases h : l = k <;> simp [h, isIntegral_one, isIntegral_zero]
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hv k trivial)
    have : (Pi.single k (v k) : Fin n → E) = y • (Pi.single k 1 : Fin n → E) := by
      rw [← Pi.single_smul', Algebra.smul_def, mul_one, hy]
    rw [this]
    exact Submodule.smul_mem _ y (Submodule.subset_span ⟨k, rfl⟩)

omit [NumberField E] [IsCMField E] in

theorem fg_pi_one : (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)).FG :=
  span_range_single_eq_pi_one (E := E) ▸ Submodule.fg_span (Set.finite_range _)

omit [NumberField E] [IsCMField E] in

theorem span_pi_one_eq_top : Submodule.span E
    (Submodule.pi Set.univ (fun _ : Fin n => (1 : Submodule (𝓞 E) E)) : Set (Fin n → E)) = ⊤ := by
  rw [← span_range_single_eq_pi_one, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2; funext k; simp

theorem mem_range_map_ringOfIntegers_iff {σ : Type*} {P : MvPolynomial σ K} :
    (∃ Q, MvPolynomial.map (algebraMap (𝓞 K) K) Q = P) ↔ ∀ m, IsIntegral ℤ (coeff m P) := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]; exact (coeff m Q).isIntegral_coe
  · intro h
    refine ⟨∑ m ∈ P.support, monomial m ⟨_, h m⟩, ?_⟩
    conv_rhs => rw [P.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => map_monomial _ _ _

theorem symO_pi_one : symO p q τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
    (mapAlgHom (σ := Var T p q (Fin n)) (Algebra.ofId (𝓞 K) K)).range := by
  apply le_antisymm
  · refine (symO_le_iff τ).2 ⟨fun t a v hv => ?_, fun t b v hv => ?_⟩
    · exact ⟨xForm t a fun k => ⟨_, map_isIntegral_int (τ t) (mem_pi_one_iff.1 hv k)⟩,
        map_xForm (algebraMap (𝓞 K) K) t a _⟩
    · exact ⟨yForm t b fun k =>
        ⟨_, map_isIntegral_int ((τ t).comp (ccHom E)) (mem_pi_one_iff.1 hv k)⟩,
        map_yForm (algebraMap (𝓞 K) K) t b _⟩
  · rintro _ ⟨Q, rfl⟩
    change mapAlgHom (Algebra.ofId (𝓞 K) K) Q ∈ _
    induction Q using MvPolynomial.induction_on with
    | C r => rw [← algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P v hP =>
      rw [map_mul]
      refine mul_mem hP ?_
      obtain ⟨t, r, k⟩ := v
      have hk : (Pi.single k 1 : Fin n → E) ∈
          Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E) :=
        span_range_single_eq_pi_one (E := E) ▸ Submodule.subset_span ⟨k, rfl⟩
      have h₁ : (fun l => τ t ((Pi.single k 1 : Fin n → E) l)) = Pi.single k 1 := by
        funext l; simp [Pi.single_apply, apply_ite (τ t)]
      have h₂ : (fun l => τ t (cc ((Pi.single k 1 : Fin n → E) l))) = Pi.single k 1 := by
        funext l; rw [← ccHom_apply]; by_cases h : l = k <;> simp [h]
      change MvPolynomial.map (algebraMap (𝓞 K) K) _ ∈ _
      rw [map_X]
      rcases r with a | b
      · rw [← xForm_single, ← h₁]; exact xForm_mem_symO τ t a hk
      · rw [← yForm_single, ← h₂]; exact yForm_mem_symO τ t b hk

theorem mem_symO_pi_one_iff :
    P ∈ symO p q τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ m, IsIntegral ℤ (coeff m P) := by
  rw [symO_pi_one, ← mem_range_map_ringOfIntegers_iff]; rfl

variable (c c') in

theorem Ha_pi_one_eq_map :
    Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
      (rowHighest (𝓞 K) c c').map
        (mapAlgHom (σ := Var T p q (Fin n)) (Algebra.ofId (𝓞 K) K)).toLinearMap := by
  ext P
  rw [mem_Ha, symO_pi_one]
  constructor
  · rintro ⟨hP, Q, rfl⟩
    exact ⟨Q, (map_mem_rowHighest_iff (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 hP, rfl⟩
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨map_mem_rowHighest (algebraMap (𝓞 K) K) hQ, Q, rfl⟩

variable [NumberField K]

variable (c c') in

theorem Ha_pi_one_eq_span :
    Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
      Submodule.span (𝓞 K) (MvPolynomial.map (Int.castRingHom K) ''
        (rowHighest ℤ (κ := Fin n) c c' : Set (Poly ℤ T p q (Fin n)))) := by
  rw [Ha_pi_one_eq_map, ← span_map_rowHighest ℤ (𝓞 K), Submodule.map_span, Set.image_image]
  congr 2
  funext P
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [MvPolynomial.map_map]
  congr 2

variable [Fintype T]

variable (c c') in

theorem fg_Ha (hΛ : Λ.FG) : (Ha τ c c' Λ).FG := by
  obtain ⟨N, hN, h⟩ := exists_zsmul_le hΛ (span_pi_one_eq_top (E := E))
  have h₀ : (Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))).FG := by
    rw [Ha_pi_one_eq_map]
    exact (Module.Finite.iff_fg.1 inferInstance).map _
  have hd : (N : 𝓞 K) ^ typeDegree c c' ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.2 hN)
  refine Submodule.fg_of_fg_map_injective
    (LinearMap.lsmul (𝓞 K) (Poly K T p q (Fin n)) ((N : 𝓞 K) ^ typeDegree c c'))
    (LinearMap.lsmul_injective hd) (h₀.of_le ?_)
  rintro _ ⟨P, hP, rfl⟩
  exact pow_smul_mem_Ha τ h hP

theorem exists_zsmul_mem_Ha (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hP : P ∈ rowHighest K c c') : ∃ N : ℤ, N ≠ 0 ∧ N • P ∈ Ha τ c c' Λ := by
  classical
  obtain ⟨N, hN, h⟩ := exists_zsmul_le (fg_pi_one (E := E)) hΛ
  have : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨M, hM, hM'⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (P.support.image fun m => coeff m P)
  have h₀ : M • P ∈ Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
    refine ⟨zsmul_mem hP M, (mem_symO_pi_one_iff τ).2 fun m => ?_⟩
    rw [coeff_smul]
    by_cases hm : m ∈ P.support
    · exact hM' _ (Finset.mem_image_of_mem _ hm)
    · rw [notMem_support_iff.1 hm, smul_zero]; exact isIntegral_zero
  refine ⟨N ^ typeDegree c c' * M, mul_ne_zero (pow_ne_zero _ hN) hM, ?_⟩
  rw [mul_smul]
  exact pow_zsmul_mem_Ha τ h h₀

variable (c c') in

theorem span_Ha (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    Submodule.span K (Ha τ c c' Λ : Set (Poly K T p q (Fin n))) = rowHighest K c c' := by
  refine le_antisymm (Submodule.span_le.2 fun P hP => hP.1) fun P hP => ?_
  obtain ⟨N, hN, h⟩ := exists_zsmul_mem_Ha τ hΛ hP
  rw [← Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hN : (N : K) ≠ 0), Int.cast_smul_eq_zsmul]
  exact Submodule.subset_span h

variable (c c') in

theorem Ha_ne_bot (h : p + q ≤ n) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    Ha τ c c' Λ ≠ ⊥ := fun e =>
  rowHighest_ne_bot (R := K) h c c' (by rw [← span_Ha τ c c' hΛ, e]; simp)

omit [NumberField K] in
variable (c c') in

theorem pow_zsmul_Ha_of_isCoprime {ℓ M : ℤ} (hM : IsCoprime M ℓ) (h : ∀ v ∈ Λ, M • v ∈ Λ')
    (h' : ∀ v ∈ Λ', M • v ∈ Λ) :
    IsCoprime (M ^ typeDegree c c') ℓ ∧
      (∀ P ∈ Ha τ c c' Λ, M ^ typeDegree c c' • P ∈ Ha τ c c' Λ') ∧
      ∀ P ∈ Ha τ c c' Λ', M ^ typeDegree c c' • P ∈ Ha τ c c' Λ := by
  refine ⟨hM.pow_left, fun P hP => ?_, fun P hP => ?_⟩
  · exact pow_zsmul_mem_Ha τ h hP
  · exact pow_zsmul_mem_Ha τ h' hP

variable (c c' Λ) in

theorem integral_harmonic_on_lattice (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    (∀ (e : T → Fin p → Fin n → E) (f : T → Fin q → Fin n → E), (∀ t a, e t a ∈ Λ) →
      (∀ t b, f t b ∈ Λ) → (∀ t a b, herm 1 (e t a) (f t b) = 0) →
      minorProd c c' (fun t a k => τ t (e t a k)) (fun t b k => τ t (cc (f t b k))) ∈
        Ha τ c c' Λ) ∧
    ((Ha τ c c' Λ).FG ∧
      Submodule.span K (Ha τ c c' Λ : Set (Poly K T p q (Fin n))) = rowHighest K c c') ∧
    ((∀ P, P ∈ symO p q τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
        ∀ m, IsIntegral ℤ (coeff m P)) ∧
      Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
        Submodule.span (𝓞 K) (MvPolynomial.map (Int.castRingHom K) ''
          (rowHighest ℤ (κ := Fin n) c c' : Set (Poly ℤ T p q (Fin n))))) ∧
    (∀ γ : GL (Fin n) E, (∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y) →
      ∀ F, F = colAct K T p q (Fin n)
          (fun t => Matrix.GeneralLinearGroup.map ((τ t).comp (ccHom E)) γ) →
        (∀ t a (v : Fin n → E),
          F (xForm t a fun k => τ t (v k)) = xForm t a fun k => τ t ((γ.val *ᵥ v) k)) ∧
        (∀ t b (v : Fin n → E),
          F (yForm t b fun k => τ t (cc (v k))) = yForm t b fun k => τ t (cc ((γ.val *ᵥ v) k))) ∧
        (∀ P, F P ∈ rowHighest K c c' ↔ P ∈ rowHighest K c c') ∧
        F '' (Ha τ c c' Λ : Set (Poly K T p q (Fin n))) =
          Ha τ c c' (Λ.map (γ.val.mulVecLin.restrictScalars (𝓞 E)))) ∧
    ∀ (Λ' : Submodule (𝓞 E) (Fin n → E)) (M : ℤ), (∀ v ∈ Λ, M • v ∈ Λ') →
      ∀ P ∈ Ha τ c c' Λ, M ^ typeDegree c c' • P ∈ Ha τ c c' Λ' := by
  refine ⟨fun e f => minorProd_mem_Ha τ c c', ⟨fg_Ha τ c c' hfg, span_Ha τ c c' hspan⟩,
    ⟨fun P => mem_symO_pi_one_iff τ, Ha_pi_one_eq_span τ c c'⟩, ?_, fun Λ' M h P hP => ?_⟩
  · rintro γ hγ _ rfl
    simp only [← pushLetters_eq_colAct τ hγ, pushLetters_xForm, pushLetters_yForm,
      pushLetters_mem_rowHighest_iff τ hγ, implies_true, true_and]
    rw [← map_pushLetters_Ha τ c c' hγ]; rfl
  · exact pow_zsmul_mem_Ha τ h hP

end Lattice

end GlobalTheory.Harm
