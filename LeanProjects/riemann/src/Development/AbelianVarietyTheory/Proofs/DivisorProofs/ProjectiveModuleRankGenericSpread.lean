import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

namespace GlobalTheory.ArLieBase.MaxMinor

open Matrix Polynomial

theorem charpoly_of_sq_eq_smul : ∀ (K : Type) [Field K] (g r : ℕ) (D : K) (P : Matrix (Fin g) (Fin g) K),
    D ≠ 0 → P * P = D • P → P.rank = r →
      P.charpoly = Polynomial.X ^ (g - r) * (Polynomial.X - Polynomial.C D) ^ r := by
  intro K _ g r D P hD hP hr
  classical
  set f : Module.End K (Fin g → K) := Matrix.toLin' P with hf
  set E : Module.End K (Fin g → K) := D⁻¹ • f with hEdef
  have hfE : f = D • E := by rw [hEdef, smul_smul, mul_inv_cancel₀ hD, one_smul]
  have hff : f * f = D • f := by
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP, map_smul]
  have hE : IsIdempotentElem E := by
    show E * E = E
    rw [hEdef, smul_mul_assoc, mul_smul_comm, hff, smul_smul, smul_smul]
    congr 1
    field_simp
  have hrange : LinearMap.range E = LinearMap.range f := LinearMap.range_smul f _ (inv_ne_zero hD)
  have hc := LinearMap.IsIdempotentElem.isCompl hE
  have hrk1 : Module.finrank K (LinearMap.range E) = r := by
    rw [hrange, ← hr]; rfl
  have hrk0 : Module.finrank K (LinearMap.ker E) = g - r := by
    have := LinearMap.finrank_range_add_finrank_ker E
    rw [hrk1, Module.finrank_fin_fun] at this
    omega
  let b1 : Module.Basis (Fin r) K (LinearMap.range E) := Module.finBasisOfFinrankEq K _ hrk1
  let b0 : Module.Basis (Fin (g - r)) K (LinearMap.ker E) := Module.finBasisOfFinrankEq K _ hrk0
  let b : Module.Basis (Fin r ⊕ Fin (g - r)) K (Fin g → K) :=
    (b1.prod b0).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hb1 : ∀ a, b (Sum.inl a) = (b1 a : Fin g → K) := by
    intro a; simp [b]
  have hb0 : ∀ a, b (Sum.inr a) = (b0 a : Fin g → K) := by
    intro a; simp [b]
  have hfb : ∀ j, f (b j) = (Sum.elim (fun _ => D) (fun _ => (0 : K)) j) • b j := by
    rintro (a | a)
    · have h1 : E (b1 a) = b1 a := (LinearMap.IsIdempotentElem.mem_range_iff hE).1 (b1 a).2
      rw [hb1, hfE, LinearMap.smul_apply, h1]; rfl
    · have h0 : E (b0 a) = 0 := (b0 a).2
      rw [hb0, hfE, LinearMap.smul_apply, h0]; simp
  have hmat : LinearMap.toMatrix b b f = Matrix.diagonal (Sum.elim (fun _ => D) (fun _ => (0 : K))) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hfb, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Matrix.diagonal_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin' P, ← hf, ← LinearMap.charpoly_toMatrix f b, hmat, Matrix.charpoly_diagonal,
    Fintype.prod_sum_type]
  simp [Finset.prod_const, mul_comm]

theorem mul_mul_eq_smul_of_field : ∀ (K : Type) [Field K] (g r : ℕ) (D N : K) (P : Matrix (Fin g) (Fin g) K)
    (U : Matrix (Fin g) (Fin r) K) (Z : Matrix (Fin r) (Fin g) K), D ≠ 0 → N ≠ 0 → P * P = D • P → P.rank = r →
    P * U = D • U → Z * U = N • (1 : Matrix (Fin r) (Fin r) K) → U * Z * P = N • P := by
  intro K _ g r D N P U Z hD hN hP hr hPU hZU
  have hle : LinearMap.range U.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    refine ⟨D⁻¹ • (U *ᵥ y), ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hPU,
      Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hD, one_smul]
  have hrU : U.rank = r := by
    apply le_antisymm (Matrix.rank_le_width U)
    have h1 := Matrix.rank_mul_le_right Z U
    have hu : IsUnit (N • (1 : Matrix (Fin r) (Fin r) K)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (pow_ne_zero _ hN).isUnit
    rw [hZU, Matrix.rank_of_isUnit _ hu, Fintype.card_fin] at h1
    exact h1
  have heq : LinearMap.range U.mulVecLin = LinearMap.range P.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      show U.rank = P.rank
      rw [hrU, hr])
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨y, hy⟩ : P *ᵥ v ∈ LinearMap.range U.mulVecLin := heq ▸ ⟨v, rfl⟩
  rw [Matrix.mulVecLin_apply] at hy
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec, Matrix.mul_assoc U Z U, hZU, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mulVec, Matrix.smul_mulVec, hy]

theorem det_mul_eq_sum_rows {V : Type} [CommRing V] {m g : ℕ} (M : Matrix (Fin m) (Fin g) V)
    (C : Matrix (Fin g) (Fin m) V) :
    (M * C).det = ∑ J : Fin m → Fin g, (∏ i, M i (J i)) * (C.submatrix J id).det := by
  have h : M * C = Matrix.of fun i => ∑ k, M i k • C k := by
    ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  show Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ k, M i k • C k) = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem minor_mul_mem {R : Type} [CommRing R] {a b c r : ℕ} (C : Matrix (Fin a) (Fin b) R)
    (Y : Matrix (Fin b) (Fin c) R) (I : Fin r → Fin a) (K : Fin r → Fin c) :
    ((C * Y).submatrix I K).det ∈
      Ideal.span (Set.range fun p : (Fin r → Fin b) × (Fin r → Fin c) => (Y.submatrix p.1 p.2).det) := by
  have e : (C * Y).submatrix I K = C.submatrix I id * Y.submatrix id K := by
    ext i k; simp [Matrix.mul_apply]
  rw [e, det_mul_eq_sum_rows]
  exact Ideal.sum_mem _ fun f _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(f, K), rfl⟩)

theorem pow_mem_span_principal {R : Type} [CommRing R] [IsDomain R] {g r : ℕ} (D : R)
    (P : Matrix (Fin g) (Fin g) R) (hD : D ≠ 0) (hP : P * P = D • P)
    (hr : (P.map (algebraMap R (FractionRing R))).rank = r) :
    D ^ r ∈ Ideal.span (Set.range fun q : Fin r → Fin g => (P.submatrix q q).det) := by
  classical
  set F := FractionRing R
  have hinj := IsFractionRing.injective R F
  have hDF : algebraMap R F D ≠ 0 := (map_ne_zero_iff _ hinj).2 hD
  have hPF : P.map (algebraMap R F) * P.map (algebraMap R F) = algebraMap R F D • P.map (algebraMap R F) := by
    have := congrArg (RingHom.mapMatrix (algebraMap R F)) hP
    rw [map_mul] at this
    exact this.trans (by ext i j; simp)
  have hcF := charpoly_of_sq_eq_smul F g r _ _ hDF hPF hr
  have hc : P.charpoly = Polynomial.X ^ (g - r) * (Polynomial.X - Polynomial.C D) ^ r := by
    apply Polynomial.map_injective _ hinj
    rw [← Matrix.charpoly_map, hcF]
    simp
  have hrg : r ≤ g := hr ▸ Matrix.rank_le_width _
  have hcoef := Matrix.charpoly_coeff_eq_sum_minors P r (by simpa using hrg)
  rw [hc, Fintype.card_fin, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero] at hcoef
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub] at hcoef
  have hsum : D ^ r = ∑ s ∈ Finset.univ.powersetCard r,
      (P.submatrix (Subtype.val : s → Fin g) (Subtype.val : s → Fin g)).det := by
    have h1 : ((-1 : R) ^ r) * ((-1) ^ r) = 1 := by rw [← mul_pow]; simp
    calc D ^ r = ((-1) ^ r * (-1) ^ r) * D ^ r := by rw [h1, one_mul]
      _ = (-1) ^ r * (-D) ^ r := by rw [neg_pow D r]; ring
      _ = _ := by rw [hcoef, ← mul_assoc, h1, one_mul]
  rw [hsum]
  refine Ideal.sum_mem _ fun s hs => ?_
  have hcard : s.card = r := (Finset.mem_powersetCard.1 hs).2
  let e : Fin r ≃ s := (s.equivFinOfCardEq hcard).symm
  rw [← Matrix.det_submatrix_equiv_self e]
  exact Ideal.subset_span ⟨fun i => (e i).1, rfl⟩

end GlobalTheory.ArLieBase.MaxMinor

namespace GlobalTheory.ArLieBase.MaxMinor
theorem map_mul_rect {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a b c : Type} [Fintype b]
    (X : Matrix a b A) (Y : Matrix b c A) : (X * Y).map f = X.map f * Y.map f := Matrix.map_mul
end GlobalTheory.ArLieBase.MaxMinor

namespace GlobalTheory.ArLieBase.MaxMinor

open Matrix

theorem maxMinors_split : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (g M r D : ℕ) (P : Matrix (Fin g) (Fin g) R) (h : Fin M → Fin g → R), D ≠ 0 → P * P = (D : R) • P → (∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), (P.map ψ).rank = r) → (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) → ∃ (n m : ℕ) (A : Fin m → R), n ≠ 0 ∧ (n : R) ∈ (Ideal.span (Set.range A)).radical ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : R →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) → ∃ (N : ℕ) (U : Matrix (Fin g) (Fin r) R') (I : Fin r → Fin M), N ≠ 0 ∧ IsSplitting D (P.map ψ) (fun j i => ψ (h j i)) N U I := by
  intro R _ _ _ g M r D P h hD hP hrank ⟨n₀, hn₀, hspan⟩
  classical
  set H : Matrix (Fin M) (Fin g) R := Matrix.of h with hH
  have hc : ∀ i, ∃ c : Fin M → R, ∑ j, c j • h j = Pi.single i (n₀ : R) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (hspan i)
  choose c hc using hc
  set Cm : Matrix (Fin g) (Fin M) R := Matrix.of c with hCm
  have hCH : Cm * H = (n₀ : R) • (1 : Matrix (Fin g) (Fin g) R) := by
    ext i k
    have := congrFun (hc i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, hCm, hH, Matrix.of_apply, this, Matrix.smul_apply, Matrix.one_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  set Y : Matrix (Fin M) (Fin g) R := H * P with hY
  have hCY : Cm * Y = (n₀ : R) • P := by
    rw [hY, ← Matrix.mul_assoc, hCH, Matrix.smul_mul, Matrix.one_mul]
  let ι := (Fin r → Fin M) × (Fin r → Fin g)
  let A0 : ι → R := fun p => (Y.submatrix p.1 p.2).det
  let e := Fintype.equivFin ι
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have hrF := hrank (FractionRing R) (algebraMap R (FractionRing R))
  have hDR : (D : R) ≠ 0 := Nat.cast_ne_zero.2 hD
  have hprin := pow_mem_span_principal (D : R) P hDR hP hrF
  have hkey : ((n₀ : R) * D) ^ r ∈ Ideal.span (Set.range A0) := by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hprin
    rw [mul_pow, ← ha, Finset.mul_sum]
    refine Ideal.sum_mem _ fun q _ => ?_
    have : (n₀ : R) ^ r * (a q • (P.submatrix q q).det) = a q * ((Cm * Y).submatrix q q).det := by
      rw [hCY, show ((n₀ : R) • P).submatrix q q = (n₀ : R) • P.submatrix q q from rfl, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (minor_mul_mem Cm Y q q)
  refine ⟨n₀ * D, Fintype.card ι, A0 ∘ e.symm, Nat.mul_ne_zero hn₀ hD, ?_, ?_⟩
  · have hrange : Set.range (A0 ∘ e.symm) = Set.range A0 := e.symm.surjective.range_comp _
    rw [hrange]
    exact ⟨r, by push_cast; exact hkey⟩
  intro R' _ _ _ ψ ⟨k, hk⟩
  rcases hpk : e.symm k with ⟨I, K⟩

  set P' : Matrix (Fin g) (Fin g) R' := P.map ψ with hP'def
  set Hψ : Matrix (Fin M) (Fin g) R' := H.map ψ with hHψ
  have hY' : Y.map ψ = Hψ * P' := by
    rw [hY, hHψ, hP'def]; exact Matrix.map_mul
  have hP' : P' * P' = (D : R') • P' := by
    have := congrArg (RingHom.mapMatrix ψ) hP
    rw [map_mul] at this
    exact this.trans (by ext i j; simp [hP'def])
  set B : Matrix (Fin r) (Fin r) R' := (Hψ * P').submatrix I K with hB
  have hψA : ∀ q : ι, ψ (A0 q) = ((Hψ * P').submatrix q.1 q.2).det := by
    intro q
    rw [RingHom.map_det, ← hY']
    rfl
  have hdiv : ∀ q : ι, B.det ∣ ((Hψ * P').submatrix q.1 q.2).det := by
    intro q
    have := hk (e q)
    simp only [Function.comp_apply, Equiv.symm_apply_apply, hpk] at this
    rw [hψA, hψA] at this
    exact this
  set N : ℕ := (n₀ * D) ^ r with hNdef
  have hN0 : N ≠ 0 := pow_ne_zero _ (Nat.mul_ne_zero hn₀ hD)
  have hNdvd : B.det ∣ (N : R') := by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hkey
    have : (N : R') = ψ (((n₀ : R) * D) ^ r) := by simp [hNdef]
    rw [this, ← ha, map_sum]
    exact Finset.dvd_sum fun q _ => by
      rw [smul_eq_mul, map_mul, hψA]
      exact Dvd.dvd.mul_left (hdiv q) _
  obtain ⟨cc, hcc⟩ := hNdvd
  let ιK : Matrix (Fin g) (Fin r) R' := Matrix.of fun a i => if a = K i then 1 else 0
  have hιK : ∀ {m : Type} [Fintype m] (X : Matrix m (Fin g) R'), X * ιK = X.submatrix id K := by
    intro m _ X
    ext i a
    simp [Matrix.mul_apply, ιK]
  have hhI : (Matrix.of fun i => (fun j i => ψ (h j i)) (I i)) = Hψ.submatrix I id := by
    ext i a; simp [hHψ, hH]
  have hIP : Hψ.submatrix I id * P' * ιK = B := by
    rw [hιK, hB]
    ext i a; simp [Matrix.mul_apply]
  set U : Matrix (Fin g) (Fin r) R' := P' * (ιK * (cc • B.adjugate)) with hU
  have hIU : Hψ.submatrix I id * U = (N : R') • (1 : Matrix (Fin r) (Fin r) R') := by
    rw [hU, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hIP, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
      mul_comm, ← hcc]
  have hPU : P' * U = (D : R') • U := by
    rw [hU, ← Matrix.mul_assoc, hP', Matrix.smul_mul]

  have hUIP : U * Hψ.submatrix I id * P' = (N : R') • P' := by
    have hinj := IsFractionRing.injective R' (FractionRing R')
    haveI : CharZero (FractionRing R') := charZero_of_injective_algebraMap hinj
    set φ := algebraMap R' (FractionRing R') with hφ
    have hrk : (P'.map φ).rank = r := by
      rw [hP'def, Matrix.map_map, ← RingHom.coe_comp]
      exact hrank _ (φ.comp ψ)
    have h1 : P'.map φ * P'.map φ = (D : FractionRing R') • P'.map φ := by
      rw [← map_mul_rect φ, hP']; ext i j; simp
    have h2 : P'.map φ * U.map φ = (D : FractionRing R') • U.map φ := by
      rw [← map_mul_rect φ, hPU]; ext i j; simp
    have h3 : (Hψ.submatrix I id).map φ * U.map φ = (N : FractionRing R') • (1 : Matrix (Fin r) (Fin r) _) := by
      rw [← map_mul_rect φ, hIU]; ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := mul_mul_eq_smul_of_field (FractionRing R') g r (D : FractionRing R') (N : FractionRing R') (P'.map φ)
      (U.map φ) ((Hψ.submatrix I id).map φ) (Nat.cast_ne_zero.2 hD) (Nat.cast_ne_zero.2 hN0) h1 hrk h2 h3
    apply Matrix.map_injective hinj
    show (U * Hψ.submatrix I id * P').map φ = ((N : R') • P').map φ
    rw [map_mul_rect φ, map_mul_rect φ, this]; ext i j; simp
  refine ⟨N, U, I, hN0, hPU, hhI ▸ hIU, hhI ▸ hUIP, ?_⟩
  intro j
  let yj : Fin r → R' := fun a => (Hψ * P') j (K a)
  have hupd : ∀ i, B.updateRow i yj = (Hψ * P').submatrix (Function.update I i j) K := by
    intro i
    ext i' a
    by_cases h' : i' = i
    · subst h'; simp [Matrix.updateRow_apply, yj]
    · simp [Matrix.updateRow_apply, h', hB]
  have hdi : ∀ i, ∃ a, (B.updateRow i yj).det = B.det * a := fun i => by
    rw [hupd]; exact hdiv (Function.update I i j, K)
  choose a ha using hdi
  refine ⟨a, ?_⟩
  have hadj : Matrix.vecMul yj B.adjugate = fun i => (B.updateRow i yj).det := by
    funext i
    rw [← Matrix.mulVec_transpose, Matrix.adjugate_transpose, ← Matrix.cramer_eq_adjugate_mulVec,
      Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
  have hrow : ∀ j', Matrix.vecMul (fun i => ψ (h j' i)) P' = (Hψ * P') j' := by
    intro j'
    ext k; simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, hHψ, hH]

  have hyK : ∀ x : Fin g → R', Matrix.vecMul x ιK = fun a => x (K a) := by
    intro x; ext a; simp [Matrix.vecMul, dotProduct, ιK]
  have hvU : Matrix.vecMul (fun i => ψ (h j i)) U = fun i => cc * (B.updateRow i yj).det := by
    rw [hU, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hrow, hyK, Matrix.vecMul_smul]
    change cc • Matrix.vecMul yj B.adjugate = _
    rw [hadj]; rfl
  have key := congrArg (Matrix.vecMul (fun i => ψ (h j i))) hUIP
  rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, hvU, Matrix.vecMul_eq_sum, Matrix.vecMul_smul] at key
  apply smul_right_injective (Fin g → R') (Nat.cast_ne_zero.2 hN0 : (N : R') ≠ 0)
  change (N : R') • Matrix.vecMul (fun i => ψ (h j i)) P' = (N : R') • ∑ i, a i • Matrix.vecMul (fun a => ψ (h (I i) a)) P'
  rw [← key, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (Hψ.submatrix I id * P') i = Matrix.vecMul (fun a => ψ (h (I i) a)) P' := by
    rw [hrow]; rfl
  rw [hr, ha i, smul_smul, hcc]
  congr 1
  ring

end GlobalTheory.ArLieBase.MaxMinor
