import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem matUnits_pair {A E k : Type} [CommRing A] [Ring E] [Algebra A E] [Field k] [Algebra A k] [IsLocalHom (algebraMap A k)] {n : ℕ} (π : E →ₐ[A] Matrix (Fin n) (Fin n) k) (e : Fin n → E)
    (hs : Function.Surjective π) (hid : ∀ i, e i * e i = e i)
    (hπ : ∀ i, π (e i) = Matrix.single i i 1) (hc : ∀ i x, ∃ a : A, e i * x * e i = a • e i)
    (hf : ∀ i (a : A), a • e i = 0 → a = 0) (o j : Fin n) :
    ∃ P Q : E, e o * P = P ∧ P * e j = P ∧ e j * Q = Q ∧ Q * e o = Q ∧ P * Q = e o ∧ Q * P = e j ∧
      π P = Matrix.single o j 1 ∧ π Q = Matrix.single j o 1 := by
  obtain ⟨p, hp⟩ := hs (Matrix.single o j 1)
  obtain ⟨q, hq⟩ := hs (Matrix.single j o 1)
  obtain ⟨P, hP⟩ : ∃ P, P = e o * p * e j := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = e j * q * e o := ⟨_, rfl⟩
  have h1 : e o * P = P := by rw [hP, ← mul_assoc, ← mul_assoc, hid]
  have h2 : P * e j = P := by rw [hP, mul_assoc _ (e j), hid]
  have h3 : e j * Q = Q := by rw [hQ, ← mul_assoc, ← mul_assoc, hid]
  have h4 : Q * e o = Q := by rw [hQ, mul_assoc _ (e o), hid]
  have hπP : π P = Matrix.single o j 1 := by
    rw [hP, map_mul, map_mul, hπ, hπ, hp, Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp
  have hπQ : π Q = Matrix.single j o 1 := by
    rw [hQ, map_mul, map_mul, hπ, hπ, hq, Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp
  obtain ⟨c, hc1⟩ := hc j (Q * P)
  obtain ⟨d, hd1⟩ := hc o (P * Q)
  have hc2 : Q * P = c • e j := by
    rw [← hc1, ← mul_assoc, h3, mul_assoc, h2]
  have hd2 : P * Q = d • e o := by
    rw [← hd1, ← mul_assoc, h1, mul_assoc, h4]
  have hone : ∀ (i : Fin n) (a : A) (x : E), π x = Matrix.single i i 1 → x = a • e i → algebraMap A k a = 1 := by
    intro i a x hx hxa
    rw [hxa, map_smul, hπ] at hx
    have := congrFun (congrFun hx i) i
    simpa [Algebra.smul_def] using this
  have hck : algebraMap A k c = 1 := hone j c _ (by
    rw [map_mul, hπP, hπQ, Matrix.single_mul_single_same, mul_one]) hc2
  have hdk : algebraMap A k d = 1 := hone o d _ (by
    rw [map_mul, hπP, hπQ, Matrix.single_mul_single_same, mul_one]) hd2
  have hcu : IsUnit c := (isUnit_map_iff (algebraMap A k) c).1 (hck ▸ isUnit_one)
  have hdu : IsUnit d := (isUnit_map_iff (algebraMap A k) d).1 (hdk ▸ isUnit_one)
  have hcd : c = d := by
    have a1 : P * Q * (P * Q) = (d * d) • e o := by
      rw [hd2, smul_mul_smul_comm, hid]
    have a2 : P * Q * (P * Q) = (c * d) • e o := by
      rw [mul_assoc, ← mul_assoc Q, hc2, smul_mul_assoc, h3, mul_smul_comm, hd2, smul_smul]
    have a3 : (c * d - d * d) • e o = 0 := by rw [sub_smul, ← a1, ← a2, sub_self]
    exact hdu.mul_right_cancel (sub_eq_zero.1 (hf o _ a3))
  obtain ⟨b, hb⟩ := hcu.exists_left_inv
  have hbk : algebraMap A k b = 1 := by
    have := congrArg (algebraMap A k) hb
    rwa [map_mul, hck, mul_one, map_one] at this
  refine ⟨P, b • Q, h1, h2, ?_, ?_, ?_, ?_, hπP, ?_⟩
  · rw [mul_smul_comm, h3]
  · rw [smul_mul_assoc, h4]
  · rw [mul_smul_comm, hd2, smul_smul, ← hcd, hb, one_smul]
  · rw [smul_mul_assoc, hc2, smul_smul, hb, one_smul]
  · rw [map_smul, hπQ, ← algebraMap_smul k b, hbk, one_smul]

theorem UpperTheory.V.Ws.Eb.matUnits :
    ∀ {A E k : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] [Field k] [Algebra A k] [IsLocalHom (algebraMap A k)] {n : ℕ} (π : E →ₐ[A] Matrix (Fin n) (Fin n) k) (e : Fin n → E), Function.Surjective π → CompleteOrthogonalIdempotents e → (∀ i, π (e i) = Matrix.single i i 1) → (∀ i x, ∃ a : A, e i * x * e i = a • e i) → (∀ i (a : A), a • e i = 0 → a = 0) →
        ∃ φ : E →ₐ[A] Matrix (Fin n) (Fin n) A, (∀ i, φ (e i) = Matrix.single i i 1) ∧ ∀ x, (φ x).map (algebraMap A k) = π x := by
  intro A E k _ _ _ _ _ _ _ n π e hs he hπ hc hf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  let o : Fin n := ⟨0, hn⟩
  have hid : ∀ i, e i * e i = e i := fun i => (he.idem i).eq
  choose P Q h1 h2 h3 h4 h5 h6 hP hQ using matUnits_pair π e hs hid hπ hc hf o
  choose c hcc using hc o
  have inj : ∀ a b : A, a • e o = b • e o → a = b := fun a b h =>
    sub_eq_zero.1 (hf o _ (by rw [sub_smul, h, sub_self]))
  obtain ⟨m, hm⟩ : ∃ m : E → Matrix (Fin n) (Fin n) A, ∀ x i j, m x i j • e o = P i * x * Q j := by
    refine ⟨fun x => Matrix.of fun i j => c (P i * x * Q j), fun x i j => ?_⟩
    change c (P i * x * Q j) • e o = _
    rw [← hcc, ← mul_assoc, ← mul_assoc, h1, mul_assoc _ (Q j), h4]
  have hPQ : ∀ i j, P i * Q j = (1 : Matrix (Fin n) (Fin n) A) i j • e o := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [h5, Matrix.one_apply_eq, one_smul]
    · rw [Matrix.one_apply_ne hij, zero_smul, ← h2 i, ← h3 j, mul_assoc, ← mul_assoc (e i),
        he.ortho hij, zero_mul, mul_zero]
  have m1 : m 1 = 1 := by
    ext i j
    apply inj
    rw [hm, mul_one, hPQ]
  have mmul : ∀ x y, m (x * y) = m x * m y := by
    intro x y
    ext i j
    apply inj
    rw [hm, Matrix.mul_apply, Finset.sum_smul]
    have : ∀ l, (m x i l * m y l j) • e o = P i * x * e l * (y * Q j) := by
      intro l
      rw [← hid o, ← smul_mul_smul_comm, hm, hm, ← h6 l]
      simp only [mul_assoc]
    simp only [this]
    rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete]
    simp only [mul_assoc, one_mul]
  have madd : ∀ x y, m (x + y) = m x + m y := by
    intro x y
    ext i j
    apply inj
    rw [Matrix.add_apply, add_smul, hm, hm, hm, mul_add, add_mul]
  have msmul : ∀ (a : A) x, m (a • x) = a • m x := by
    intro a x
    ext i j
    apply inj
    rw [Matrix.smul_apply, smul_eq_mul, mul_smul, hm, hm, mul_smul_comm, smul_mul_assoc]
  let L : E →ₗ[A] Matrix (Fin n) (Fin n) A := ⟨⟨m, madd⟩, msmul⟩
  refine ⟨AlgHom.ofLinearMap L m1 mmul, fun l => ?_, fun x => ?_⟩
  · change m (e l) = _
    ext i j
    apply inj
    rw [hm]
    by_cases hi : l = i
    · subst hi
      rw [h2, hPQ]
      congr 1
      simp [Matrix.one_apply, Matrix.single_apply]
    · rw [← h2 i, mul_assoc _ (e i), he.ortho (Ne.symm hi), mul_zero, zero_mul,
        Matrix.single_apply_of_row_ne hi, zero_smul]
  · change (m x).map _ = _
    ext i j
    have h := congrArg π (hm x i j)
    rw [map_smul, map_mul, map_mul, hπ, hP, hQ, Matrix.single_mul_mul_single] at h
    have := congrFun (congrFun h o) o
    simpa [Algebra.smul_def] using this
