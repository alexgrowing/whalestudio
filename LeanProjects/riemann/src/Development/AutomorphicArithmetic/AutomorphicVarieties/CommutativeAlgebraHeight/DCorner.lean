import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section aux

variable {A E : Type} [CommRing A] [Ring E] [Algebra A E]

private lemma map_smul_c {B B' : Type} [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B')
    (c : B) (w : B ⊗[A] E) :
    Algebra.TensorProduct.map φ (AlgHom.id A E) (c • w) = φ c • Algebra.TensorProduct.map φ (AlgHom.id A E) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

private lemma map_map_c {B B' B'' : Type} [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B']
    [CommRing B''] [Algebra A B''] (φ : B →ₐ[A] B') (ψ : B' →ₐ[A] B'') (χ : B →ₐ[A] B'') (h : ∀ b, ψ (φ b) = χ b)
    (w : B ⊗[A] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id A E) (Algebra.TensorProduct.map φ (AlgHom.id A E) w) =
      Algebra.TensorProduct.map χ (AlgHom.id A E) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h]
  | add a b ha hb => simp only [map_add, ha, hb]

private lemma add_of_homog (f : ∀ (B : Type) [CommRing B] [Algebra A B], B ⊗[A] E → B)
    (nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') (x : B ⊗[A] E),
      f B' (Algebra.TensorProduct.map φ (AlgHom.id A E) x) = φ (f B x))
    (hom : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E), f B (b • x) = b * f B x)
    (B : Type) [CommRing B] [Algebra A B] (x y : B ⊗[A] E) : f B (x + y) = f B x + f B y := by
  let i2 : B →ₐ[A] TrivSqZeroExt B (B × B) := IsScalarTower.toAlgHom A B _
  let i1 : B →ₐ[A] TrivSqZeroExt B B := IsScalarTower.toAlgHom A B _
  let z : TrivSqZeroExt B (B × B) ⊗[A] E :=
    (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt B (B × B)) • Algebra.TensorProduct.map i2 (AlgHom.id A E) x +
    (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt B (B × B)) • Algebra.TensorProduct.map i2 (AlgHom.id A E) y
  have key : ∀ (g : (B × B) →ₗ[B] B), g (f _ z).snd = (f _
      ((TrivSqZeroExt.inr (g (1, 0)) : TrivSqZeroExt B B) • Algebra.TensorProduct.map i1 (AlgHom.id A E) x +
       (TrivSqZeroExt.inr (g (0, 1)) : TrivSqZeroExt B B) • Algebra.TensorProduct.map i1 (AlgHom.id A E) y)).snd := by
    intro g
    have h := nat _ _ ((TrivSqZeroExt.map g).restrictScalars A) z
    have hc : ∀ b, ((TrivSqZeroExt.map g).restrictScalars A) (i2 b) = i1 b := fun b =>
      (TrivSqZeroExt.map g).commutes b
    simp only [z, map_add, map_smul_c, map_map_c i2 _ i1 hc] at h
    have h2 := congrArg TrivSqZeroExt.snd h
    simp only [AlgHom.restrictScalars_apply, TrivSqZeroExt.map_inr, TrivSqZeroExt.snd_map] at h2
    exact h2.symm
  have ev : ∀ w : B ⊗[A] E, (f _ ((TrivSqZeroExt.inr 1 : TrivSqZeroExt B B) •
      Algebra.TensorProduct.map i1 (AlgHom.id A E) w)).snd = f B w := by
    intro w
    rw [hom, nat]
    simp [i1, TrivSqZeroExt.algebraMap_eq_inl]
  have k1 := key (LinearMap.fst B B B)
  have k2 := key (LinearMap.snd B B B)
  have k3 := key (LinearMap.fst B B B + LinearMap.snd B B B)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, TrivSqZeroExt.inr_zero, zero_smul,
    add_zero, zero_add, ← smul_add, ← map_add, ev] at k1 k2 k3
  rw [← k1, ← k2, ← k3]

end aux

section aux2

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)

private noncomputable def cornerF (B : Type) [CommRing B] [Algebra A B] (z : B ⊗[A] E) : B :=
  D.D B (1 - (1 : B) ⊗ₜ[A] e + (1 : B) ⊗ₜ[A] e * z * (1 : B) ⊗ₜ[A] e)

private lemma cornerF_nat (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    cornerF D e B' (Algebra.TensorProduct.map φ (AlgHom.id A E) x) = φ (cornerF D e B x) := by
  unfold cornerF
  rw [← D.nat]
  simp

variable {D e}

private lemma one_add_e (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + b ⊗ₜ e) = 1 + b := by
  have := D.nat A[X] B (aeval b) (1 + X ⊗ₜ e)
  rw [h1] at this
  simpa using this

private lemma ee (he : IsIdempotentElem e) (B : Type) [CommRing B] [Algebra A B] :
    ((1 : B) ⊗ₜ[A] e) * ((1 : B) ⊗ₜ[A] e) = (1 : B) ⊗ₜ[A] e := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul]

private lemma tmul_eq (B : Type) [CommRing B] [Algebra A B] (b : B) (x : E) :
    b ⊗ₜ[A] x = b • ((1 : B) ⊗ₜ[A] x) := by
  simp [smul_tmul']

private lemma cornerF_hom (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E) :
    cornerF D e B (b • x) = b * cornerF D e B x := by
  unfold cornerF
  have h := one_add_e h1 B (b - 1)
  rw [add_sub_cancel] at h
  conv_rhs => rw [← h, ← map_mul]
  congr 1
  rw [tmul_eq B (b - 1)]
  have h2 := ee (A := A) he B
  generalize ((1 : B) ⊗ₜ[A] e) = ε at h2 ⊢
  simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, ← mul_assoc, h2, sub_smul,
    one_smul, sub_mul]
  abel

private lemma cornerF_add (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (x y : B ⊗[A] E) :
    cornerF D e B (x + y) = cornerF D e B x + cornerF D e B y :=
  add_of_homog (cornerF D e) (cornerF_nat D e) (cornerF_hom he h1) B x y

private lemma cornerF_e (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (b : B) : cornerF D e B (b ⊗ₜ e) = b := by
  rw [tmul_eq, cornerF_hom he h1, cornerF, ee he, ee he, sub_add_cancel, map_one, mul_one]

private lemma cornerF_tmul (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X)
    (B : Type) [CommRing B] [Algebra A B] (b : B) (u : E) :
    cornerF D e B (b ⊗ₜ u) = b * algebraMap A B (cornerF D e A (1 ⊗ₜ u)) := by
  rw [tmul_eq, cornerF_hom he h1]
  congr 1
  have := cornerF_nat D e A B (Algebra.ofId A B) (1 ⊗ₜ u)
  simpa [Algebra.ofId_apply] using this

private lemma cornerF_tr (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (u : E) (hu : e * u * e = u) : D.tr u = cornerF D e A (1 ⊗ₜ u) := by
  have h : D.D A[X] (1 + X ⊗ₜ u) = cornerF D e A[X] (1 ⊗ₜ e + X ⊗ₜ u) := by
    unfold cornerF
    congr 1
    simp [mul_add, add_mul, he.eq, hu, ← add_assoc]
  rw [cornerF_add he h1, cornerF_e he h1, cornerF_tmul he h1, (d_chi D u).2.2.1] at h
  have h2 := congrArg (fun p => p.coeff 1) h
  simp only [finset_sum_coeff, coeff_C_mul_X_pow] at h2
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (by omega))] at h2
  simpa [Det.tr, coeff_one] using h2

private lemma compl_e (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (S : Type) [CommRing S] [Algebra A S] :
    D.D S[X] (X ⊗ₜ 1 - X ⊗ₜ e + 1 ⊗ₜ e) = X ^ (n - 1) := by
  have h := one_add_e h1 S[X] (X - 1)
  rw [add_sub_cancel] at h
  have h2 : D.D S[X] (X ⊗ₜ 1 - X ⊗ₜ e + 1 ⊗ₜ e) * X = X ^ (n - 1) * X := by
    conv_lhs => enter [2]; rw [← h]
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel hn]
    have := D.homog S[X] X 1
    rw [map_one, mul_one] at this
    rw [← this]
    congr 1
    simp only [mul_add, add_mul, sub_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul, mul_sub,
      sub_tmul, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul]
    abel
  exact (Polynomial.isRegular_X.right) h2

private lemma chiS_corner (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (S : Type) [CommRing S] [Algebra A S] (s : S) (u : E) (hu : e * u * e = u) :
    D.chiS S (1 ⊗ₜ e + s ⊗ₜ u) = X ^ (n - 1) * (X - C (1 + s * algebraMap A S (D.tr u))) := by
  have hl : e * u = u := by rw [← hu, ← mul_assoc, ← mul_assoc, he.eq]
  have hr : u * e = u := by rw [← hu, mul_assoc, he.eq]
  have h : cornerF D e S[X] ((X - 1) ⊗ₜ e + (- C s) ⊗ₜ u) = X - C (1 + s * algebraMap A S (D.tr u)) := by
    rw [cornerF_add he h1, cornerF_e he h1, cornerF_tmul he h1, ← cornerF_tr he h1 hn u hu]
    simp [Polynomial.algebraMap_apply]
    ring
  rw [← h, ← compl_e he h1 hn, cornerF, ← map_mul, Det.chiS]
  congr 1
  simp only [mul_add, add_mul, sub_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul, mul_sub,
      sub_tmul, Algebra.TensorProduct.one_def, hr, hl, map_add, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.id_apply, IsScalarTower.toAlgHom_apply, Polynomial.algebraMap_eq, neg_tmul, mul_neg, neg_mul]
  abel

private lemma corner_eq (hD : D.IsCH) (he : IsIdempotentElem e) (h1 : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (hn : 1 ≤ n)
    (u : E) (hu : e * u * e = u) : u = D.tr u • e := by
  have hl : e * u = u := by rw [← hu, ← mul_assoc, ← mul_assoc, he.eq]
  have hr : u * e = u := by rw [← hu, mul_assoc, he.eq]
  let s : TrivSqZeroExt A A := TrivSqZeroExt.inr 1
  have hs : s * s = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
  have h := (d_chS D (TrivSqZeroExt A A)).1 (1 ⊗ₜ e + s ⊗ₜ u)
  rw [chiS_corner he h1 hn _ s u hu, show D.CH = ⊥ from hD] at h
  have h0 := (Submodule.span_le (p := ⊥)).2 (by
    rintro _ ⟨z, hz, rfl⟩
    have : z = 0 := by simpa using hz
    simp [this]) h
  rw [Submodule.mem_bot, map_mul, map_pow, map_sub, aeval_X, aeval_C] at h0
  have h2 : ((1 ⊗ₜ e + s ⊗ₜ u : TrivSqZeroExt A A ⊗[A] E) - algebraMap (TrivSqZeroExt A A) _
      (1 + s * algebraMap A _ (D.tr u))) * (1 ⊗ₜ e) = s ⊗ₜ (u - D.tr u • e) := by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sub_mul, add_mul,
      Algebra.TensorProduct.tmul_mul_tmul, he.eq, hr, mul_one, one_mul, add_tmul, tmul_sub]
    rw [← smul_tmul, Algebra.smul_def, mul_comm s]
    abel
  have h3 : ∀ k : ℕ, (1 ⊗ₜ e + s ⊗ₜ u : TrivSqZeroExt A A ⊗[A] E) ^ k * (s ⊗ₜ (u - D.tr u • e)) =
      s ⊗ₜ (u - D.tr u • e) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, hs, zero_tmul, add_zero, one_mul, mul_sub, hl, mul_smul_comm, he.eq]
  have h4 := congrArg (· * ((1 : TrivSqZeroExt A A) ⊗ₜ[A] e)) h0
  simp only [mul_assoc, h2, h3, zero_mul] at h4
  have h5 := congrArg (fun w => TensorProduct.lid A E ((TrivSqZeroExt.sndHom A A).rTensor E w)) h4
  simpa [s, sub_eq_zero] using h5

end aux2

theorem UpperTheory.V.CA.d_corner :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E), D.IsCH → IsIdempotentElem e → D.D A[X] (1 + X ⊗ₜ e) = 1 + X → 1 ≤ n → (∀ x, e * x * e = D.tr (e * x) • e) ∧ D.tr e = 1 ∧ (∀ a : A, a • e = 0 → a = 0) ∧ ∀ a : A, D.D A[X] (1 + X ⊗ₜ (a • e)) = 1 + C a * X := by
  intro n A E _ _ _ D e hD he h1 hn
  have h4 : ∀ a : A, D.D A[X] (1 + X ⊗ₜ (a • e)) = 1 + C a * X := by
    intro a
    rw [← smul_tmul, one_add_e h1, Polynomial.smul_eq_C_mul]
  refine ⟨fun x => ?_, ?_, fun a ha => ?_, h4⟩
  · have h := corner_eq hD he h1 hn (e * x * e) (by
      rw [← mul_assoc, ← mul_assoc, he.eq, mul_assoc _ e e, he.eq])
    have h2 : D.tr (e * x * e) = D.tr (e * x) := by
      rw [Det.tr, (d_tr D).2.1 1 (e * x) e, ← mul_assoc, he.eq, Det.tr]
    rw [← h2]; exact h
  · rw [cornerF_tr he h1 hn e (by rw [he.eq, he.eq]), cornerF_e he h1]
  · have h := h4 a
    rw [ha, tmul_zero, add_zero, map_one] at h
    have h2 := congrArg (fun p => p.coeff 1) h
    simpa [coeff_one] using h2.symm
