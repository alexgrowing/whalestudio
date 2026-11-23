import Mathlib
open TensorProduct

universe u₁ u₂ u₃ u₄ u₅ u₆

private lemma loc_ker {W A C L : Type*} [CommRing W] [CommRing A] [CommRing C] [Algebra W A]
    [Algebra A C] [Algebra W C] [IsScalarTower W A C] [AddCommGroup L] [Module W L] (t : A)
    [IsLocalization (Submonoid.powers t) C] (x : A ⊗[W] L)
    (hx : LinearMap.rTensor L (IsScalarTower.toAlgHom W A C).toLinearMap x = 0) :
    ∃ b : ℕ, t ^ b • x = 0 := by
  have hbc := TensorProduct.isBaseChange A (A ⊗[W] L) C
  have hl := (isLocalizedModule_iff_isBaseChange (Submonoid.powers t) C _).2 hbc
  have key : ∀ p : A ⊗[W] L, AlgebraTensorModule.cancelBaseChange W A C C L
      ((TensorProduct.mk A C (A ⊗[W] L) 1) p) =
      LinearMap.rTensor L (IsScalarTower.toAlgHom W A C).toLinearMap p := by
    intro p
    induction p with
    | zero => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul a y => simp [Algebra.algebraMap_eq_smul_one]
  have h0 : (TensorProduct.mk A C (A ⊗[W] L) 1) x = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange W A C C L).injective
    rw [map_zero, key, hx]
  obtain ⟨⟨_, b, rfl⟩, hb⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers t) _).1 h0
  exact ⟨b, hb⟩

private lemma coords (W : Type u₁) (K : Type u₂) (C : Type u₃) (L : Type u₄) [CommRing W] [Field K]
    [Algebra W K] [CommRing C] [Algebra W C] [Algebra K C] [IsScalarTower W K C] [AddCommGroup L]
    [Module W L] :
    ∃ (I : Type (max u₂ u₄)) (b : Module.Basis I K (K ⊗[W] L)) (e : C ⊗[W] L ≃ₗ[C] (I →₀ C)),
      ∀ (x : C) (y : L), e (x ⊗ₜ y) =
        x • Finsupp.mapRange (algebraMap K C) (map_zero _) (b.repr (1 ⊗ₜ y)) := by
  let b := Module.Basis.ofVectorSpace K (K ⊗[W] L)
  refine ⟨_, b, (AlgebraTensorModule.cancelBaseChange W K C C L).symm.trans
    (Algebra.TensorProduct.basis C b).repr, ?_⟩
  intro x y
  simp [Algebra.TensorProduct.basis_repr_tmul]

private lemma aux {W : Type u₁} {K : Type u₂} {A : Type u₅} {C : Type u₃} {Γ : Type u₆} {L : Type u₄}
    (l : ℕ) [CommRing W] [IsDomain W] [Field K] [Algebra W K] [IsFractionRing W K]
    [CommRing A] [Algebra W A] [CommRing C] [Algebra A C] [Algebra W C] [IsScalarTower W A C]
    [Algebra K C] [IsScalarTower W K C] [AddCommGroup L] [Module W L] (t : A)
    [IsLocalization (Submonoid.powers t) C]
    (σA : Γ → A →+* A) (σC : Γ → C →+* C) (χ : Γ → A) (T : Γ → (A ⊗[W] L →+ A ⊗[W] L))
    (z : A ⊗[W] L) (s : ℕ)
    (hW : ∀ y : W, y ≠ 0 → ∃ (m : ℕ) (b : W), y = (l : W) ^ m * b ∧ IsUnit b)
    (hl : IsUnit (l : C))
    (hσ : ∀ g a, σC g (algebraMap A C a) = algebraMap A C (σA g a))
    (hσW : ∀ g (w : W), σA g (algebraMap W A w) = algebraMap W A w)
    (hσt : ∀ g, σA g t = χ g * t)
    (hT : ∀ g (a : A) (y : L), T g (a ⊗ₜ[W] y) = σA g a ⊗ₜ[W] y)
    (hfix : ∀ x : C, (∀ g, σC g x = x) → ∃ (a : ℕ) (w : W), (l : C) ^ a * x = algebraMap W C w)
    (hz : ∀ g, ∃ a b : ℕ, ((l : A) ^ a * t ^ b) • T g z = ((l : A) ^ a * t ^ b * χ g ^ s) • z) :
    ∃ (a b : ℕ) (y : L), ((l : A) ^ a * t ^ b) • z = (t ^ (b + s)) • ((1 : A) ⊗ₜ[W] y) := by
  classical
  obtain ⟨I, b, e, he⟩ := coords W K C L
  obtain ⟨R, hR⟩ : ∃ R : A ⊗[W] L →ₗ[W] C ⊗[W] L,
      R = LinearMap.rTensor L (IsScalarTower.toAlgHom W A C).toLinearMap := ⟨_, rfl⟩
  have hRt : ∀ (a : A) (y : L), R (a ⊗ₜ y) = algebraMap A C a ⊗ₜ y := fun a y => by simp [hR]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : A ⊗[W] L → (I →₀ C), ∀ x, Φ x = e (R x) := ⟨_, fun _ => rfl⟩
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hΦadd : ∀ p q, Φ (p + q) = Φ p + Φ q := fun p q => by simp [hΦ]
  have hΦsub : ∀ p q, Φ (p - q) = Φ p - Φ q := fun p q => by simp [hΦ]
  have hΦt : ∀ a y i, Φ (a ⊗ₜ y) i = algebraMap A C a * algebraMap K C (b.repr (1 ⊗ₜ y) i) := by
    intro a y i
    rw [hΦ, hRt, he, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  have hΦs : ∀ (a : A) x i, Φ (a • x) i = algebraMap A C a * Φ x i := by
    intro a x i
    induction x with
    | zero => simp [hΦ0]
    | add p q hp hq =>
      rw [smul_add, hΦadd, hΦadd, Finsupp.add_apply, Finsupp.add_apply, hp, hq, mul_add]
    | tmul a' y => rw [TensorProduct.smul_tmul', hΦt, hΦt, smul_eq_mul, map_mul, mul_assoc]
  have hσK : ∀ g (k : K), σC g (algebraMap K C k) = algebraMap K C k := by
    intro g k
    have h : (σC g).comp (algebraMap K C) = algebraMap K C := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors W)
      ext w
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply W K C, IsScalarTower.algebraMap_apply W A C, hσ, hσW]
    exact RingHom.congr_fun h k
  have hΦT : ∀ g x i, Φ (T g x) i = σC g (Φ x i) := by
    intro g x i
    induction x with
    | zero => simp [hΦ0]
    | add p q hp hq =>
      rw [map_add, hΦadd, hΦadd, Finsupp.add_apply, Finsupp.add_apply, hp, hq, map_add]
    | tmul a y => rw [hT, hΦt, hΦt, map_mul, hσ, hσK]
  have hct : IsUnit (algebraMap A C t) :=
    IsLocalization.map_units C (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)
  obtain ⟨u, hu⟩ : ∃ u : C, algebraMap A C t ^ s * u = 1 := (hct.pow s).exists_right_inv
  have hy : ∀ i g, σC g (u * Φ z i) = u * Φ z i := by
    intro i g
    obtain ⟨a, b', h⟩ := hz g
    have h1 : Φ (((l : A) ^ a * t ^ b') • T g z) i = Φ (((l : A) ^ a * t ^ b' * χ g ^ s) • z) i := by
      rw [h]
    rw [hΦs, hΦs] at h1
    have hunit : IsUnit (algebraMap A C ((l : A) ^ a * t ^ b')) := by
      rw [map_mul, map_pow, map_pow, map_natCast]
      exact (hl.pow a).mul (hct.pow b')
    have h2 : σC g (Φ z i) = algebraMap A C (χ g) ^ s * Φ z i := by
      rw [← hΦT]
      apply hunit.mul_left_cancel
      rw [h1, map_mul _ _ (χ g ^ s), map_pow, mul_assoc]
    have h3 : σC g (algebraMap A C t ^ s) = algebraMap A C (χ g) ^ s * algebraMap A C t ^ s := by
      rw [map_pow, hσ, hσt, map_mul, mul_pow]
    have h4 : σC g (algebraMap A C t ^ s) * σC g u = 1 := by rw [← map_mul, hu, map_one]
    rw [map_mul, h2]
    calc σC g u * (algebraMap A C (χ g) ^ s * Φ z i)
        = σC g u * (algebraMap A C (χ g) ^ s * ((algebraMap A C t ^ s * u) * Φ z i)) := by
          rw [hu, one_mul]
      _ = (σC g (algebraMap A C t ^ s) * σC g u) * (u * Φ z i) := by rw [h3]; ring
      _ = u * Φ z i := by rw [h4, one_mul]
  choose a₀ w₀ hw₀ using fun i => hfix (u * Φ z i) (hy i)
  obtain ⟨S, hS⟩ : ∃ S, S = (Φ z).support := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = S.sup a₀ := ⟨_, rfl⟩
  let f : I →₀ K := Finsupp.onFinset S
    (fun i => if i ∈ S then algebraMap W K ((l : W) ^ (N - a₀ i) * w₀ i) else 0)
    (by intro i hi; by_contra h; simp [h] at hi)
  have hf : ∀ i, algebraMap K C (f i) = (l : C) ^ N * (u * Φ z i) := by
    intro i
    by_cases hi : i ∈ S
    · have hle : a₀ i ≤ N := hN ▸ Finset.le_sup hi
      simp only [f, Finsupp.onFinset_apply, if_pos hi]
      rw [← IsScalarTower.algebraMap_apply W K C, map_mul, map_pow, map_natCast, ← hw₀ i,
        ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · have h0 : Φ z i = 0 := by simpa [hS] using hi
      simp [f, hi, h0]
  have hloc : IsLocalizedModule (nonZeroDivisors W) (TensorProduct.mk W K L 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors W) K _).2
      (TensorProduct.isBaseChange W L K)
  obtain ⟨⟨y₀, d⟩, hd⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors W) (TensorProduct.mk W K L 1) (b.repr.symm f)
  obtain ⟨m, β, hdβ, hβ⟩ := hW d (nonZeroDivisors.ne_zero d.2)
  obtain ⟨β', hβ'⟩ := hβ.exists_left_inv
  obtain ⟨y₁, hy₁d⟩ : ∃ y₁, y₁ = β' • y₀ := ⟨_, rfl⟩
  have hy₁ : (1 : K) ⊗ₜ[W] y₁ = ((l : W) ^ m) • b.repr.symm f := by
    have h5 : (d : W) • b.repr.symm f = (1 : K) ⊗ₜ[W] y₀ := hd
    rw [hy₁d, TensorProduct.tmul_smul, ← h5, smul_smul, hdβ]
    congr 1
    calc β' * ((l : W) ^ m * β) = (β' * β) * (l : W) ^ m := by ring
      _ = (l : W) ^ m := by rw [hβ', one_mul]
  have hrep : ∀ i, algebraMap K C (b.repr (1 ⊗ₜ y₁) i) =
      (l : C) ^ m * ((l : C) ^ N * (u * Φ z i)) := by
    intro i
    rw [hy₁, ← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply,
      smul_eq_mul, map_mul, hf, ← IsScalarTower.algebraMap_apply, map_pow, map_natCast]
  have hΦx : Φ ((l : A) ^ (m + N) • z - t ^ s • ((1 : A) ⊗ₜ[W] y₁)) = 0 := by
    ext i
    rw [hΦsub, Finsupp.sub_apply, hΦs, hΦs, hΦt, hrep]
    simp only [map_pow, map_natCast, map_one, one_mul, Finsupp.coe_zero, Pi.zero_apply]
    have h6 : algebraMap A C t ^ s * ((l : C) ^ m * ((l : C) ^ N * (u * Φ z i))) =
        (l : C) ^ m * (l : C) ^ N * ((algebraMap A C t ^ s * u) * Φ z i) := by ring
    rw [h6, hu, pow_add]
    ring
  have hRx : R ((l : A) ^ (m + N) • z - t ^ s • ((1 : A) ⊗ₜ[W] y₁)) = 0 := by
    rw [hΦ] at hΦx
    exact e.map_eq_zero_iff.1 hΦx
  obtain ⟨b', hb'⟩ := loc_ker t _ (hR ▸ hRx)
  refine ⟨m + N, b', y₁, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at hb'
  rw [mul_comm, hb', pow_add]

theorem UpperTheory.galois_equivariant_tensor_descent_of_prime_power_units :
    ∀ (l : ℕ) {W A C Γ : Type} {L : Type 1} [CommRing W] [IsDomain W] [CommRing A] [Algebra W A] [CommRing C]
        [AddCommGroup L] [Module W L] (c : A →+* C) (t : A) (σA : Γ → A →+* A) (σC : Γ → C →+* C) (χ : Γ → A)
        (T : Γ → (A ⊗[W] L →+ A ⊗[W] L)) (z : A ⊗[W] L) (s : ℕ),
        (∀ y : W, y ≠ 0 → ∃ (m : ℕ) (b : W), y = (l : W) ^ m * b ∧ IsUnit b) →
        IsUnit (l : C) → IsUnit (c t) →
        (∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) →
        (∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0) →
        (∀ g a, σC g (c a) = c (σA g a)) →
        (∀ g (w : W), σA g (algebraMap W A w) = algebraMap W A w) →
        (∀ g, σA g t = χ g * t) →
        (∀ g (a : A) (y : L), T g (a ⊗ₜ[W] y) = σA g a ⊗ₜ[W] y) →
        (∀ x : C, (∀ g, σC g x = x) → ∃ (a : ℕ) (w : W), (l : C) ^ a * x = c (algebraMap W A w)) →
        (∀ g, ∃ a b : ℕ, ((l : A) ^ a * t ^ b) • T g z = ((l : A) ^ a * t ^ b * χ g ^ s) • z) →
        ∃ (a b : ℕ) (y : L), ((l : A) ^ a * t ^ b) • z = (t ^ (b + s)) • ((1 : A) ⊗ₜ[W] y) := by
  intro l W A C Γ L _ _ _ _ _ _ _ c t σA σC χ T z s hW hl hct hlocC hker hσ hσW hσt hT hfix hz
  letI : Algebra A C := c.toAlgebra
  letI : Algebra W C := (c.comp (algebraMap W A)).toAlgebra
  haveI : IsScalarTower W A C := IsScalarTower.of_algebraMap_eq' rfl
  have hunit : ∀ y : nonZeroDivisors W, IsUnit (algebraMap W C y) := by
    intro y
    obtain ⟨m, β, h, hβ⟩ := hW y (nonZeroDivisors.ne_zero y.2)
    rw [h, map_mul, map_pow, map_natCast]
    exact (hl.pow m).mul (hβ.map _)
  letI : Algebra (FractionRing W) C := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower W (FractionRing W) C :=
    IsScalarTower.of_algebraMap_eq (fun w => (IsLocalization.lift_eq hunit w).symm)
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        exact (map_pow c t n).symm ▸ hct.pow n
      surj := by
        intro x
        obtain ⟨r, a, h⟩ := hlocC x
        refine ⟨(a, ⟨t ^ r, r, rfl⟩), ?_⟩
        change x * c (t ^ r) = c a
        rw [map_pow, mul_comm, h]
      exists_of_eq := by
        intro x y h
        obtain ⟨r, hr⟩ := hker (x - y) (by
          rw [map_sub, sub_eq_zero]
          exact h)
        refine ⟨⟨t ^ r, r, rfl⟩, ?_⟩
        rw [mul_sub, sub_eq_zero] at hr
        exact hr }
  exact aux (K := FractionRing W) l t σA σC χ T z s hW hl hσ hσW hσt hT hfix hz
