import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder

open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.SiegelChar

namespace GlobalTheory.CompanionTheory.Ar.RT.Siegel

theorem finite_nonunit {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    (p : Polynomial E) (τ : E) (h : IsUnit (p.eval τ)) : {t : F | ¬ IsUnit (p.eval (algebraMap F E t))}.Finite := by
  have hm : ∀ m : MaximalSpectrum E, {t : F | p.eval (algebraMap F E t) ∈ m.asIdeal}.Finite := by
    intro m
    haveI := m.isMaximal
    have hq : p.map (Ideal.Quotient.mk m.asIdeal) ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval (Ideal.Quotient.mk m.asIdeal τ)) h0
      rw [Polynomial.eval_map_apply, Polynomial.eval_zero] at this
      exact (h.map (Ideal.Quotient.mk m.asIdeal)).ne_zero this
    refine ((Polynomial.finite_setOf_isRoot hq).preimage
      (f := ((Ideal.Quotient.mk m.asIdeal).comp (algebraMap F E))) (RingHom.injective _).injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Polynomial.IsRoot, RingHom.comp_apply, Polynomial.eval_map_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht
  refine (Set.finite_iUnion hm).subset ?_
  intro t ht
  obtain ⟨m, hm1, hm2⟩ := exists_max_ideal_of_mem_nonunits ht
  exact Set.mem_iUnion.mpr ⟨⟨m, hm1⟩, hm2⟩

theorem finite_nonunit_matrix {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    {β : Type} [Fintype β] [DecidableEq β] (A B D : Matrix β β E) (τ : E) (h : IsUnit (A + τ • B + (τ * τ) • D)) :
    {t : F | ¬ IsUnit (A + algebraMap F E t • B + (algebraMap F E t * algebraMap F E t) • D)}.Finite := by
  have key : ∀ z : E, ((A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C +
      ((Polynomial.X : Polynomial E) * Polynomial.X) • D.map Polynomial.C).det).eval z =
      (A + z • B + (z * z) • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  simp only [Matrix.isUnit_iff_isUnit_det, ← key] at h ⊢
  exact finite_nonunit _ τ h

theorem triv_of_cell {F : Type} [Field F] [Infinite F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    {β : Type} [Fintype β] [DecidableEq β] {c : E →ₐ[F] E} {ξ : E} (hξ : IsUnit ξ) (h2 : IsUnit (2 : E))
    (hc : c ξ = -ξ) {σ : Matrix β β E →+ Matrix β β E} {G : Type} [Group G] {φ : G →* Matrix β β E}
    {e f : Matrix β β E} (hsm : ∀ (a : E) x, σ (a • x) = c a • σ x) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1)
    (hu : ∀ g, σ (φ g) * φ g = 1) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0) (lam : G →* ℂˣ)
    (hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1) (g : G) : lam g = 1 := by
  have hk1 : φ g⁻¹ * φ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hk2 : φ g * φ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hσh : σ (φ g) = φ g⁻¹ := by
    calc σ (φ g) = σ (φ g) * φ g * φ g⁻¹ := by rw [mul_assoc, hk2, mul_one]
      _ = _ := by rw [hu, one_mul]
  have hσk : σ (φ g⁻¹) = φ g := by
    calc σ (φ g⁻¹) = σ (φ g⁻¹) * φ g⁻¹ * φ g := by rw [mul_assoc, hk1, mul_one]
      _ = _ := by rw [hu, one_mul]
  generalize hkd : φ g⁻¹ = k at hk1 hk2 hσh hσk
  generalize hhd : φ g = h at hk1 hk2 hσh hσk
  have hunit : ∀ a b : E, IsUnit a → IsUnit b → IsUnit (a • e + b • f) := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine IsUnit.of_mul_eq_one (((a⁻¹ : Eˣ) : E) • e + ((b⁻¹ : Eˣ) : E) • f) ?_
    simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, Units.mul_inv, one_smul,
      zero_add, add_zero, hef]
  let y : E → Matrix β β E := fun t => (t * t + t * ξ) • h + (t - ξ) • 1
  let y' : E → Matrix β β E := fun t => (t * t - t * ξ) • k + (t + ξ) • 1
  have e1 : ∀ t, y' t = ξ • 1 + t • (1 - ξ • k) + (t * t) • k := by
    intro t; simp only [y']; module
  have e2 : ∀ (t : E) (z : Matrix β β E), y t * e + y' t * z = ((-ξ) • e + ξ • z) + t • (ξ • (h * e) + e - ξ • (k * z) + z) +
      (t * t) • (h * e + k * z) := by
    intro t z; simp only [y, y', add_mul, smul_mul_assoc, one_mul]; module
  have f1 : {t : F | ¬ IsUnit (y' (algebraMap F E t))}.Finite := by
    simp only [e1]
    refine finite_nonunit_matrix _ _ _ 0 ?_
    rw [← e1]
    simp only [y', mul_zero, zero_mul, sub_zero, zero_smul, zero_add]
    rw [← hef, smul_add]
    exact hunit _ _ hξ hξ
  have f2 : {t : F | ¬ IsUnit (y (algebraMap F E t) * e + y' (algebraMap F E t) * f)}.Finite := by
    simp only [e2]
    refine finite_nonunit_matrix _ _ _ 0 ?_
    simp only [mul_zero, zero_smul, add_zero]
    exact hunit _ _ hξ.neg hξ
  have f3 : {t : F | ¬ IsUnit (y (algebraMap F E t) * e + y' (algebraMap F E t) * (h * f))}.Finite := by
    simp only [e2]
    refine finite_nonunit_matrix _ _ _ ξ ?_
    rw [← e2]
    have : y ξ * e + y' ξ * (h * f) = h * ((2 * ξ * ξ) • e + (2 * ξ) • f) := by
      simp only [y, y', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, sub_self, zero_smul, zero_mul]; module
    rw [this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul (hunit _ _ ((h2.mul hξ).mul hξ) (h2.mul hξ))
  obtain ⟨t, ht⟩ := ((f1.union f2).union f3).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at ht
  obtain ⟨⟨⟨W, hW⟩, u2⟩, u3⟩ := ht
  have s1 : σ (y (algebraMap F E t)) = y' (algebraMap F E t) := by
    simp only [y, y', map_add, hsm, hσh, h1, map_mul, map_sub, c.commutes, hc]; module
  have s2 : σ (y' (algebraMap F E t)) = y (algebraMap F E t) := by
    simp only [y, y', map_add, hsm, hσk, h1, map_mul, map_sub, c.commutes, hc]; module
  have cm : y (algebraMap F E t) * y' (algebraMap F E t) = y' (algebraMap F E t) * y (algebraMap F E t) := by
    simp only [y, y', add_mul, mul_add, smul_mul_smul_comm, hk1, hk2, one_mul, mul_one]; module
  have w1 : y' (algebraMap F E t) * (↑W⁻¹ : Matrix β β E) = 1 := by rw [← hW, Units.mul_inv]
  have w2 : (↑W⁻¹ : Matrix β β E) * y' (algebraMap F E t) = 1 := by rw [← hW, Units.inv_mul]
  have wu : IsUnit (↑W⁻¹ : Matrix β β E) := Units.isUnit _
  generalize (↑W⁻¹ : Matrix β β E) = w at w1 w2 wu
  generalize y (algebraMap F E t) = Y at s1 s2 cm u2 u3
  generalize y' (algebraMap F E t) = Y' at s1 s2 cm u2 u3 w1 w2
  have cw : w * Y = Y * w := by
    calc w * Y = w * (Y * Y') * w := by rw [mul_assoc w, mul_assoc Y, w1, mul_one]
      _ = Y * w := by rw [cm, ← mul_assoc, w2, one_mul]
  obtain ⟨x, hx⟩ := hsurj (w * Y) (by
    have : σ w * Y = 1 := by rw [← s2, ← hmul, w1, h1]
    rw [hmul, s1, cw, mul_assoc, ← mul_assoc (σ w), this, one_mul, w1])
  have l1 : lam x = 1 := hcell x (by
    have : φ x * e + f = w * (Y * e + Y' * f) := by rw [hx, mul_add, ← mul_assoc w Y', w2, one_mul, mul_assoc]
    rw [this]; exact wu.mul u2)
  have l2 : lam (g⁻¹ * x) = 1 := hcell _ (by
    have : φ (g⁻¹ * x) * e + f = k * (w * (Y * e + Y' * (h * f))) := by
      rw [map_mul, hkd, hx, mul_add, ← mul_assoc w Y', w2, one_mul, mul_add, ← mul_assoc k h, hk1, one_mul]
      simp only [mul_assoc]
    rw [this]; exact (IsUnit.of_mul_eq_one _ hk1).mul (wu.mul u3))
  rwa [map_mul, l1, mul_one, map_inv, inv_eq_one] at l2

theorem char_trivial_artinian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [CommRing E] [IsArtinianRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsUnit ξ → c ξ = -ξ → (∀ x, c (c x) = x) → IsUnit J.det → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  intro F _ _ E _ _ _ c ξ β ν _ _ _ _ J Cy hξ hanti hinvol hJ hL lam hlam
  obtain ⟨hy, Cx, M, hx, hM1, hM2⟩ := hL
  have cmul : ∀ {l m n : Type} [Fintype m] (a : Matrix l m E) (b : Matrix m n E), (a * b).map c = a.map c * b.map c :=
    fun a b => Matrix.map_mul (f := c.toRingHom)
  have cone : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have cc : ∀ a : Matrix β β E, (a.map c).map c = a := fun a => by ext i j; exact hinvol _
  have J1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have J2 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hJ
  let σ : Matrix β β E →+ Matrix β β E := AddMonoidHom.mk' (fun x => (J⁻¹ * xᵀ * J).map c) (fun a b => by
    rw [transpose_add, mul_add, add_mul, Matrix.map_add _ (map_add c)])
  have hσ : ∀ x, σ x = (J⁻¹ * xᵀ * J).map c := fun _ => rfl
  have hsm : ∀ (a : E) x, σ (a • x) = c a • σ x := fun a x => by
    rw [hσ, hσ, transpose_smul, mul_smul_comm, smul_mul_assoc]
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hmul : ∀ x y, σ (x * y) = σ y * σ x := fun x y => by
    rw [hσ, hσ, hσ, ← cmul, transpose_mul]
    congr 1
    calc _ = J⁻¹ * yᵀ * (J * J⁻¹) * xᵀ * J := by rw [J1, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have h1 : σ 1 = 1 := by rw [hσ, transpose_one, mul_one, J2, cone]
  have hform : ∀ x y, σ x * y = (J⁻¹ * (xᵀ * J * y.map c)).map c := fun x y => by
    rw [hσ, ← mul_assoc, ← mul_assoc, cmul _ (y.map c), cc]
  let φ : UG c J →* Matrix β β E := (Units.coeHom _).comp (UG c J).subtype
  have hφ : ∀ g, φ g = ((g : GL β E) : Matrix β β E) := fun _ => rfl
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
  have hu : ∀ g, σ (φ g) * φ g = 1 := fun g => by
    rw [hform, show (φ g)ᵀ * J * (φ g).map c = J from g.2, J2, cone]
  have hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x := fun x h => by
    refine ⟨⟨⟨x, σ x, mul_eq_one_comm.mp h, h⟩, ?_⟩, rfl⟩
    change xᵀ * J * x.map c = J
    have := congrArg (fun z : Matrix β β E => J * z.map c) h
    simp only [hform, cc, cone] at this
    rwa [← mul_assoc, J1, one_mul, mul_one] at this
  rw [← Matrix.fromRows_toRows M] at hM1 hM2
  generalize M.toRows₁ = M1 at hM1 hM2
  generalize M.toRows₂ = M2 at hM1 hM2
  rw [fromCols_mul_fromRows] at hM1
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at hM2
  obtain ⟨m11, m12, m21, m22⟩ := hM2
  have hee : (Cy * M1) * (Cy * M1) = Cy * M1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M1, m11, Matrix.one_mul]
  have hff : (Cx * M2) * (Cx * M2) = Cx * M2 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M2, m22, Matrix.one_mul]
  have hef0 : (Cy * M1) * (Cx * M2) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M1, m12, Matrix.zero_mul, Matrix.mul_zero]
  have hfe0 : (Cx * M2) * (Cy * M1) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M2, m21, Matrix.zero_mul, Matrix.mul_zero]
  have iso : ∀ (C : Matrix β ν E) (N : Matrix ν β E), Cᵀ * J * C.map c = 0 → σ (C * N) * (C * N) = 0 := fun C N h => by
    rw [hform, transpose_mul, cmul C N]
    have : Nᵀ * Cᵀ * J * (C.map c * N.map c) = Nᵀ * (Cᵀ * J * C.map c) * N.map c := by simp only [Matrix.mul_assoc]
    rw [this, h, Matrix.mul_zero, Matrix.zero_mul, mul_zero, Matrix.map_zero _ (map_zero c)]
  have ie := iso Cy M1 hy
  have if' := iso Cx M2 hx
  have hP : ∀ g, (Cx * M2) * φ g * (Cy * M1) = 0 → lam g = 1 := fun g h => by
    have a : φ g * Cy = Cy * (M1 * φ g * Cy) := by
      have h' : (Cx * M2) * φ g * Cy = 0 := by
        have := congrArg (· * Cy) h
        simp only [Matrix.mul_assoc, m11, Matrix.mul_one, Matrix.zero_mul] at this ⊢
        exact this
      calc φ g * Cy = (Cy * M1 + Cx * M2) * φ g * Cy := by rw [hM1, one_mul]
        _ = _ := by rw [add_mul, Matrix.add_mul, h', add_zero]; simp only [Matrix.mul_assoc]
    have b : (M1 * φ g⁻¹ * Cy) * (M1 * φ g * Cy) = 1 := by
      rw [Matrix.mul_assoc, ← a, Matrix.mul_assoc, ← Matrix.mul_assoc (φ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mul, m11]
    exact hlam g ⟨_, _, mul_eq_one_comm.mp b, b⟩ a
  generalize Cy * M1 = e at *
  generalize Cx * M2 = f at *
  have hsum : σ e + σ f = 1 := by rw [← map_add, hM1, h1]
  have hse : σ e = f := by
    calc σ e = σ e * (e + f) + σ f * f := by rw [hM1, if', mul_one, add_zero]
      _ = (σ e + σ f) * f := by rw [mul_add, ie, zero_add, add_mul]
      _ = f := by rw [hsum, one_mul]
  have hsf : σ f = e := by
    rw [hse, ← hM1, add_comm e] at hsum
    exact add_left_cancel hsum
  have h2 : (2 : E) * algebraMap F E 2⁻¹ = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  have h3 : (3 : E) * algebraMap F E 3⁻¹ = 1 := by
    rw [← map_ofNat (algebraMap F E) 3, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  ext g
  rw [triv_of_cell hξ (IsUnit.of_mul_eq_one _ h2) hanti hsm hmul h1 hu hsurj hM1 hee hff hef0 hfe0 lam
    (cell_triv hmul h1 hu hM1 hee hff hef0 hfe0 hse hsf lam
      (lower_triv hsm h1 h2 h3 (map_ofNat c 2) (c.commutes _) (c.commutes _) hinj hsurj hM1 hee hff hef0 hfe0 hse hsf lam)
      hP) g]
  rfl

end GlobalTheory.CompanionTheory.Ar.RT.Siegel
