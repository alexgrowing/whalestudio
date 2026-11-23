import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

open QuadraticAlgebra Matrix Polynomial

namespace UpperTheory.V.Z.Sym.Glob

open Loc

variable {K : Type} [Field K] {Δ τ : K}

private theorem quo_eq {z : (Etau K τ)ˣ} {u : Etau K τ} : quo z = u ↔ (z : Etau K τ) = u * star (z : Etau K τ) := by
  have h : star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ) = 1 := by
    rw [← star_mul', Units.inv_mul, star_one]
  unfold quo
  constructor
  · rintro rfl
    rw [mul_assoc, h, mul_one]
  · intro e
    calc _ = u * star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) := by rw [← e]
      _ = u := by rw [mul_assoc, mul_comm (star _), h, mul_one]

private theorem h90E [CharZero K] (hτ : τ ^ 2 - 4 ≠ 0) (u : Etau K τ) (hu : u * star u = 1) :
    ∃ z : (Etau K τ)ˣ, quo z = u := by
  have hn : u.re * u.re + τ * u.re * u.im + u.im * u.im = 1 := by
    have := congrArg QuadraticAlgebra.re hu
    simp [QuadraticAlgebra.re_one] at this
    linear_combination this
  by_cases h : 2 + (2 * u.re + τ * u.im) = 0
  · have hz : IsUnit ((ω - star ω : Etau K τ) * (1 - u)) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, isUnit_iff_ne_zero]
      have : QuadraticAlgebra.norm ((ω - star ω : Etau K τ) * (1 - u)) = -4 * (τ ^ 2 - 4) := by
        simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
        linear_combination (4 - τ ^ 2) * hn + (τ ^ 2 - 4) * h
      rw [this]
      exact mul_ne_zero (by norm_num) hτ
    refine ⟨hz.unit, quo_eq.2 ?_⟩
    simp only [IsUnit.unit_spec, star_mul', star_sub, star_star, star_one]
    linear_combination (star ω - ω : Etau K τ) * hu
  · have hz : IsUnit (1 + u) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, isUnit_iff_ne_zero]
      have : QuadraticAlgebra.norm (1 + u) = 2 + (2 * u.re + τ * u.im) := by
        simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
        linear_combination hn
      rwa [this]
    refine ⟨hz.unit, quo_eq.2 ?_⟩
    simp only [IsUnit.unit_spec, star_add, star_one]
    linear_combination -hu

private theorem sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_ofE (u : Etau K τ) : sigL (ofE Δ u) = ofE Δ u := by
  ext <;> simp [sigL, ofE]

private theorem sigL_one : sigL (1 : EL Δ τ) = 1 := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem sigL_sigL (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem ofE_omega : ofE Δ (ω : Etau K τ) = ω := by
  ext <;> simp [ofE]

private theorem ofE_norm {u : Etau K τ} (h : ofE Δ u * star (ofE Δ u) = 1) : u * star u = 1 := by
  have h1 := congrArg (fun x => x.re.re) h
  simp [ofE, QuadraticAlgebra.re_one] at h1
  ext
  · simp [QuadraticAlgebra.re_one]
    linear_combination h1
  · simp [QuadraticAlgebra.im_one]
    ring

private theorem ofE_eq_one {u : Etau K τ} (h : ofE Δ u = 1) : u = 1 := by
  have h1 := congrArg (fun x => x.re.re) h
  have h2 := congrArg (fun x => x.im.re) h
  simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at h1 h2
  ext
  · simpa [QuadraticAlgebra.re_one] using h1
  · simpa [QuadraticAlgebra.im_one] using h2

private theorem fix_sigL [CharZero K] {w : EL Δ τ} (h : sigL w = w) : ∃ u, w = ofE Δ u := by
  have h1 := congrArg (fun x => x.re.im) h
  have h2 := congrArg (fun x => x.im.im) h
  simp [sigL] at h1 h2
  refine ⟨⟨w.re.re, w.im.re⟩, ?_⟩
  ext <;> simp [ofE]
  · linear_combination (-1 / 2 : K) * h1
  · linear_combination (-1 / 2 : K) * h2

private theorem trace_nondeg (hτ : τ ^ 2 - 4 ≠ 0) {w : EL Δ τ} (h : ∀ x, QuadraticAlgebra.trace (w * x) = 0) : w = 0 := by
  have h1 := h 1
  have h2 := h ω
  simp [QuadraticAlgebra.trace_def] at h1 h2
  have hu : IsUnit (algebraMap K (Lsq K Δ) (τ ^ 2 - 4)) := (IsUnit.mk0 _ hτ).map _
  rw [map_sub, map_pow, map_ofNat] at hu
  refine QuadraticAlgebra.ext ?_ ?_
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * h1 - (algebraMap K (Lsq K Δ) τ) * h2
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination 2 * h2 - (algebraMap K (Lsq K Δ) τ) * h1

private theorem semi_semi {c : K} {d m : EL Δ τ} (h : IsDat c d m) (x : Sp Δ τ) : semi d (semi d x) = (x.1, ω * x.2) := by
  simp only [semi, star_star, sigL_mul, sigL_sigL, ← mul_assoc, h.d_norm, ofE_omega]

private theorem shape (hτ : τ ^ 2 - 4 ≠ 0) (X : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ)
    (hN : ∀ x, X (x.1, ω * x.2) = ((X x).1, ω * (X x).2)) :
    ∃ (a : Lsq K Δ) (w : EL Δ τ), ∀ x, X x = (a * x.1, w * x.2) := by
  have hu : IsUnit (ω - 1 : EL Δ τ) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    have h2 : (2 - τ) ≠ 0 := fun h => hτ (by linear_combination (-2 - τ) * h)
    have := (IsUnit.mk0 _ h2).map (algebraMap K (Lsq K Δ))
    rw [map_sub, map_ofNat] at this
    convert this using 1
    simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  have h1 : (X (1, 0)).2 = 0 := by
    have := congrArg Prod.snd (hN (1, 0))
    simp only [mul_zero] at this
    refine hu.mul_right_eq_zero.1 ?_
    linear_combination -this
  have h2 : ∀ y, (X (0, y)).1 = 0 := by
    intro y
    obtain ⟨v, rfl⟩ : ∃ v, y = (ω - 1) * v := ⟨hu.unit⁻¹ * y, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    have e : ((0, (ω - 1) * v) : Sp Δ τ) = (0, ω * v) - (0, v) := by
      simp [sub_mul]
    have := congrArg Prod.fst (hN (0, v))
    simp only at this
    rw [e, map_sub, Prod.fst_sub, this, sub_self]
  have h3 : X (0, ω) = (0, ω * (X (0, 1)).2) := by
    have := hN (0, 1)
    simpa [h2] using this
  refine ⟨(X (1, 0)).1, (X (0, 1)).2, fun x => ?_⟩
  have e : x = x.1 • ((1, 0) : Sp Δ τ) + x.2.re • (0, 1) + x.2.im • (0, ω) := by
    refine Prod.ext (by simp) (QuadraticAlgebra.ext ?_ ?_) <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  conv_lhs => rw [e]
  rw [map_add, map_add, map_smul, map_smul, map_smul, h3]
  refine Prod.ext ?_ ?_
  · simp [h2, mul_comm]
  · simp only [Prod.snd_add, Prod.smul_snd, h1, smul_zero, zero_add]
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp <;> ring

private theorem key [CharZero K] {c : K} {d m : EL Δ τ} (h : IsDat c d m) (X : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ)
    (hs : ∀ x, X (semi d x) = semi d (X x)) (hh : ∀ x y, herm c m (X x) (X y) = herm c m x y) :
    ∃ z, (∀ x, X x = tor Δ z x) ∨ ∀ x, -X x = tor Δ z x := by
  obtain ⟨a, w, hX⟩ := shape h.reg X fun x => by rw [← semi_semi h, hs, hs, semi_semi h]
  have hω : IsUnit (ω : EL Δ τ) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    simp [QuadraticAlgebra.norm_def]
  have hd : IsUnit d := isUnit_of_mul_isUnit_left (by rw [h.d_norm, ofE_omega]; exact hω)
  have s1 := hs (1, 1)
  simp only [hX, semi, star_one, mul_one, sigL_one, Prod.mk.injEq] at s1
  have hw : sigL w = w := (hd.mul_left_cancel (by rw [← s1.2, mul_comm])).symm
  have ha : a * a = 1 := by
    have := hh (1, 0) (1, 0)
    simp only [hX, herm, mul_zero, zero_mul, map_zero, add_zero, mul_one, star_one, ← s1.1] at this
    have hc : IsUnit (algebraMap K (Lsq K Δ) c) := (IsUnit.mk0 _ h.c_ne).map _
    exact hc.mul_left_cancel (by rw [← mul_assoc, this, mul_one])
  have ha' : a = 1 ∨ a = -1 := by
    have i1 := congrArg QuadraticAlgebra.im s1.1
    have i2 : a.im = 0 := by
      simp at i1
      linear_combination (1 / 2 : K) * i1
    have i3 := congrArg QuadraticAlgebra.re ha
    simp [i2, QuadraticAlgebra.re_one] at i3
    rcases mul_self_eq_one_iff.1 i3 with e | e
    · left; ext <;> simp [e, i2, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · right; ext <;> simp [e, i2, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hww : w * star w = 1 := by
    have : m * (w * star w - 1) = 0 := by
      refine trace_nondeg h.reg fun x => ?_
      have := hh (0, x) (0, 1)
      simp only [hX, herm, mul_zero, zero_mul, zero_add, mul_one, star_one, sigL_one, hw] at this
      rw [← sub_eq_zero, ← map_sub] at this
      rw [← this]
      congr 1
      ring
    exact sub_eq_zero.1 (h.m_unit.mul_right_eq_zero.1 this)
  obtain ⟨u, rfl⟩ := fix_sigL hw
  have hu := ofE_norm hww
  rcases ha' with rfl | rfl
  · obtain ⟨z, hz⟩ := h90E h.reg u hu
    exact ⟨z, Or.inl fun x => by simp [hX, tor, hz]⟩
  · obtain ⟨z, hz⟩ := h90E h.reg (-u) (by simpa using hu)
    have e : ofE Δ (-u) = -ofE Δ u := by ext <;> simp [ofE]
    exact ⟨z, Or.inr fun x => by simp [hX, tor, hz, e]⟩

private theorem mat_ext {R : Type} [CommRing R] {M : Type} (P : M → Fin 3 → R) (hP : Function.Surjective P)
    {A B : Matrix (Fin 3) (Fin 3) R} (h : ∀ x, A *ᵥ P x = B *ᵥ P x) : A = B := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := hP v
  simpa using h x

private theorem theta_mulVec (g : U3 Δ) (v : Fin 3 → Lsq K Δ) :
    ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star v = star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) := by
  funext i
  simp [theta, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem unitary_form (g : U3 Δ) (v w : Fin 3 → Lsq K Δ) :
    ∑ i, ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) i * star (((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ w) i) =
      ∑ i, v i * star (w i) := by
  change ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) ⬝ᵥ star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ w) = v ⬝ᵥ star w
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    g.2.1, Matrix.one_mulVec, dotProduct_comm]

private theorem comm_iff {d : EL Δ τ} {δ : U3 Δ} {P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}
    (hs : ∀ x, P (semi d x) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x)) (x : U3 Δ) (X : Sp Δ τ → Sp Δ τ)
    (hX : ∀ v, P (X v) = (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P v) :
    x⁻¹ * δ * theta Δ x = δ ↔ ∀ v, X (semi d v) = semi d (X v) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  have e : ∀ v, X (semi d v) = semi d (X v) ↔
      ((δ * theta Δ x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P v) = ((x * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P v) := by
    intro v
    rw [← P.injective.eq_iff, hX, hs, hs, hX, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      theta_mulVec, eq_comm]
  simp only [e]
  constructor
  · intro h v
    rw [h]
  · intro h
    exact Subtype.ext (mat_ext (fun v => star (P v)) (star_involutive.surjective.comp P.surjective) h)

private theorem charpoly_N :
    (LinearMap.prodMap (1 : Lsq K Δ →ₗ[Lsq K Δ] Lsq K Δ) (LinearMap.mulLeft (Lsq K Δ) (ω : EL Δ τ))).charpoly =
      (X - 1) * (X ^ 2 - C (algebraMap K _ τ) * X + 1) := by
  have hb : ∀ (x : EL Δ τ) i, (QuadraticAlgebra.basis (-1) (algebraMap K (Lsq K Δ) τ)).repr x i = ![x.re, x.im] i := fun x i => by
    rw [QuadraticAlgebra.basis_repr_apply]
  have b0 : QuadraticAlgebra.basis (-1) (algebraMap K (Lsq K Δ) τ) 0 = 1 := by
    refine (QuadraticAlgebra.basis (-1) (algebraMap K (Lsq K Δ) τ)).repr.injective (Finsupp.ext fun i => ?_)
    rw [Module.Basis.repr_self, hb]
    fin_cases i <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have b1 : QuadraticAlgebra.basis (-1) (algebraMap K (Lsq K Δ) τ) 1 = ω := by
    refine (QuadraticAlgebra.basis (-1) (algebraMap K (Lsq K Δ) τ)).repr.injective (Finsupp.ext fun i => ?_)
    rw [Module.Basis.repr_self, hb]
    fin_cases i <;> simp
  rw [LinearMap.charpoly_prodMap, LinearMap.charpoly_one, Module.finrank_self, pow_one,
    ← LinearMap.charpoly_toMatrix _ (QuadraticAlgebra.basis _ _), Matrix.charpoly_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, LinearMap.toMatrix_apply, hb, b0, b1, LinearMap.mulLeft_apply]
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc in
theorem UpperTheory.V.Z.Sym.Glob.modelFacts :
    UpperTheory.V.Z.Sym.Glob.ModelFacts := by
  intro K _ _ Δ τ c d m δ ι P _ hD hM
  have hneg : ∀ (x : U3 Δ) (v : Fin 3 → Lsq K Δ), ((negU Δ * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v =
      -((x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) := fun x v => by
    simp [negU, Matrix.neg_mulVec]
  refine ⟨?_, ?_, ?_, fun x => ?_⟩
  · unfold HasTau
    rw [← charpoly_N, ← LinearEquiv.charpoly_conj P, ← Matrix.charpoly_toLin']
    congr 1
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := P.surjective v
    have := congrArg P (semi_semi hD x)
    rw [hM.semi, hM.semi, ← theta_mulVec, star_star, Matrix.mulVec_mulVec] at this
    simpa [LinearEquiv.conj_apply] using this
  · ext z
    have e : z ∈ scalE τ ↔ quo z = 1 := by
      rw [quo_eq, one_mul]
      constructor
      · rintro ⟨s, rfl⟩
        ext <;> simp
      · intro h
        have i1 := congrArg QuadraticAlgebra.im h
        have i2 : (z : Etau K τ).im = 0 := by
          simp at i1
          linear_combination (1 / 2 : K) * i1
        have i3 : (z : Etau K τ).re ≠ 0 := fun h0 => z.ne_zero (by ext <;> simp [h0, i2])
        refine ⟨Units.mk0 _ i3, Units.ext ?_⟩
        ext <;> simp [i2]
    rw [e, MonoidHom.mem_ker]
    constructor
    · intro h
      have := hM.tor z (0, 1)
      rw [h, OneMemClass.coe_one, Matrix.one_mulVec, P.injective.eq_iff] at this
      exact ofE_eq_one (by simpa [tor] using this)
    · intro h
      refine Subtype.ext (mat_ext P P.surjective fun x => ?_)
      have e1 : ofE Δ (1 : Etau K τ) = 1 := by
        ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      rw [← hM.tor]
      simp [tor, h, e1]
  · rintro ⟨z, hz⟩
    have := hM.tor z (1, 0)
    rw [hz, ← mul_one (negU Δ), hneg, OneMemClass.coe_one, Matrix.one_mulVec, ← map_neg, P.injective.eq_iff] at this
    have h2 := congrArg (fun x => x.1.re) this
    simp [tor, QuadraticAlgebra.re_one] at h2
    norm_num at h2
  · have hX : ∀ v, P ((P.symm.conj (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)))) v) =
        (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P v := fun v => by
      simp [LinearEquiv.conj_apply]
    have hc : ∀ z v, tor Δ z (semi d v) = semi d (tor Δ z v) := fun z v => by
      simp only [tor, semi, sigL_mul, sigL_ofE, mul_left_comm]
    constructor
    · intro h
      obtain ⟨z, hz | hz⟩ := key hD _ ((comm_iff hM.semi x _ hX).1 h) fun v w => by
        rw [hM.form, hM.form, hX, hX, unitary_form]
      · exact Or.inl ⟨z, Subtype.ext (mat_ext P P.surjective fun v => by rw [← hM.tor, ← hz, hX])⟩
      · exact Or.inr ⟨z, Subtype.ext (mat_ext P P.surjective fun v => by rw [← hM.tor, ← hz, map_neg, hX, hneg])⟩
    · rintro (⟨z, rfl⟩ | ⟨z, hz⟩)
      · exact (comm_iff hM.semi _ _ (hM.tor z)).2 (hc z)
      · refine (comm_iff hM.semi x (fun v => -tor Δ z v) fun v => ?_).2 fun v => ?_
        · rw [map_neg, hM.tor, hz, hneg, neg_neg]
        · have e : ∀ y : EL Δ τ, sigL (-y) = -sigL y := fun y => by ext <;> simp [sigL]
          rw [hc]
          simp [semi, e]
