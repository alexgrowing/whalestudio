import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section H90

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K}

private theorem unit_of_norm (z : Lsq K Δ) (h : QuadraticAlgebra.norm z ≠ 0) :
    ∃ c : (Lsq K Δ)ˣ, (c : Lsq K Δ) = z ∧
      ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm z)⁻¹ * star z := by
  have h1 : z * (algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm z)⁻¹ * star z) = 1 := by
    rw [mul_left_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_mul, inv_mul_cancel₀ h, map_one]
  exact ⟨⟨z, _, h1, by rw [mul_comm]; exact h1⟩, rfl, rfl⟩

private def starO : Lsq K Δ →ₐ[O] Lsq K Δ :=
  { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) r]
      change star (algebraMap K (Lsq K Δ) _) = _
      ext <;> simp }

private theorem int_star {z : Lsq K Δ} (h : IsIntegral O z) : IsIntegral O (star z) :=
  h.map (starO (O := O) (K := K) (Δ := Δ))

private theorem dich [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K] (h2 : IsUnit (2 : O))
    {u : Lsq K Δ} (hu : IsIntegral O u) :
    (∃ v : Oˣ, algebraMap O K v = 2 + 2 * u.re) ∨ (∃ v : Oˣ, algebraMap O K v = 2 - 2 * u.re) := by
  have ht : IsIntegral O (algebraMap K (Lsq K Δ) (2 * u.re)) := by
    have : algebraMap K (Lsq K Δ) (2 * u.re) = u + star u := by
      ext <;> simp <;> ring
    rw [this]
    exact hu.add (int_star hu)
  have ht' : IsIntegral O (2 * u.re) :=
    (isIntegral_algebraMap_iff (algebraMap K (Lsq K Δ)).injective).1 ht
  haveI : IsDomain O := (IsFractionRing.injective O K).isDomain (algebraMap O K)
  obtain ⟨τ, hτ⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht'
  have h4 : IsUnit ((2 + τ) + (2 - τ) : O) := by
    have : ((2 + τ) + (2 - τ) : O) = 2 * 2 := by ring
    rw [this]
    exact h2.mul h2
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h4 with h | h
  · left
    exact ⟨h.unit, by simp [hτ, map_ofNat]⟩
  · right
    exact ⟨h.unit, by simp [hτ, map_ofNat]⟩

private theorem int_omega {d : O} (hd : algebraMap O K d = Δ) :
    IsIntegral O (QuadraticAlgebra.omega : Lsq K Δ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C d two_ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
    IsScalarTower.algebraMap_apply O K (Lsq K Δ), hd, pow_two,
    QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp

private theorem exists_unit_norm_quotient_lift (z u : Lsq K Δ) (hz : z = u * star z) (hn : QuadraticAlgebra.norm z ≠ 0)
    (hi : ∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) →
      (∃ v : Oˣ, algebraMap O K v = Δ) → IsIntegral O u →
        IsIntegral O z ∧ ∃ v : Oˣ, algebraMap O K v = QuadraticAlgebra.norm z) :
    ∃ c : (Lsq K Δ)ˣ, (c : Lsq K Δ) = u * star (c : Lsq K Δ) ∧
      ∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) →
        (∃ v : Oˣ, algebraMap O K v = Δ) → IsIntegral O u →
          IsIntegral O (c : Lsq K Δ) ∧ IsIntegral O ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := by
  obtain ⟨c, hc, hci⟩ := unit_of_norm z hn
  refine ⟨c, by rw [hc]; exact hz, ?_⟩
  intro _ _ _ h2 hΔ hu
  obtain ⟨hzi, v, hv⟩ := hi h2 hΔ hu
  refine ⟨by rw [hc]; exact hzi, ?_⟩
  rw [hci, ← hv, ← map_units_inv, ← IsScalarTower.algebraMap_apply]
  exact isIntegral_algebraMap.mul (int_star hzi)

private theorem ex_c (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (u : Lsq K Δ) (hu : u * star u = 1) :
    ∃ c : (Lsq K Δ)ˣ, (c : Lsq K Δ) = u * star (c : Lsq K Δ) ∧
      ∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) →
        (∃ v : Oˣ, algebraMap O K v = Δ) → IsIntegral O u →
          IsIntegral O (c : Lsq K Δ) ∧ IsIntegral O ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := by
  classical
  have r1 : (1 : Lsq K Δ).re = 1 := rfl
  have i1 : (1 : Lsq K Δ).im = 0 := rfl
  have hN1 : QuadraticAlgebra.norm u = 1 := by
    apply (algebraMap K (Lsq K Δ)).injective
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, hu, map_one]
  have hN := hN1
  rw [QuadraticAlgebra.norm_def] at hN
  by_cases hcase : (2 + 2 * u.re ≠ 0) ∧ ¬ ∃ v : Oˣ, algebraMap O K v = 2 - 2 * u.re
  · have hn : QuadraticAlgebra.norm (1 + u) = 2 + 2 * u.re := by
      rw [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, r1, i1]
      linear_combination hN
    apply exists_unit_norm_quotient_lift (1 + u) u (by rw [star_add, star_one, mul_add, hu]; ring) (by rw [hn]; exact hcase.1)
    intro _ _ _ h2' _ hi
    refine ⟨isIntegral_one.add hi, ?_⟩
    rcases dich h2' hi with ⟨v, hv⟩ | h
    · exact ⟨v, by rw [hn, hv]⟩
    · exact absurd h hcase.2
  · have hsω : star (QuadraticAlgebra.omega : Lsq K Δ) = -QuadraticAlgebra.omega := by
      ext <;> simp
    have hn : QuadraticAlgebra.norm ((1 - u) * QuadraticAlgebra.omega)
        = (2 - 2 * u.re) * (-Δ) := by
      rw [map_mul, QuadraticAlgebra.norm_def (1 - u), QuadraticAlgebra.norm_def QuadraticAlgebra.omega,
        QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, r1, i1, QuadraticAlgebra.omega_re,
        QuadraticAlgebra.omega_im]
      linear_combination (-Δ) * hN
    have hne : 2 - 2 * u.re ≠ 0 := by
      intro h0
      apply hcase
      refine ⟨fun h1 => h2 ?_, ?_⟩
      · have h4 : (2 : K) * 2 = 0 := by linear_combination h0 + h1
        exact mul_self_eq_zero.mp h4
      · rintro ⟨v, hv⟩
        rw [h0] at hv
        exact (v.isUnit.map (algebraMap O K)).ne_zero hv
    apply exists_unit_norm_quotient_lift ((1 - u) * QuadraticAlgebra.omega) u
      (by
        rw [star_mul', star_sub, star_one, hsω]
        linear_combination (-QuadraticAlgebra.omega) * hu)
      (by rw [hn]; exact mul_ne_zero hne (neg_ne_zero.mpr hΔ))
    intro _ _ _ h2' hΔ' hi
    obtain ⟨d, hd⟩ := hΔ'
    refine ⟨(isIntegral_one.sub hi).mul (int_omega hd), ?_⟩
    obtain ⟨w, hw⟩ : ∃ w : Oˣ, algebraMap O K w = 2 - 2 * u.re := by
      by_cases hB : ∃ w : Oˣ, algebraMap O K w = 2 - 2 * u.re
      · exact hB
      · have hA : 2 + 2 * u.re = 0 := by
          by_contra hA
          exact hcase ⟨hA, hB⟩
        refine ⟨h2'.unit * h2'.unit, ?_⟩
        rw [Units.val_mul, IsUnit.unit_spec, map_mul, map_ofNat]
        linear_combination hA
    exact ⟨-(w * d), by rw [hn, ← hw, ← hd]; simp⟩

private theorem mem_range (g : GL (Fin 2) (Lsq K Δ)) (h1 : ∀ i j, IsIntegral O (g.1 i j))
    (h2 : ∀ i j, IsIntegral O (g.inv i j)) :
    g ∈ (GeneralLinearGroup.map ((integralClosure O (Lsq K Δ)).val :
      integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range := by
  let f : integralClosure O (Lsq K Δ) →+* Lsq K Δ := (integralClosure O (Lsq K Δ)).val
  let F := RingHom.mapMatrix (m := Fin 2) f
  let A : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) :=
    Matrix.of fun i j => ⟨g.1 i j, h1 i j⟩
  let B : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) :=
    Matrix.of fun i j => ⟨g.inv i j, h2 i j⟩
  have hA : F A = g.1 := Matrix.ext fun i j => rfl
  have hB : F B = g.inv := Matrix.ext fun i j => rfl
  have inj : Function.Injective F := fun M N e =>
    Matrix.map_injective Subtype.val_injective e
  have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, g.val_inv, map_one])
  have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, g.inv_val, map_one])
  refine MonoidHom.mem_range.mpr ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

private theorem conj_two {A : Type} [CommRing A] (m : Matrix (Fin 2) (Fin 2) A) :
    !![0, -1; 1, 0] * m * !![0, 1; -1, 0] = !![m 1 1, -m 1 0; -m 0 1, m 0 0] := by
  rw [Matrix.eta_fin_two m]
  simp [Matrix.mul_fin_two]

end H90

theorem UpperTheory.V.Z.Sym.Dict.Br.h90 :
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (Δ : K), (2 : K) ≠ 0 → Δ ≠ 0 → ∀ x : Matrix (Fin 2) (Fin 2) (Lsq K Δ), star x * x = 1 → ∃ (y : DX Δ) (c : (Lsq K Δ)ˣ), x = (c : Lsq K Δ) • mt y ∧ (x = 1 → y = 1) ∧ (∀ [IsLocalRing O] [IsIntegrallyClosed O] [IsFractionRing O K], IsUnit (2 : O) → (∃ u : Oˣ, algebraMap O K u = Δ) → (∀ i j, IsIntegral O (x i j)) → y ∈ KD Δ O) := by
  intro O K _ _ _ Δ h2 hΔ x hx
  by_cases hx1 : x = 1
  · refine ⟨1, 1, ?_, fun _ => rfl, fun _ _ _ => one_mem _⟩
    subst hx1
    simp [Glob.mt]
  set u := x.det with hu_def
  have hxx : x * star x = 1 := mul_eq_one_comm.mp hx
  have hu : u * star u = 1 := by
    have e := congrArg Matrix.det hx
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose,
      Matrix.det_conjTranspose] at e
    rw [mul_comm]
    exact e
  obtain ⟨c, hc, hci⟩ := ex_c (O := O) h2 hΔ u hu
  set s : Lsq K Δ := ((c⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) with hs_def
  have hsc : s * c = 1 := Units.inv_mul c
  have hcs : (c : Lsq K Δ) * s = 1 := Units.mul_inv c
  have hss : star s = s * u := by
    have e2 : star s * star (c : Lsq K Δ) = 1 := by rw [← star_mul', hsc, star_one]
    linear_combination (-star s) * hsc + (u * s) * e2 + (star s * s) * hc
  have hM : u • star x = Matrix.adjugate x := by
    calc u • star x = star x * (u • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = star x * (x * Matrix.adjugate x) := by rw [Matrix.mul_adjugate]
      _ = Matrix.adjugate x := by rw [← Matrix.mul_assoc, hx, Matrix.one_mul]
  have r : ∀ i j, u * star (x j i) = Matrix.adjugate x i j := fun i j => by
    have e := congrFun (congrFun hM i) j
    simpa [Matrix.star_apply] using e
  have r00 := r 0 0
  have r01 := r 0 1
  have r10 := r 1 0
  have r11 := r 1 1
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at r00 r01 r10 r11
  let Y : GL (Fin 2) (Lsq K Δ) :=
    ⟨s • x, (c : Lsq K Δ) • star x,
      by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hxx, hsc, one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx, hcs, one_smul]⟩
  have hY : Y ∈ DX Δ := by
    show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) Y
      = MulEquiv.toMonoidHom (MulAut.conj (wJ Δ)⁻¹) Y
    apply Units.ext
    show (starRingEnd (Lsq K Δ)).mapMatrix (s • x) = !![0, -1; 1, 0] * (s • x) * !![0, 1; -1, 0]
    rw [conj_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show star (s * x 0 0) = s * x 1 1
      rw [star_mul']
      linear_combination (star (x 0 0)) * hss + s * r00
    · show star (s * x 0 1) = -(s * x 1 0)
      rw [star_mul']
      linear_combination (star (x 0 1)) * hss + s * r10
    · show star (s * x 1 0) = -(s * x 0 1)
      rw [star_mul']
      linear_combination (star (x 1 0)) * hss + s * r01
    · show star (s * x 1 1) = s * x 0 0
      rw [star_mul']
      linear_combination (star (x 1 1)) * hss + s * r11
  refine ⟨⟨Y, hY⟩, c, ?_, fun h => absurd h hx1, ?_⟩
  · show x = (c : Lsq K Δ) • (s • x)
    rw [smul_smul, hcs, one_smul]
  · intro _ _ _ h2' hΔ' hint
    have hui : IsIntegral O u := by
      rw [hu_def, Matrix.det_fin_two]
      exact ((hint 0 0).mul (hint 1 1)).sub ((hint 0 1).mul (hint 1 0))
    obtain ⟨hci1, hci2⟩ := hci h2' hΔ' hui
    rw [KD, Subgroup.mem_subgroupOf]
    exact mem_range Y (fun i j => hci2.mul (hint i j)) (fun i j => hci1.mul (int_star (hint j i)))
