import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open QuadraticAlgebra Matrix Loc

section Vec

variable {R : Type} [CommRing R] [StarRing R]

private theorem map_star_mulVec (M : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    M.map star *ᵥ star v = star (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

private theorem dot_unitary {X : Matrix (Fin 3) (Fin 3) R} (hX : star X * X = 1) (p q : Fin 3 → R) :
    ∑ i, (X *ᵥ p) i * star ((X *ᵥ q) i) = ∑ i, p i * star (q i) := by
  have h1 : (X *ᵥ p) ⬝ᵥ star (X *ᵥ q) = p ⬝ᵥ star q := by
    rw [dotProduct_comm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hX, Matrix.one_mulVec, dotProduct_comm]
  simpa [dotProduct] using h1

private theorem unitary_of_map (T : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (h : ∀ p q, ∑ i, T p i * star (T q i) = ∑ i, p i * star (q i)) :
    ∃ M ∈ Matrix.unitaryGroup (Fin 3) R, ∀ p, M *ᵥ p = T p := by
  classical
  have hM : ∀ p, LinearMap.toMatrix' T *ᵥ p = T p := fun p => by
    simpa using congrFun (congrArg DFunLike.coe (Matrix.toLin'_toMatrix' T)) p
  refine ⟨LinearMap.toMatrix' T, ?_, hM⟩
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [← hM, Matrix.mulVec_single_one] at this
  simpa [Matrix.mul_apply, Matrix.star_apply, mul_comm, Pi.single_apply, Matrix.one_apply, eq_comm, apply_ite (star : R → R)] using this

end Vec

section Shape

variable {K : Type} [Field K] {Δ τ : K}

private theorem semi_semi {d : EL Δ τ} (hd : d * sigL d = ofE Δ (ω : Etau K τ)) (x : Sp Δ τ) :
    semi d (semi d x) = (x.1, ofE Δ (ω : Etau K τ) * x.2) := by
  refine Prod.ext (by simp [semi]) ?_
  change d * sigL (d * sigL x.2) = _
  rw [sigL_mul, sigL_sigL, ← mul_assoc, hd]

private theorem omega_sub_inv (hτ : τ ^ 2 - 4 ≠ 0) : ∃ u : EL Δ τ, (ofE Δ (ω : Etau K τ) - 1) * u = 1 := by
  have h2 : 2 - τ ≠ 0 := fun h => hτ (by linear_combination (-(2 + τ)) * h)
  refine ⟨ofE Δ ⟨(τ - 1) / (2 - τ), -1 / (2 - τ)⟩, ?_⟩
  have e : ofE Δ (ω : Etau K τ) - 1 = ofE Δ ((ω : Etau K τ) - 1) := by
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [e, ← ofE_mul, ← ofE_one (Δ := Δ) (τ := τ)]
  congr 1
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring

private theorem eq_of_star_eq [CharZero K] {x : Lsq K Δ} (h : star x = x) : x = algebraMap K _ x.re := by
  have := congrArg QuadraticAlgebra.im h
  simp at this
  have h2 : (2 : K) * x.im = 0 := by linear_combination -this
  have h3 : x.im = 0 := by simpa using h2
  ext
  · simp
  · simpa using h3

private theorem alg_inj {x y : K} (h : algebraMap K (Lsq K Δ) x = algebraMap K _ y) : x = y := by
  simpa using congrArg QuadraticAlgebra.re h

private theorem isUnit_of_norm {d : EL Δ τ} (hd : d * sigL d = ofE Δ (ω : Etau K τ)) : IsUnit d := by
  have h : (ω : Etau K τ) * star ω = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    simp [QuadraticAlgebra.norm_def]
  have : d * (sigL d * ofE Δ (star (ω : Etau K τ))) = 1 := by
    rw [← mul_assoc, hd, ← ofE_mul, h, ofE_one]
  exact IsUnit.of_mul_eq_one _ this

private theorem shape [CharZero K] {c₁ c₂ t₁ t₂ : K} {d m n : EL Δ τ} (hτ : τ ^ 2 - 4 ≠ 0)
    (hd : d * sigL d = ofE Δ (ω : Etau K τ)) (hn : m * n = 1)
    (Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ) (hs : ∀ v, Q (semi d v) = semi d (Q v))
    (hf : ∀ v w, herm c₂ (t₂ • m) (Q v) (Q w) = herm c₁ (t₁ • m) v w) :
    ∃ (s : K) (z : Etau K τ), c₁ = c₂ * s ^ 2 ∧ t₁ = t₂ * QuadraticAlgebra.norm z := by
  set W : EL Δ τ := ofE Δ (ω : Etau K τ) with hW
  obtain ⟨u, hu⟩ := omega_sub_inv (Δ := Δ) hτ
  rw [← hW] at hu
  have hN : ∀ v, Q (v.1, W * v.2) = ((Q v).1, W * (Q v).2) := fun v => by
    rw [← semi_semi hd, hs, hs, semi_semi hd]

  have h1 : (Q (1, 0)).2 = 0 := by
    have := congrArg Prod.snd (hN (1, 0))
    simp only [mul_zero] at this
    have h' : (W - 1) * (Q (1, 0)).2 = 0 := by linear_combination -this
    calc (Q (1, 0)).2 = u * ((W - 1) * (Q (1, 0)).2) := by linear_combination (-(Q (1, 0)).2) * hu
      _ = 0 := by rw [h', mul_zero]

  have h2 : ∀ y : EL Δ τ, (Q (0, y)).1 = 0 := fun y => by
    have e : ((0 : Lsq K Δ), y) = (0, W * (u * y)) - (0, u * y) := by
      refine Prod.ext (by simp) ?_
      change y = W * (u * y) - u * y
      linear_combination (-y) * hu
    rw [e, map_sub, Prod.fst_sub, hN (0, u * y)]
    simp
  set e : EL Δ τ := (Q (0, 1)).2 with he
  have yy : ∀ y : EL Δ τ, y = y.re • (1 : EL Δ τ) + y.im • W := fun y => by
    ext <;> simp [hW, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h3 : ∀ y : EL Δ τ, (Q (0, y)).2 = e * y := fun y => by
    have ey : ((0 : Lsq K Δ), y) = y.re • ((0 : Lsq K Δ), (1 : EL Δ τ)) + y.im • (0, W * 1) := by
      refine Prod.ext (by simp) ?_
      simpa using yy y
    have hw := congrArg Prod.snd (hN (0, 1))
    rw [ey, map_add, map_smul, map_smul, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, hw]
    change y.re • e + y.im • (W * e) = _
    calc _ = e * (y.re • (1 : EL Δ τ) + y.im • W) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, mul_comm e W]
      _ = e * y := by rw [← yy]
  have hdu := isUnit_of_norm hd
  have hsig : sigL e = e := by
    have e1 : semi d ((0 : Lsq K Δ), (1 : EL Δ τ)) = (0, d) := Prod.ext (by simp [semi]) (by simp [semi, sigL_one])
    have h := congrArg Prod.snd (hs (0, 1))
    rw [e1, h3] at h
    change e * d = d * sigL e at h
    exact hdu.mul_left_cancel (by rw [← h, mul_comm])
  have hz : e = ofE Δ ⟨e.re.re, e.im.re⟩ := by
    have a1 : star e.re = e.re := congrArg QuadraticAlgebra.re hsig
    have a2 : star e.im = e.im := congrArg QuadraticAlgebra.im hsig
    ext1
    · exact eq_of_star_eq a1
    · exact eq_of_star_eq a2
  set z : Etau K τ := ⟨e.re.re, e.im.re⟩ with hzdef
  set a : Lsq K Δ := (Q (1, 0)).1 with ha
  have hQ1 : Q (1, 0) = (a, 0) := Prod.ext rfl h1
  have hstar : star a = a := by
    have e1 : semi d ((1 : Lsq K Δ), (0 : EL Δ τ)) = (1, 0) := Prod.ext (by simp [semi]) (by
      have s0 : sigL (0 : EL Δ τ) = 0 := by ext <;> simp [sigL]
      simp [semi, s0])
    have h := congrArg Prod.fst (hs (1, 0))
    rw [e1, hQ1] at h
    exact h.symm
  refine ⟨a.re, z, ?_, ?_⟩
  · have h := hf (1, 0) (1, 0)
    rw [hQ1] at h
    simp only [herm, mul_zero, zero_mul, map_zero, add_zero, star_one, mul_one, hstar] at h
    rw [eq_of_star_eq hstar] at h
    simp only [← map_mul] at h
    linear_combination -alg_inj h
  · have ht : ∀ k : K, QuadraticAlgebra.trace (k • (1 : EL Δ τ)) = 2 * algebraMap K (Lsq K Δ) k := fun k => by
      have : (k • (1 : EL Δ τ)).re = algebraMap K (Lsq K Δ) k := by
        simp [QuadraticAlgebra.re_one, Algebra.algebraMap_eq_smul_one]
      have h0 : (k • (1 : EL Δ τ)).im = 0 := by simp [QuadraticAlgebra.im_one]
      rw [QuadraticAlgebra.trace_def, this, h0, mul_zero, add_zero]
    have hee : e * star (sigL e) = QuadraticAlgebra.norm z • (1 : EL Δ τ) := by
      rw [hsig, hz, ← ofE_star, ← ofE_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.algebraMap_eq_smul_one]
    have h := hf (0, n) (0, 1)
    have q1 : Q (0, n) = (0, e * n) := Prod.ext (h2 n) (h3 n)
    have q2 : Q (0, 1) = (0, e) := Prod.ext (h2 1) (by rw [h3, mul_one])
    rw [q1, q2] at h
    simp only [herm, mul_zero, zero_mul, star_zero, zero_add, sigL_one, star_one, mul_one] at h
    have l1 : t₂ • m * (e * n) * star (sigL e) = (t₂ * QuadraticAlgebra.norm z) • (1 : EL Δ τ) := by
      rw [mul_smul, ← hee]
      simp only [smul_mul_assoc]
      congr 1
      linear_combination (e * star (sigL e)) * hn
    have l2 : t₁ • m * n = t₁ • (1 : EL Δ τ) := by rw [smul_mul_assoc, hn]
    rw [l1, l2, ht, ht] at h
    have h4 : 2 * (t₂ * QuadraticAlgebra.norm z) = 2 * t₁ := alg_inj (Δ := Δ) (by
      rw [map_mul (algebraMap K (Lsq K Δ)) 2, map_mul (algebraMap K (Lsq K Δ)) 2, map_ofNat]
      exact h)
    exact (mul_left_cancel₀ two_ne_zero h4).symm

end Shape

section Main

variable {K : Type} [Field K] {Δ τ : K}

private theorem star_alg (r : K) : star (algebraMap K (Lsq K Δ) r) = algebraMap K _ r := by
  ext <;> simp

private theorem ofE_norm (z : Etau K τ) :
    ofE Δ z * star (ofE Δ z) = QuadraticAlgebra.norm z • (1 : EL Δ τ) := by
  rw [← ofE_star, ← ofE_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.algebraMap_eq_smul_one]

private def scaleMap (r : K) (y : EL Δ τ) : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ where
  toFun x := (algebraMap K _ r * x.1, y * x.2)
  map_add' a b := by simp [mul_add]
  map_smul' a b := Prod.ext (by simp; ring) (mul_smul_comm _ _ _)

private theorem fwd {c c' : K} {d m m' : EL Δ τ} {δ δ' x : U3 Δ} {ι ι' P P'}
    (h : Models c d m δ ι P) (h' : Models c' d m' δ' ι' P') (hx : δ' = x⁻¹ * δ * theta Δ x) :
    ∃ Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ, (∀ v, Q (semi d v) = semi d (Q v)) ∧
      ∀ v w, herm c' m' (Q v) (Q w) = herm c m v w := by
  set X : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) with hX
  have hXu : star X * X = 1 := (Matrix.mem_unitaryGroup_iff').1 (x⁻¹ : U3 Δ).2
  let Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ := P'.symm.toLinearMap ∘ₗ X.mulVecLin ∘ₗ P.toLinearMap
  have hQ : ∀ v, P' (Q v) = X *ᵥ P v := fun v => by simp [Q]
  refine ⟨Q, fun v => P'.injective ?_, fun v w => ?_⟩
  · rw [hQ, h'.semi, hQ, h.semi, hx]
    have e : ((x⁻¹ * δ * theta Δ x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
        X * (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := rfl
    have e2 : (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * X = 1 := by
      rw [hX]; exact congrArg Subtype.val (mul_inv_cancel x)
    rw [e, ← Matrix.mulVec_mulVec, map_star_mulVec, Matrix.mulVec_mulVec _ (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)), e2,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  · rw [h'.form, h.form, hQ, hQ]
    exact dot_unitary hXu _ _

private theorem bwd {c c' : K} {d m m' : EL Δ τ} {δ δ' : U3 Δ} {ι ι' P P'}
    (h : Models c d m δ ι P) (h' : Models c' d m' δ' ι' P')
    (Q : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ) (hs : ∀ v, Q (semi d v) = semi d (Q v))
    (hf : ∀ v w, herm c m (Q v) (Q w) = herm c' m' v w) :
    ∃ x, δ' = x⁻¹ * δ * theta Δ x := by
  obtain ⟨M, hM, hMv⟩ := unitary_of_map (P.toLinearMap ∘ₗ Q ∘ₗ P'.symm.toLinearMap) (fun p q => by
    have e := hf (P'.symm p) (P'.symm q)
    rw [h.form, h'.form] at e
    simpa using e)
  have hMP : ∀ v, M *ᵥ P' v = P (Q v) := fun v => by simp [hMv]
  refine ⟨⟨M, hM⟩, ?_⟩
  have key : (⟨M, hM⟩ : U3 Δ) * δ' = δ * theta Δ ⟨M, hM⟩ := by
    apply Subtype.ext
    change M * (δ' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * M.map star
    have hall : ∀ u, (M * (δ' : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) *ᵥ u =
        ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * M.map star) *ᵥ u := fun u => by
      obtain ⟨v, rfl⟩ : ∃ v, u = star (P' v) := ⟨P'.symm (star u), by simp⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← h'.semi, hMP, hs, h.semi, map_star_mulVec, hMP]
    exact Matrix.ext_of_mulVec_single fun i => hall _
  rw [mul_assoc, ← key]
  simp

end Main

theorem conjG : ConjG := by
  intro K _ _ Δ τ d m hΔ hD c c' t t' δ δ' ι ι' P P' h h'
  obtain ⟨n, hn⟩ : ∃ n, m * n = 1 := hD.m_unit.exists_right_inv
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨Q, q1, q2⟩ := fwd h h' hx
    obtain ⟨s, z, e1, e2⟩ := shape hD.reg hD.d_norm hn Q q1 q2
    have hs0 : s ≠ 0 := fun h0 => c.ne_zero (by rw [e1, h0]; simp)
    have hN0 : QuadraticAlgebra.norm z ≠ 0 := fun h0 => t.ne_zero (by rw [e2, h0, mul_zero])
    have hzu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (isUnit_iff_ne_zero.2 hN0)
    refine ⟨⟨Units.mk0 s⁻¹ (inv_ne_zero hs0), Units.ext ?_⟩, hzu.unit⁻¹, ?_⟩
    · simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
      rw [e1]
      have := c'.ne_zero
      field_simp
    · rw [map_inv]
      apply Units.ext
      simp only [Units.val_inv_eq_inv_val, Units.coe_map, IsUnit.unit_spec, Units.val_div_eq_div_val, MonoidHom.coe_coe]
      rw [e2]
      have := t'.ne_zero
      field_simp
  · rintro ⟨⟨r, hr⟩, ⟨z, hz⟩⟩
    have C : (c' : K) = c * r * r := by
      have := congrArg Units.val hr
      simp only [Units.val_div_eq_div_val, Units.val_mul] at this
      rw [mul_assoc, ← this]
      have := c.ne_zero
      field_simp
    have T : (t' : K) = t * QuadraticAlgebra.norm (z : Etau K τ) := by
      have := congrArg Units.val hz
      simp only [Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe] at this
      rw [this]
      have := t.ne_zero
      field_simp
    refine bwd h h' (scaleMap r (ofE Δ z)) (fun v => Prod.ext ?_ ?_) (fun v w => ?_)
    · change algebraMap K (Lsq K Δ) r * star v.1 = star (algebraMap K (Lsq K Δ) r * v.1)
      rw [star_mul', star_alg]
    · change ofE Δ (z : Etau K τ) * (d * sigL v.2) = d * sigL (ofE Δ (z : Etau K τ) * v.2)
      rw [sigL_mul, sigL_ofE]
      ring
    · change herm (c : K) ((t : K) • m) (algebraMap K (Lsq K Δ) r * v.1, ofE Δ (z : Etau K τ) * v.2)
        (algebraMap K (Lsq K Δ) r * w.1, ofE Δ (z : Etau K τ) * w.2) = _
      simp only [herm, sigL_mul, sigL_ofE, star_mul', star_alg]
      congr 1
      · rw [C]
        simp only [map_mul]
        ring
      · congr 1
        simp only [smul_mul_assoc]
        rw [show m * (ofE Δ (z : Etau K τ) * v.2) * (star (ofE Δ (z : Etau K τ)) * star (sigL w.2)) =
          (ofE Δ (z : Etau K τ) * star (ofE Δ (z : Etau K τ))) * (m * v.2 * star (sigL w.2)) by ring,
          ofE_norm, smul_mul_assoc, one_mul, smul_smul, ← T]

end UpperTheory.V.Z.Sym.Glob
