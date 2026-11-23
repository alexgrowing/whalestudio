import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem star_alg {K : Type} [Field K] {Δ : K} (x : K) :
    star (algebraMap K (Lsq K Δ) x) = algebraMap K (Lsq K Δ) x := by
  ext <;> simp

private theorem sigL_mul' {K : Type} [Field K] {Δ τ : K} (a b : EL Δ τ) :
    sigL (a * b) = sigL a * sigL b := by
  ext <;> simp [sigL, star_alg] <;> ring

private theorem sigL_one' {K : Type} [Field K] {Δ τ : K} : sigL (1 : EL Δ τ) = 1 := by
  apply QuadraticAlgebra.ext
  · exact star_one (Lsq K Δ)
  · exact star_zero (Lsq K Δ)

private theorem fixed_scalar {K : Type} [Field K] [CharZero K] {Δ τ : K} (r : EL Δ τ)
    (h1 : sigL r = r) (h2 : star r = r) : ∃ p : K, ∀ x : EL Δ τ, r * x = p • x := by
  have z : ∀ y : K, -y = y → y = 0 := fun y h => by
    have h' : (2 : K) * y = 0 := by linear_combination -h
    simpa using h'
  have e1 := congrArg (fun w : EL Δ τ => w.re.im) h1
  have e2 := congrArg (fun w : EL Δ τ => w.im.re) h2
  have e3 := congrArg (fun w : EL Δ τ => w.im.im) h2
  simp [sigL] at e1 e2 e3
  have hr : algebraMap K (EL Δ τ) r.re.re = r := by
    rw [show algebraMap K (EL Δ τ) r.re.re = ⟨⟨r.re.re, 0⟩, 0⟩ from rfl]
    ext <;> simp [z _ e1, z _ e2, z _ e3]
  refine ⟨r.re.re, fun x => ?_⟩
  calc r * x = algebraMap K (EL Δ τ) r.re.re * x := by rw [hr]
    _ = r.re.re • x := (Algebra.smul_def _ _).symm

theorem UpperTheory.hermitian_datum_unique_up_to_scalar :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c c' : K) (d m m' : EL Δ τ), IsDat c d m → IsDat c' d m' → ∃ t : Kˣ, m' = (t : K) • m := by
  intro K _ _ Δ τ c c' d m m' hm hm'
  obtain ⟨u, hu⟩ := hm.m_unit
  set r : EL Δ τ := m' * ↑u⁻¹ with hrdef
  have hrm : r * m = m' := by
    rw [hrdef, ← hu, mul_assoc, Units.inv_mul, mul_one]
  have hsu : IsUnit (sigL m) := by
    refine IsUnit.of_mul_eq_one (sigL (↑u⁻¹ : EL Δ τ)) ?_
    rw [← sigL_mul', ← hu, Units.mul_inv, sigL_one']
  have hs : sigL r = r := by
    have e : sigL r * sigL m = r * sigL m := by
      rw [← sigL_mul', hrm, hm'.m_sig, hm.m_sig, ← mul_assoc, ← mul_assoc, hrm]
    exact hsu.mul_left_injective e
  have hsm : star m = sigL m := by
    conv_lhs => rw [← hm.m_star]
    exact star_star _
  have hsm' : star m' = sigL m' := by
    conv_lhs => rw [← hm'.m_star]
    exact star_star _
  have hst : star r = r := by
    have e : star r * sigL m = r * sigL m :=
      calc star r * sigL m = star r * star m := by rw [hsm]
        _ = star (r * m) := (star_mul' r m).symm
        _ = star m' := by rw [hrm]
        _ = sigL m' := hsm'
        _ = sigL r * sigL m := by rw [← sigL_mul', hrm]
        _ = r * sigL m := by rw [hs]
    exact hsu.mul_left_injective e
  obtain ⟨p, hp⟩ := fixed_scalar r hs hst
  have hm'p : m' = p • m := by rw [← hp, hrm]
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hm'p
    exact hm'.m_unit.ne_zero hm'p
  exact ⟨Units.mk0 p hp0, hm'p⟩
