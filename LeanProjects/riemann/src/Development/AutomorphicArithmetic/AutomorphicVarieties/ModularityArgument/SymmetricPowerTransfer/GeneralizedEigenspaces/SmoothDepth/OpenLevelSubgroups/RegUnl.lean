import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem ne_of_div {G : Type*} [CommGroup G] {p x y : G} (h₁ : x / y ≠ 1) (h₂ : x / y ≠ p) :
    x ≠ y ∧ x ≠ y * p :=
  ⟨fun h => h₁ (by rw [h, div_self']), fun h => h₂ (by rw [h, mul_div_cancel_left])⟩

private theorem inv_ne_of {G : Type*} [CommGroup G] {p x : G} (h : x ≠ p⁻¹) : x⁻¹ ≠ p :=
  fun e => h (by rw [← e, inv_inv])

private theorem triple {G : Type*} [CommGroup G] {a p : G} (h1 : a ≠ 1) (hp : a ≠ p) (hm : a ≠ p⁻¹)
    (s1 : a ^ 2 ≠ 1) (sp : a ^ 2 ≠ p) (sm : a ^ 2 ≠ p⁻¹) (i i' : Fin 3) (hne : i ≠ i') :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ ![a, 1, a⁻¹] i' ∧ (![a, 1, a⁻¹] : Fin 3 → G) i ≠ ![a, 1, a⁻¹] i' * p := by
  have e02 : a / a⁻¹ = a ^ 2 := by rw [div_inv_eq_mul, pow_two]
  have e20 : a⁻¹ / a = (a ^ 2)⁻¹ := by rw [← e02, inv_div]
  fin_cases i <;> fin_cases i' <;> first
    | exact absurd rfl hne
    | (apply ne_of_div <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, div_one, one_div, inv_inv, e02, e20]
       <;> first
         | exact h1 | exact hp | exact s1 | exact sp
         | exact inv_ne_one.2 h1 | exact inv_ne_one.2 s1
         | exact inv_ne_of hm | exact inv_ne_of sm)

theorem UpperTheory.V.Z.Sym.Al.regUnl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : kˣ →* ℂˣ), Reg a →
        ((∀ i, ∀ u ∈ Hi.Uo k, (![a, 1, a⁻¹] : Fin 3 → kˣ →* ℂˣ) i u = 1) ∧
          ∀ i i' : Fin 3, i ≠ i' → ![a, 1, a⁻¹] i ≠ ![a, 1, a⁻¹] i' ∧ ![a, 1, a⁻¹] i ≠ ![a, 1, a⁻¹] i' * absPow k 1) ∧
        ∀ ψ : Fin 2 → kˣ →* ℂˣ, ψ 0 / ψ 1 = a ^ 2 → ∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow k 1 := by
  intro k _ _ _ _ a ⟨hu, hr⟩
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  have s1 : a ^ 2 ≠ 1 := by
    have := hr 0 (by norm_num)
    simpa using this
  have sp : a ^ 2 ≠ absPow k 1 := by
    have := hr 1 (by norm_num)
    simpa using this
  have sm : a ^ 2 ≠ (absPow k 1)⁻¹ := by
    have := hr (-1) (by norm_num)
    simpa [absPow_neg] using this
  have h1 : a ≠ 1 := fun h => s1 (by rw [h, one_pow])
  have hp : a ≠ absPow k 1 := fun h => hr 2 (by norm_num) (by
    rw [h]; push_cast; exact two.symm)
  have hm : a ≠ (absPow k 1)⁻¹ := fun h => hr (-2) (by norm_num) (by
    rw [h]; push_cast; rw [absPow_neg, two, inv_pow])
  refine ⟨⟨fun i u hu' => ?_, triple h1 hp hm s1 sp sm⟩, fun ψ hψ i i' hne => ?_⟩
  · fin_cases i
    · exact hu u hu'
    · rfl
    · show (a u)⁻¹ = 1
      rw [hu u hu', inv_one]
  · have e : ψ 1 / ψ 0 = (a ^ 2)⁻¹ := by rw [← hψ, inv_div]
    fin_cases i <;> fin_cases i'
    · exact absurd rfl hne
    · apply ne_of_div
      · exact hψ ▸ s1
      · exact hψ ▸ sp
    · apply ne_of_div
      · exact e ▸ inv_ne_one.2 s1
      · exact e ▸ inv_ne_of sm
    · exact absurd rfl hne
