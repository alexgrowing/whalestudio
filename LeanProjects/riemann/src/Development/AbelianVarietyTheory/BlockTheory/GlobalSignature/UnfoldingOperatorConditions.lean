import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnfoldingOperatorConditions

open Formalism.L2.Col Formalism.L2.Col.Loc

variable {E : Type} [Field E] [NumberField E]

def IsLatAt (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  ∃ g : (Fin N → E) ≃ₗ[E] (Fin N → E), ∀ v, v ∈ Λ ↔ ∀ l, IntAt P (g.symm v l)

def aux (E : Type) [Field E] (n c i : ℕ) : Fin (n + c) → E := eN E (n + c) (n + (i - 1))

def unfoldedCoordinate {E : Type} [Field E] (n c i : ℕ) (v : Fin (n + c) → E) : E := atN v (n + (i - 1))

def IsNormalForm (P : HeightOneSpectrum (𝓞 E)) {n' c' : ℕ} (L' : Submodule (𝓞 E) (Fin n' → E)) (e : ℕ → ℤ) (z : Fin n' → E)
    (Λ' : Submodule (𝓞 E) (Fin (n' + c') → E)) : Prop :=
  ∀ v, v ∈ Λ' ↔ ∃ l ∈ L', ∃ s : ℕ → E, (∀ i, IntAt P (s i)) ∧
    v = inX E n' c' l + (s 1 * (qOf P : E) ^ e 1) • (aux E n' c' 1 + inX E n' c' z) +
      ∑ i ∈ Finset.Icc 2 c', (s i * (qOf P : E) ^ e i) • aux E n' c' i

def CoordinateImageOfLattice (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ} (Λ : Submodule (𝓞 E) (Fin (n + c) → E)) (i : ℕ) (m : ℤ) : Prop :=
  ∀ s : E, (∃ v ∈ Λ, v ∈ Ufl E n c i ∧ unfoldedCoordinate n c i v = s) ↔ ∃ u : E, IntAt P u ∧ s = (qOf P : E) ^ m * u

structure CondO {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (D : ℕ) : Prop where
  add : ∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → psi (x + y) = psi x * psi y
  int : ∀ x : E, IntAt P x → psi x = 1
  ne : psi ((qOf P : E)⁻¹) ≠ 1

def SuppIn {K : Type} [Field K] {N' N : ℕ} (Λ' : Submodule (𝓞 E) (Fin N' → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (Ψ : SF E K N' N) : Prop :=
  ∀ x, Ψ x ≠ 0 → ∀ v ∈ Λ', x v ∈ Λ

def InvUnder {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) {N' N : ℕ} (Λ' : Submodule (𝓞 E) (Fin N' → E))
    (Λ : Submodule (𝓞 E) (Fin N → E)) (Ψ : SF E K N' N) : Prop :=
  ∀ y : (Fin N' → E) →ₗ[E] (Fin N → E), (∀ v ∈ Λ', y v ∈ Λ) → ∀ x, Ψ (x + (qOf P : E) • y) = Ψ x

def unfoldingOperatorAtPlace {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (A B : ℕ) {n' n c : ℕ}
    (Ψ : SF E K (n' + (c + 1)) (n + c)) : SF E K n' n :=
  Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Ψ

def Concl (P : HeightOneSpectrum (𝓞 E)) {n' n c : ℕ} (e' : ℕ → ℤ) (z : Fin n' → E) (Λ : Submodule (𝓞 E) (Fin (n + c) → E))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : Prop :=
  (∃ e : ℕ → ℤ, ∀ i, 1 ≤ i → i ≤ c → CoordinateImageOfLattice P Λ i (e i) ∧ e' (i + 1) - 1 ≤ e i ∧ e i ≤ e' i) ∧
    ((qOf P : E) ^ e' 1) • (aux E n c 1 + inX E n c (xj z)) ∈ Λ

def UnfoldedBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)),
    ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
  ∀ (n' n c : ℕ), 1 ≤ c →
  ∀ (L' : Submodule (𝓞 E) (Fin n' → E)) (e' : ℕ → ℤ) (z : Fin n' → E) (Λ' : Submodule (𝓞 E) (Fin (n' + (c + 1)) → E))
    (Λ : Submodule (𝓞 E) (Fin (n + c) → E)),
    IsLatAt P L' → IsNormalForm P L' e' z Λ' → IsLatAt P Λ →
  ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B →
  ∀ (psi : E → K) (D : ℕ) (Ψ : SF E K (n' + (c + 1)) (n + c)) (xj : (Fin n' → E) →ₗ[E] (Fin n → E)),
    CondO P psi D → SuppIn Λ' Λ Ψ → InvUnder P Λ' Λ Ψ →
    (∀ t : FC n' (c + 1) n c → E, Ψ (xx1 xj t) ≠ 0 → IntAt P ((qOf P : E) ^ D * chArg (xx1 xj t))) →
    unfoldingOperatorAtPlace P psi A B Ψ xj ≠ 0 → Concl P e' z Λ xj

theorem condO_of_ok {X : Formalism.L2.Col.Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {cst : LocCst X SB} (h : cst.Ok) (P : SB) :
    CondO P.1 (cst.psi P) (cst.D P) :=
  ⟨h.psi_add P, h.psi_int P, h.psi_ne P⟩

theorem condO_of_addChar {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (ψ : AddChar E K)
    (h1 : ∀ x, IntAt P x → ψ x = 1) (h2 : ψ ((qOf P : E)⁻¹) ≠ 1) (D : ℕ) : CondO P ψ D :=
  ⟨fun x y _ _ => ψ.map_add_eq_mul x y, h1, h2⟩

theorem exists_condO (P : HeightOneSpectrum (𝓞 E)) : ∃ psi : E → ℂ, CondO P psi 1 := by
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have h1 : (1 : 𝓞 E ⧸ P.asIdeal) ≠ 0 := one_ne_zero
  obtain ⟨χ, hχ⟩ := (AddChar.exists_apply_ne_zero (α := 𝓞 E ⧸ P.asIdeal)).2 h1
  have hq : (qOf P : E) ≠ 0 := by
    have : qOf P ≠ 0 := by
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  have hqc : (qOf P : E) = algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E) := by simp
  refine ⟨fun x => χ (redP P ((qOf P : E) * x)), fun x y hx hy => ?_, fun x hx => ?_, ?_⟩
  · rw [pow_one] at hx hy
    simp only [mul_add, reduction_add hx hy, AddChar.map_add_eq_mul]
  · have h0 : Ideal.Quotient.mk P.asIdeal ((qOf P : ℕ) : 𝓞 E) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
    show χ (redP P ((qOf P : E) * x)) = 1
    rw [hqc, reduction_mul (IntAt.coe P _) hx, reduction_coe, h0, zero_mul, AddChar.map_zero_eq_one]
  · show χ (redP P ((qOf P : E) * (qOf P : E)⁻¹)) ≠ 1
    rw [mul_inv_cancel₀ hq, ← map_one (algebraMap (𝓞 E) E), reduction_coe, map_one]
    exact hχ

example : aux ℚ 2 3 1 = ![0, 0, 1, 0, 0] := by
  funext l; fin_cases l <;> simp [aux, eN]

example : unfoldedCoordinate 2 3 2 (aux ℚ 2 3 2) = 1 := by
  simp [unfoldedCoordinate, aux, atN, eN]

end GlobalTheory.IndefiniteRowSideFullHecke.UnfoldingOperatorConditions
