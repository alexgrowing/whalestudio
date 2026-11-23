import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X] {m : ℕ}

def linW (w : (X × X) →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := w.sum fun p k => k * β p.1 p.2
  map_add' β γ := by
    simp only [LinearMap.add_apply, mul_add]
    exact Finsupp.sum_add
  map_smul' c β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    exact Finsupp.sum_congr fun _ _ => by ring

def evalW (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := w.sum fun p k => (k : ℝ) * B p.1 p.2

theorem linW_apply (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : linW w β = w.sum fun p k => k * β p.1 p.2 := rfl

theorem evalW_toReal (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : evalW w (toReal β) = linW w β := by
  simp [evalW, linW_apply, Finsupp.sum]

theorem evalW_add (w : (X × X) →₀ ℤ) (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (B + B') = evalW w B + evalW w B' := by
  simp only [evalW, LinearMap.add_apply, mul_add]
  exact Finsupp.sum_add

theorem evalW_smul (w : (X × X) →₀ ℤ) (t : ℝ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (t • B) = t * evalW w B := by
  simp only [evalW, LinearMap.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

def evalWL (w : (X × X) →₀ ℤ) : (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) →ₗ[ℝ] ℝ where
  toFun := evalW w
  map_add' := evalW_add w
  map_smul' t B := evalW_smul w t B

theorem evalW_sum (w : (X × X) →₀ ℤ) (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    evalW w (∑ i, t i • toReal (u i)) = ∑ i, t i * linW w (u i) := by
  have := map_sum (evalWL w) (fun i => t i • toReal (u i)) Finset.univ
  simp only [evalWL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [evalW_smul, evalW_toReal]

def rcone (u : Fin m → LinearMap.BilinForm ℤ X) : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • toReal (u i)}

def StrictWith {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) [Module O X] [Module.Finite O X] (N : ℕ)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (u : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ i, (ℓ (u i) : ℝ) = N * φ.evalZ (u i)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i

theorem isStrict_iff {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} [Module O X] [Module.Finite O X]
    {u : Fin m → LinearMap.BilinForm ℤ X} : IsStrict bar φ u ↔ ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧
      StrictWith bar φ N ℓ u := Iff.rfl

def kDen (N n : ℕ) (𝓜 : Finset ℕ) : ℕ := N * ∏ M ∈ 𝓜, (M + 1) ^ n

def lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) : (X × X) →₀ ℤ :=
  (D : ℤ) • ((∏ M ∈ 𝓜, ((M : ℤ) + 1) ^ n) • w +
    ∑ M ∈ 𝓜, ((N : ℤ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℤ) + 1) ^ n) • ∑ y, Finsupp.single (r (a M y), r (a M y)) 1)

example : linW (Finsupp.single ((1 : ℤ), (1 : ℤ)) 1) mulForm = 1 := by simp [linW_apply]

example : toReal mulForm ∈ rcone ![mulForm] := ⟨![1], fun i => by fin_cases i; simp, by simp⟩

end GlobalTheory.PolCell
