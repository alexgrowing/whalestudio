import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ShFam

namespace GlobalTheory.TorRef

section PosPart

variable {O : Type} [CommRing O]

def posPart (φ : InvFun O) : InvFun O where
  toFun n B := max (φ.toFun n B) 0
  inv n m r hr B := by rw [φ.inv n m r hr]
  zero B := by simp [φ.zero]

variable (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem posPart_eval (B : X → X → ℝ) : (posPart φ).eval X B = max (φ.eval X B) 0 := rfl

theorem posPart_evalR (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalR (posPart φ) B = max (evalR φ B) 0 := rfl

theorem posPart_evalZ (β : LinearMap.BilinForm ℤ X) : (posPart φ).evalZ β = max (φ.evalZ β) 0 := rfl

variable {φ}

theorem isStrict_congr (bar : O → O) {φ₁ φ₂ : InvFun O} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (he : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → φ₁.evalZ β = φ₂.evalZ β)
    (hm : ∀ i, γ i ∈ balForms bar X) (hn : ∀ i y, 0 ≤ γ i y y) (h : GlobalTheory.PolFan.IsStrict bar φ₁ γ) : GlobalTheory.PolFan.IsStrict bar φ₂ γ := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h
  refine ⟨N, ℓ, hN, fun i => by rw [← he _ (hm i) (hn i)]; exact h1 i, fun β hβ hp => ?_, fun β hβ hp hq => ?_⟩
  · rw [← he β hβ hp]; exact h2 β hβ hp
  · rw [← he β hβ hp] at hq; exact h3 β hβ hp hq

end PosPart

section Fan

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {φ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem evalZ_posPart_eq (hF : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) : (posPart φ).evalZ β = φ.evalZ β := by
  rw [posPart_evalZ, max_eq_left (hF.evalZ_nonneg hβ hp)]

theorem evalR_posPart_eq (hF : IsPolFanOn bar φ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X) :
    evalR (posPart φ) B = evalR φ B := by
  rw [posPart_evalR, max_eq_left (hF.evalR_nonneg hB)]

theorem linearOn_posPart_iff (hF : IsPolFanOn bar φ X) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hm : ∀ i, γ i ∈ balForms bar X) (hn : ∀ i y, 0 ≤ γ i y y) : (posPart φ).LinearOn γ ↔ φ.LinearOn γ := by
  rw [linearOn_iff, linearOn_iff]
  refine forall₂_congr fun c hc => ?_
  rw [evalR_posPart_eq hF (ConeSub.sum_smul_toReal_mem_psdCone O bar X m γ c hm hn hc)]
  simp only [evalZ_posPart_eq hF (hm _) (hn _)]

theorem isCone_posPart_iff (hF : IsPolFanOn bar φ X) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} :
    IsCone bar (posPart φ) γ ↔ IsCone bar φ γ := by
  have he : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (posPart φ).evalZ β = φ.evalZ β :=
    fun β hβ hp => evalZ_posPart_eq hF hβ hp
  constructor
  · intro h
    exact ⟨h.mem, h.nonneg, h.basis, (linearOn_posPart_iff hF h.mem h.nonneg).1 h.linear,
      isStrict_congr bar he h.mem h.nonneg h.strict⟩
  · intro h
    exact ⟨h.mem, h.nonneg, h.basis, (linearOn_posPart_iff hF h.mem h.nonneg).2 h.linear,
      isStrict_congr bar (fun β hβ hp => (he β hβ hp).symm) h.mem h.nonneg h.strict⟩

theorem isPolFanOn_posPart (hF : IsPolFanOn bar φ X) : IsPolFanOn bar (posPart φ) X where
  homog B hB t ht := by
    rw [evalR_posPart_eq hF hB, evalR_posPart_eq hF (smul_mem_psdCone hB ht)]
    exact hF.homog B hB t ht
  superadd B hB B' hB' := by
    rw [evalR_posPart_eq hF hB, evalR_posPart_eq hF hB', posPart_evalR]
    exact (hF.superadd B hB B' hB').trans (le_max_left _ _)
  integral β hβ hp := by rw [evalZ_posPart_eq hF hβ hp]; exact hF.integral β hβ hp
  pos β hβ hp h0 := by rw [evalZ_posPart_eq hF hβ hp]; exact hF.pos β hβ hp h0
  face m m' γ s hγ := (isCone_posPart_iff hF).2 (hF.face m m' γ s ((isCone_posPart_iff hF).1 hγ))
  cover B hB := by
    obtain ⟨m, γ, c, hγ, hc, e⟩ := hF.cover B hB
    exact ⟨m, γ, c, (isCone_posPart_iff hF).2 hγ, hc, e⟩
  finite := by
    obtain ⟨S, hS, h⟩ := hF.finite
    exact ⟨S, hS, fun m γ hγ => h m γ ((isCone_posPart_iff hF).1 hγ)⟩

end Fan

theorem refineSt : RefineSt := by
  intro E _ _ _ H q g φs 𝒩 hg hφs h𝒩
  obtain ⟨φ', k1, k2, k3, k4, k5, k6⟩ :=
    exists_fine_invariant_fan H hφs hg 𝒩 fun N hN => h𝒩 N hN
  refine ⟨posPart φ', fun X _ _ _ _ hX => isPolFanOn_posPart (k1 X hX), fun X _ _ _ _ hX m γ hγ =>
    k2 X hX m γ ((isCone_posPart_iff (k1 X hX)).1 hγ), fun σ hσ n B => ?_, fun X _ _ _ _ be hbe hp => ?_,
    ⟨fun n k B => ?_, fun n B => le_max_right _ _⟩, fun X _ _ _ _ hX m γ hγ => ?_⟩
  · show max _ 0 = max _ 0
    rw [k3 σ hσ n B]
  · rw [posPart_evalZ]
    exact lt_max_of_lt_left (k4 X be hbe hp)
  · show max _ 0 = (k : ℝ) * max _ 0
    rw [k5 n k B, mul_max_of_nonneg _ _ (Nat.cast_nonneg k), mul_zero]
  · exact k6 X hX m γ ((isCone_posPart_iff (k1 X hX)).1 hγ)

end GlobalTheory.TorRef
