import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

def kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    (a : S → w.valuationSubring) (r : ℕ) (g : S → (Fin r → C) →ₗ[C] W) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {f | f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0}
  zero_mem' := ⟨zero_mem _, fun s => by simp⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun s => by simp [hx.2 s, hy.2 s]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun s => by
    have e : (c • f) s = (c : C) • f s := rfl
    rw [e, map_smul, hf.2 s, smul_zero]⟩

theorem mem_kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    {a : S → w.valuationSubring} {r : ℕ} {g : S → (Fin r → C) →ₗ[C] W} {f : S → Fin r → C} :
    f ∈ kerFil a r g ↔ f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0 := Iff.rfl

def eigCoord {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) : (Fin N → C) →ₗ[C] M :=
  Fintype.linearCombination C (fun j => HT.eigProj ρ s (t j))

theorem eigCoord_apply {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) (y : Fin N → C) :
    eigCoord ρ t s y = ∑ j, y j • HT.eigProj ρ s (t j) := by
  simp [eigCoord, Fintype.linearCombination_apply]

def TargetO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (ν : Valuation C ℝ≥0)
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ),
    (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) →
    (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ ν.valuationSubring) →
    Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) →
    (∀ a, bar (bar a) = a) →
    ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module ν.valuationSubring W]
      [IsScalarTower ν.valuationSubring C W] [FiniteDimensional C W]
      (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
      (HV : Submodule ν.valuationSubring (W × Module.Dual C W)) (Lie : Submodule ν.valuationSubring W)
      (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W)
      (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C),
      (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) →
      HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars ν.valuationSubring) = Lie →
      (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap ν.valuationSubring C).range) →
      HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) →
      LinearIndependent C v → Submodule.span ν.valuationSubring (Set.range v) = HT.eigSub ρ σ Lie →
      LinearIndependent C w → Submodule.span ν.valuationSubring (Set.range w) = HT.eigSub ρ σ' Lie →
      IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) →
      Submodule.span ν.valuationSubring (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV →
      ∃ ε : (ν.valuationSubring)ˣ, A.det = algebraMap ν.valuationSubring C ε * γ

end GlobalTheory.CompanionTheory.Ar.Flat.ExG
