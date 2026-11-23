import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finU_mul_infU_comm (k y : UA E n) (hk : k ∈ finU E n) (hy : y ∈ infU E n) : k * y = y * k := by
  have hk' : Matrix.GeneralLinearGroup.map (pInf E) (k : GA E n) = 1 := MonoidHom.mem_ker.1 hk
  have hy' : Matrix.GeneralLinearGroup.map (pFin E) (y : GA E n) = 1 := MonoidHom.mem_ker.1 hy
  apply Subtype.ext
  apply ga_ext
  · simp only [Subgroup.coe_mul, map_mul, hk', one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, hy', one_mul, mul_one]

def levelForms (L : Subgroup (finU E n)) (C : Submodule ℂ (infU E n → ℂ)) : Submodule ℂ (UA E n → ℂ) where
  carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
    ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, a1 γ hγ g, b1 γ hγ g]
    · simp only [Pi.add_apply, a2 k hk g, b2 k hk g]
    · exact C.add_mem (a3 g) (b3 g)
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => C.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨a1, a2, a3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, a1 γ hγ g]
    · simp only [Pi.smul_apply, a2 k hk g]
    · exact C.smul_mem c (a3 g)

end GlobalTheory.UnitaryBC

open GlobalTheory.UnitaryBC in

theorem GlobalTheory.UnitaryBC.finiteDimensional_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  intro E _ _ _ n hS L hL C _
  obtain ⟨S, hS⟩ := hS L hL
  let M := levelForms L C
  have hle : Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} ≤ M :=
    Submodule.span_le.2 fun ψ h => h

  have key : ∀ ψ ∈ M, ∀ g, ∃ s ∈ S, ∃ y ∈ infU E n, ψ g = ψ (s * y) := by
    rintro ψ ⟨h1, h2, -⟩ g
    obtain ⟨γ, hγ, s, hs, k, hk, y, hy, rfl⟩ := hS g
    refine ⟨s, hs, y, hy, ?_⟩
    rw [mul_assoc, mul_assoc, h1 γ hγ, finU_mul_infU_comm _ _ k.2 hy, ← mul_assoc, h2 k hk]
  let f : M →ₗ[ℂ] (S → C) :=
    { toFun := fun ψ s => ⟨fun y : infU E n => ψ.1 ((s : UA E n) * (y : UA E n)), ψ.2.2.2 s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext g
    obtain ⟨s, hs, y, hy, e⟩ := key (a.1 - b.1) (M.sub_mem a.2 b.2) g
    have := congrArg (fun F : S → C => ((F ⟨s, hs⟩ : C) : infU E n → ℂ) ⟨y, hy⟩) hab
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
    have e' : a.1 g - b.1 g = a.1 (s * y) - b.1 (s * y) := e
    rw [this, sub_self, sub_eq_zero] at e'
    exact e'
  haveI : FiniteDimensional ℂ M := Module.Finite.of_injective f hf
  exact Submodule.finiteDimensional_of_le hle
