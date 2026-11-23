import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isAdapted_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g p q ℓ ψ ρH ρHC HL ev σ σC b₁ b₂ u x₁ x₂ hu hE hσ hcl hA hb₁ hb₂
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IsEval at hE
  unfold GlobalTheory.CompanionTheory.Ar.Flat.IsAdapted at hA ⊢
  obtain ⟨hE1, hE2, hE3⟩ := hE
  obtain ⟨hA1, hA2, hA3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show ev ⟨u i, hu i⟩ ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρHC σC
    have hui := hA1 i
    rw [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf] at hui ⊢
    intro a
    have h1 := hui a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change ρH a (u i) = σ (a : E) • u i at h1
    show ρHC a (ev ⟨u i, hu i⟩) = σC (a : E) • ev ⟨u i, hu i⟩
    obtain ⟨hσa, hψ⟩ := hσ (a : E)
    have hmem : ρH a (u i) ∈ HL := hcl a (u i) (hu i)
    have e1 : ev ⟨ρH a (u i), hmem⟩ = ρHC a (ev ⟨u i, hu i⟩) := hE1 a ⟨u i, hu i⟩ hmem
    have e2 : (⟨ρH a (u i), hmem⟩ : HL) = (⟨σ a, hσa⟩ : R') • (⟨u i, hu i⟩ : HL) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subring.smul_def]
      exact h1
    rw [← e1, e2, map_smulₛₗ, hψ]
  · intro i
    exact hE2 ⟨u (Fin.castAdd q i), hu _⟩ (x₁ i) ((hA2 i).trans (hb₁ i))
  · intro j
    obtain ⟨hj1, hj2⟩ := hA3 j
    constructor
    · have hc : (u (Fin.natAdd p j)).1 = comb ℓ (fun _ => (0 : R')) := by
        rw [hj1]
        simp [GlobalTheory.CompanionTheory.Ar.Flat.CPoint.comb]
      have h3 := hE2 ⟨u (Fin.natAdd p j), hu _⟩ (fun _ => 0) hc
      refine h3.trans ?_
      funext k
      simp
    · intro j'
      have hc : (u (Fin.natAdd p j)).2 (comb ℓ (x₂ j')) = ((if j = j' then 1 else 0 : R') : Ω) := by
        rw [← hb₂ j', hj2 j']
        split_ifs <;> simp
      have h3 := hE3 ⟨u (Fin.natAdd p j), hu _⟩ (x₂ j') (if j = j' then 1 else 0) hj1 hc
      refine h3.trans ?_
      split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
