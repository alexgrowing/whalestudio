import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDEqSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatUOfFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlacesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GlobDet

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨N, hN, hNf⟩ := (h₁.1.le hf).2
  have hfix : ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f := fun κ hκ => funext fun g => hNf κ hκ g
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places L n a S₁ S₂ h₁ h₂ hsplit (fun v hv => by
    obtain ⟨w, Dv, α, hw, hs1, hs2⟩ := hinert v hv
    have k1 : ∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs1
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    have k2 : ∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs2
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    exact ⟨w, Dv, α, hw, k1, k2, fun U hU h hh =>
      ⟨fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₁ h₁ v w Dv α hw hs1 U hU f hf hfU h hh,
       fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₂ h₂ v w Dv α hw hs2 U hU f hf hfU h hh⟩⟩) N hN ⟨f, hf, hfix, hf0⟩
  exact GlobalTheory.HeckeRecon.recon L n a a S₁ S₂ h₁ h₂ N hN φ hφ1 hφ2 hφ3

end GlobalTheory.GlobDet
