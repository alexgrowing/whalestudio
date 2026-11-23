import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

namespace UpperTheory.V.Z.Tf.GOne

def Temp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CG E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ ∀ z ∈ B, ‖(z : ℂ)‖ = 1

def TempOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → Temp (CG.mk π)

def UnitOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → (CG.mk π).IsUnitary

def Thin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  (Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹) ∧
    {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w}.Infinite

def SplitCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CG E n, π.IsUnitary → Temp π →
  ∀ (J : Type) [Fintype J] (a : J → ℕ) (P : ∀ j, CG E (a j)), (∀ j, 1 ≤ a j) → (∀ j, (P j).IsUnitary) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w (b j)) ∧ π.HasSat w (∑ j, b j)) →
    ∃ j, (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π⟩

def StrSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a) (σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))), 1 ≤ N → IsDiscrete V →
  P.IsUnitary → IsNormalised P → AscEmb V P d → (∀ w, IsLocCompGL V w (σ w)) →
  ∀ ν : Fin d → Formalism.L2.Host.HChar E, (∀ k, (ν k).IsAbsPow (spehExp d k)) →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ b : Fin d → Multiset ℂˣ,
    (∀ k, (CG.mk (P.twist (ν k))).HasSat w (b k)) ∧ GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w N) ∧
      GlobalTheory.LFun.HasSatGL w (σ w).ρ (∑ k, b k)

def SplitAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsUnitary → Temp (CG.mk π) → ∀ D : Pre E n, D.Reg →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

end UpperTheory.V.Z.Tf.GOne

end
