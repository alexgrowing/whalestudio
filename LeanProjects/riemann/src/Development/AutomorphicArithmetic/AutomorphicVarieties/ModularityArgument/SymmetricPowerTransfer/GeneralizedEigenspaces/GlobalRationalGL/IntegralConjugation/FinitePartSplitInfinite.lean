import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finite_part_split_infinite {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (f x : UA L n)
    (hf : f ∈ finU L n) (hw : ∀ w : Plc L, mL w f = mL w x) :
    f⁻¹ * x ∈ infU L n ∧ x = f * (f⁻¹ * x) ∧ ∀ τ, cEmb τ (f⁻¹ * x) = cEmb τ x := by
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := uaFacts L n
  refine ⟨((h6 _).2).2 fun w => ?_, by group, fun τ => ?_⟩
  · have : cLoc w f = cLoc w x := Units.ext (hw w)
    rw [map_mul, map_inv, this, inv_mul_cancel]
  · rw [map_mul, map_inv, ((h6 f).1).1 hf τ, inv_one, one_mul]

theorem UpperTheory.V.Z.Sym.Dict.Br.okFin :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (γ : U3 B.Δ) (g : GA B.Δ), (∀ v, (g.1 v : Matrix (Fin 3) (Fin 3) _) = (γ : Matrix (Fin 3) (Fin 3) _).map (lmap (cv v) B.Δ)) → ∃ k ∈ infU L 3, (B.rG γ : UA L 3) = B.bG g * k ∧ ∀ τ, cEmb τ k = cEmb τ (B.rG γ : UA L 3)) ∧ ∀ (γ : SU B.Δ) (g : SA B.Δ), (∀ v, mt ((g : DA B.Δ).1 v) = (mt (γ : DX B.Δ)).map (lmap (cv v) B.Δ)) → ∃ k ∈ infU L 2 ⊓ SUA L, (B.rS γ : UA L 2) = B.bS g * k ∧ ∀ τ, cEmb τ k = cEmb τ (B.rS γ : UA L 2) := by
  intro L _ _ _ B
  refine ⟨fun γ g h => ?_, fun γ g h => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := finite_part_split_infinite (B.bG g : UA L 3) (B.rG γ : UA L 3) (B.bG g).2 fun w => by
      rw [B.bG_loc, B.rG_loc, h (un w), Matrix.map_map]
      exact Matrix.ext fun i j => B.ρ_glob (un w) w rfl _
    exact ⟨_, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := finite_part_split_infinite (B.bS g : UA L 2) (B.rS γ : UA L 2) (B.bS g).2.1 fun w => by
      rw [B.bS_loc, B.rS_loc, h (un w), Matrix.map_map]
      exact Matrix.ext fun i j => B.ρ_glob (un w) w rfl _
    exact ⟨_, ⟨h1, (SUA L).mul_mem ((SUA L).inv_mem (B.bS g).2.2) (B.rS γ).2.2⟩, h2, h3⟩
