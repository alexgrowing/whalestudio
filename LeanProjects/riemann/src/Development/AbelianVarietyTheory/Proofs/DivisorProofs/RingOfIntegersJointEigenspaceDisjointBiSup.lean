import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

theorem eigSp_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  intro F _ _ g φ s τ hτ
  let ρ : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).toRingEquiv.toRingHom.comp φ
  have hcomm : ∀ a b : 𝓞 F, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : 𝓞 F => ρ a)
    (fun i j m => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) m)
  let χ : (F →+* ℂ) → (𝓞 F → ℂ) := fun σ c => σ (c : F)
  have hχ : Function.Injective χ := by
    intro σ₁ σ₂ he
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact congrFun he c
  have hle : ∀ σ : F →+* ℂ, eigSp φ σ ≤ ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (χ σ c) := by
    intro σ u hu
    rw [Submodule.mem_iInf]
    intro c
    apply (Module.End.genEigenspace (ρ c) (χ σ c)).mono le_top
    rw [Module.End.mem_eigenspace_iff]
    have := hu c
    simpa [ρ, χ, Matrix.toLin'_apply] using this
  have hnot : χ τ ∉ (χ '' (s : Set (F →+* ℂ))) := by
    rintro ⟨σ, hσ, he⟩
    exact hτ (hχ he ▸ hσ)
  have hd := h.disjoint_biSup hnot
  refine (hd.mono_left (hle τ)).mono_right ?_
  refine iSup₂_le fun σ hσ => (hle σ).trans ?_
  exact le_iSup₂_of_le (f := fun (x : 𝓞 F → ℂ) (_ : x ∈ χ '' (s : Set (F →+* ℂ))) => ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (x c)) (χ σ) ⟨σ, hσ, rfl⟩ le_rfl

end GlobalTheory.UPel.HT.LieType
