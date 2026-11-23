import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)

def smK (k : Kinf E a) : Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  TensorProduct.map (act (.cpt k)) (Matrix.toLin' (Ξ.mat (Unitary.toUnits k)))

def smLie : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lie E a X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c X := by
    rw [map_smul, map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lie E a X), ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

def IsLevelFn (φ : Sm E a) : Prop :=
  (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ u ∈ U, act (.fin u) φ = φ) ∧
    ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) → lie E a (oneL E a) φ = -m • φ

def IsSqIntMod (φ : Sm E a) : Prop :=
  ∃ (s : ℝ) (χ : HChar E), χ.IsAbsPow s ∧ GlobalTheory.UnitaryBC.IsSqInt fun g => ((chiDet a χ g : ℂˣ) : ℂ) * φ.1 g

def IsCuspFn (φ : Sm E a) : Prop :=
  IsLevelFn U Ξ φ ∧ IsCuspidal φ.1 ∧ ∀ l : List (Lie E a), IsSqIntMod ((l.map (lie E a)).prod φ)

variable {U} in

structure IsRelCochain (P : Sm E a → Prop) {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) : Prop where
  equiv : IsCochain (smK Ξ) ω
  basic : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → ω X = 0
  val : ∀ X, ω X ∈ Submodule.span ℂ {x | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v}

end Defs

def BorelC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    (∀ (γ : GL (Fin a) E) (g : GL (Fin a) (Af E)),
      g⁻¹ * GeneralLinearGroup.map (algebraMap E (Af E)) γ * g ∈ U → IsOfFinOrder γ → γ = 1) →
    ∀ Ξ : AlgRep E a, (∃ N : ℕ, 0 < N ∧ ∀ u : (𝓞 E)ˣ,
      ratC Ξ (GeneralLinearGroup.scalar (Fin a) (Units.map (algebraMap (𝓞 E) E).toMonoidHom (u ^ N))) = 1) →
    ∀ (q : ℕ) (η : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), IsRelCochain Ξ (IsLevelFn U Ξ) η →
      IsRelCochain Ξ (IsCuspFn U Ξ) (dCo (smLie Ξ) η) →
      ∃ η' : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)),
        IsRelCochain Ξ (IsCuspFn U Ξ) η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η

end UpperTheory.V.Lit
