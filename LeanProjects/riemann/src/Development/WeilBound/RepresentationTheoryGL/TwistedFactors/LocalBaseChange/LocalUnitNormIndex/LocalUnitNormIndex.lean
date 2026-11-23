import Mathlib

noncomputable section

open ValuativeRel

namespace PositivityTheory.Lbc

variable (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]

def normU : Eˣ →* Fˣ := Units.map (Algebra.norm F : E →* F)

def OU (K : Type) [Field K] [ValuativeRel K] : Subgroup Kˣ :=
  (Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom).ker

def incU : Fˣ →* Eˣ := Units.map (algebraMap F E : F →* E)

def ramIdx : ℕ := ((incU F E).range ⊔ OU E).index

variable {F E}

def sigU (σ : E ≃ₐ[F] E) : Eˣ →* Eˣ := Units.map (σ : E →* E)

def IsGen (σ : E ≃ₐ[F] E) : Prop := ∀ τ : E ≃ₐ[F] E, ∃ k : ℕ, τ = σ ^ k

def normT (n : ℕ) : (Fin n → Eˣ) →* (Fin n → Fˣ) := MonoidHom.compLeft (normU F E) (Fin n)

def incT (n : ℕ) : (Fin n → Fˣ) →* (Fin n → Eˣ) := MonoidHom.compLeft (incU F E) (Fin n)

def sigT (σ : E ≃ₐ[F] E) (n : ℕ) : (Fin n → Eˣ) →* (Fin n → Eˣ) := MonoidHom.compLeft (sigU σ) (Fin n)

def sigD (σ : E ≃ₐ[F] E) (n : ℕ) : (Fin n → Eˣ) →* (Fin n → Eˣ) := sigT σ n * (MonoidHom.id _)⁻¹

def nmT (n : ℕ) : (Fin n → Eˣ) →* (Fin n → Eˣ) := (incT (F := F) n).comp (normT (F := F) n)

def countSet (σ : E ≃ₐ[F] E) (n : ℕ) (K' : Subgroup (Fin n → Eˣ)) (t' δ : Fin n → Eˣ) :
    Set ((Fin n → Eˣ) ⧸ ((incT (F := F) n).range ⊔ K')) :=
  {q | ∃ s : Fin n → Eˣ, (s : (Fin n → Eˣ) ⧸ ((incT (F := F) n).range ⊔ K')) = q ∧
      t'⁻¹ * (s⁻¹ * δ * sigT σ n s) ∈ K'}

def fixMod (σ : E ≃ₐ[F] E) (n : ℕ) (K' : Subgroup (Fin n → Eˣ)) : Subgroup (Fin n → Eˣ) :=
  K'.comap ((sigT σ n) * (MonoidHom.id _)⁻¹)

def cnt (σ : E ≃ₐ[F] E) (n : ℕ) (K' : Subgroup (Fin n → Eˣ)) : ℕ :=
  ((incT (F := F) n).range ⊔ K').relIndex (fixMod σ n K')

def GoodK (σ : E ≃ₐ[F] E) (n : ℕ) (K' : Subgroup (Fin n → Eˣ)) : Prop :=
  IsOpen (K' : Set (Fin n → Eˣ)) ∧ (∀ x ∈ K', ∀ i, x i ∈ OU E) ∧ ∀ x ∈ K', sigT σ n x ∈ K'

variable (F E)

def LocalUnitNormContinuous : Prop := Continuous (normU F E)

def LocalUnitNormOpen : Prop := IsOpenMap (normU F E)

def LocalUnitNormOpenSubgroup : Prop :=
  ∀ U : Subgroup Eˣ, IsOpen (U : Set Eˣ) → IsOpen ((U.map (normU F E) : Subgroup Fˣ) : Set Fˣ)

def LocalUnitNormKernel : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ∀ x : Eˣ, normU F E x = 1 ↔ ∃ y : Eˣ, x = y / sigU σ y

def LocalUnitNormIndex : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ((OU E).map (normU F E)).relIndex (OU F) = ramIdx F E

def NormIndex : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → (normU F E).range.index = Module.finrank F E

def LocalUnitNormIndexFinite : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ∀ (n : ℕ) (K' : Subgroup (Fin n → Eˣ)), GoodK σ n K' →
    ∀ t' δ : Fin n → Eˣ, (countSet σ n K' t' δ).Finite

def LocalUnitNormIndexEmpty : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ∀ (n : ℕ) (K' : Subgroup (Fin n → Eˣ)), GoodK σ n K' →
    ∀ t' δ : Fin n → Eˣ, (countSet σ n K' t' δ).Nonempty ↔
      (normT (F := F) n t')⁻¹ * normT (F := F) n δ ∈ K'.map (normT (F := F) n)

def LocalUnitNormIndexCard : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ∀ (n : ℕ) (K' : Subgroup (Fin n → Eˣ)), GoodK σ n K' →
    ∀ t' δ : Fin n → Eˣ, (countSet σ n K' t' δ).Nonempty →
      Nat.card (countSet σ n K' t' δ) = cnt (F := F) σ n K'

def LocalUnitNormIndexFormula : Prop :=
  ∀ σ : E ≃ₐ[F] E, IsGen σ → ∀ (n : ℕ) (K' : Subgroup (Fin n → Eˣ)), GoodK σ n K' →
    cnt (F := F) σ n K' = (K'.map (normT (F := F) n)).relIndex (K'.comap (incT (F := F) n))

end PositivityTheory.Lbc
