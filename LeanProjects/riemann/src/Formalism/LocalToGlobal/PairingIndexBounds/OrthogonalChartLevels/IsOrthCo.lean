import Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsGMapPrPSRatAS

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]

def latAd {N : ℕ} (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) (Fin N → E) :=
  Submodule.span (𝓞 E) {x | ((y⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) ∈ Formalism.L2.Herm.hatL (F := F) Lb}

variable {I : LocId L p nV W Qq} {N m : ℕ}

def ptAd (S : StepG I N) (hk : m + 1 = N) (i : S.comp) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  ((S.rep i * jQS S hk (gOf Lt) : GAS S) : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))

def globLat (S : StepG I N) (hk : m + 1 = N) (i : S.comp) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    Submodule (𝓞 E) (Fin N → E) :=
  latAd (ptAd S hk i Lt) S.Lb

def compan (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  Λ ⊔ Ideal.span {a} • Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Λ)

def IsOrthCo (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : Prop :=
  ∀ x y, ∑ a, σ (co x a) * co y a = ∑ a, ∑ b, σ (x a) * J a b * y b

def stdCo (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) : (Fin N → E) ≃ₗ[E] (Fin N → E) :=
  Classical.epsilon (IsOrthCo σ J)

def toStd (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  Λ.map (((stdCo σ J : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E))

def kerLat (S : StepG I N) (hk : m + 1 = N) (a : 𝓞 E) (i : S.comp) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    Submodule (𝓞 E) (Fin N → E) :=
  toStd (sp.cm.sig : E →+* E) S.J (compan (sp := sp) S.J a (globLat S hk i Lt))

end Formalism.L2.PairingIndexBounds.F
