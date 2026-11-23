import Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsGMapPrPSRatAS

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local irreducible] Formalism.L2.G.repG

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    {I : LocId L p nV W Qq} {N : ℕ}

abbrev StepAt.toG (St : StepAt I O N) (hJ : IsHerm (sp.cm.sig : E →+* E) St.J) (hdet : IsUnit St.J.det)
    (U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ St.Uloc v) :
    StepG I N where
  J := St.J
  hJ := hJ
  hdet := hdet
  Lb := St.Lb
  Uloc := St.Uloc
  fr := St.fr
  U := U
  U_eq := U_eq

section Step

variable (St : StepAt I O N) (hJ : IsHerm (sp.cm.sig : E →+* E) St.J) (hdet : IsUnit St.J.det)
    (U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ St.Uloc v)
    (hH : HypAtPS (St.toG hJ hdet U U_eq))
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam' : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom' : ∀ v, IsDominant (lam' v)) (hk : m + 1 = N)

end Step

end Formalism.L2.G
