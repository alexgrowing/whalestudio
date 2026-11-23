import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PtGComp

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

abbrev HA (sp : Spaces R F E) : Subgroup (GA sp) :=
  (ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

abbrev KA (L : ColLevel R F E sp gp C A clsLat) : Subgroup (GA sp) :=
  L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

abbrev KA' (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Subgroup (GA sp) :=
  (Formalism.L2.Herm.awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

def ratA (sp : Spaces R F E) : UJ (sp.cm.sig : E →+* E) sp.gram0 →* GA sp :=
  ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).comp (UJ (sp.cm.sig : E →+* E) sp.gram0).subtype).codRestrict _
    (fun γ => Formalism.UG.P.rational_points_le_holds F E (Fin R.k) sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ⟨γ, γ.2, rfl⟩)

theorem ratA_val (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    (ratA sp γ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin R.k) E) := rfl

theorem ratA_mem (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) : ratA sp γ ∈ HA sp :=
  Subgroup.mem_subgroupOf.2 ⟨γ, γ.2, rfl⟩

theorem exists_ratA (x : GA sp) (hx : x ∈ HA sp) : ∃ γ, ratA sp γ = x := by
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 hx
  exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩

theorem mem_map_conj {G0 : Type} [Group G0] (S : Subgroup G0) (y g : G0) :
    g ∈ S.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * g * y ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : y⁻¹ * (MulAut.conj y).toMonoidHom u * y = u := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hu
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_gamC_iff (y : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _) ↔ y⁻¹ * ratA sp γ * y ∈ KA' L p :=
  mem_map_conj (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin R.k) E))

theorem prP_ratA (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) (v : Fin nV) :
    prP I hk (ratA sp γ) v = (castGL hk Qq).symm ((I.frQ v)⁻¹ * bc (I.iw v) (γ : GL (Fin R.k) E) * I.frQ v) := by
  rw [prP_apply, toF_symm]
  congr 1
  rw [map_mul, map_mul, map_inv]
  rfl

end Formalism.L2.G.Cmp
