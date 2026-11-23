import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField IntermediateField

theorem ramificationIndex_eq_one_of_adjoin_range_eq_top (F E K L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L]
    [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L]
    [FiniteDimensional F E] [FiniteDimensional K L] :
    GroundTheory.LocalField.ramificationIndex F E = 1 →
      Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
        GroundTheory.LocalField.ramificationIndex K L = 1 := by
  intro he hadj
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  set m := Nat.card 𝓀[E] - 1 with hm_def
  have hmE : (m : 𝓀[E]) ≠ 0 := natCast_card_residueField_sub_one_ne_zero E
  have hmF : (m : 𝓀[F]) ≠ 0 := fun h0 ↦ hmE (by rw [← map_natCast (algebraMap 𝓀[F] 𝓀[E]), h0, map_zero])
  have hmK : (m : 𝓀[K]) ≠ 0 := fun h0 ↦ hmF ((algebraMap 𝓀[F] 𝓀[K]).injective (by rw [map_natCast, h0, map_zero]))
  have hζ' : IsPrimitiveRoot (algebraMap E L ζ) m := hζ.map_of_injective (algebraMap E L).injective
  have hE : Set.range (algebraMap E L) ⊆ Algebra.adjoin K {algebraMap E L ζ} := by
    rintro _ ⟨e, rfl⟩
    have he' : e ∈ Algebra.adjoin F {ζ} := by
      rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial
    have h1 : algebraMap E L e ∈ (Algebra.adjoin F {ζ}).map (IsScalarTower.toAlgHom F E L) :=
      ⟨e, he', rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin F {(IsScalarTower.toAlgHom F E L) ζ} ≤
        (Algebra.adjoin K {algebraMap E L ζ}).restrictScalars F :=
      Algebra.adjoin_le (by simpa using Algebra.subset_adjoin (R := K) (s := {algebraMap E L ζ}))
    exact h2 h1
  have hadjK : Algebra.adjoin K {algebraMap E L ζ} = ⊤ := by
    rw [eq_top_iff, ← hadj]
    exact Algebra.adjoin_le hE
  have htopK : K⟮algebraMap E L ζ⟯ = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mpr hadjK
  exact ramificationIndex_eq_one_of_adjoin_eq_top hζ' hmK htopK

end GlobalTheory
