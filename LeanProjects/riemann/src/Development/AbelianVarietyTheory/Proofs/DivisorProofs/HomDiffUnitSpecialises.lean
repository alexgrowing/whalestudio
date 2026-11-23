import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hom_diff_unit_specialises : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t s : S, s ∈ closure {t} → (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∀ x : A.left, A.hom x = s → (u * v⁻¹).left x = (η[B]).left s := by
  intro S A B _ _ _ _ u v hA hB hu hv t s hst H x hx
  haveI := hA.smooth
  haveI := hB.proper
  have hη : (η[B]).left ≫ B.hom = 𝟙 S := by simpa using Over.w (η[B])
  have hid : IsClosedImmersion (𝟙 S) := inferInstance
  haveI : IsClosedImmersion ((η[B]).left ≫ B.hom) := by rw [hη]; exact hid
  haveI : IsClosedImmersion (η[B]).left := IsClosedImmersion.of_comp _ B.hom
  have hF : IsClosed ((u * v⁻¹).left ⁻¹' Set.range (η[B]).left) :=
    (η[B]).left.isClosedEmbedding.isClosed_range.preimage (u * v⁻¹).left.continuous
  have hcl : x ∈ closure (A.hom ⁻¹' {t}) := by
    rw [mem_closure_iff]
    intro U hU hxU
    have hO : IsOpen (A.hom '' U) := A.hom.isOpenMap U hU
    obtain ⟨_, ⟨y, hyU, rfl⟩, hyt⟩ := mem_closure_iff.mp hst _ hO ⟨x, hxU, hx⟩
    exact ⟨y, hyU, hyt⟩
  have hmem : x ∈ (u * v⁻¹).left ⁻¹' Set.range (η[B]).left :=
    closure_minimal (fun z (hz : z ∈ A.hom ⁻¹' {t}) =>
      (⟨t, (H z hz).symm⟩ : (u * v⁻¹).left z ∈ Set.range (η[B]).left)) hF hcl
  obtain ⟨y, hy⟩ := hmem
  have hys : y = s := by
    have e1 := congrArg B.hom hy
    rw [← Scheme.Hom.comp_apply, hη, ← Scheme.Hom.comp_apply, Over.w] at e1
    simpa [hx] using e1
  subst hys
  exact hy.symm

end GlobalTheory
