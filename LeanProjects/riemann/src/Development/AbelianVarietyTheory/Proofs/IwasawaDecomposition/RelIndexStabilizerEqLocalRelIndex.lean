import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

namespace GlobalTheory.LocRelIndex

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  intro L _ _ _ n s J H hJH
  set K := GlobalTheory.HeckeScalarSph.locK (L := L) n s.v with hK
  set O := Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  let φ : K →* O :=
    ((s.loc n).comp K.subtype).codRestrict O (fun κ => (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s κ.2.2).2 κ.2.1)
  have hsurj : Function.Surjective φ := by
    intro A
    obtain ⟨x, hx, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 A.1
    refine ⟨⟨x, ?_, hx.1⟩, ?_⟩
    · exact (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx.1).1 (hx.2 ▸ A.2)
    · exact Subtype.ext hx.2
  have hcomap : J.subgroupOf K = (H.subgroupOf O).comap φ := by
    ext κ
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hJH κ κ.2.2
  rw [Subgroup.relIndex, Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj]

end GlobalTheory.LocRelIndex
