import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

open scoped TensorProduct

namespace GlobalTheory.StdRead

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_of_mem_hatL_pi {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) (i : Fin n) :
    z i ∈ Formalism.L2.Herm.intAf F E := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hy i (Set.mem_univ i))
    exact Subring.subset_closure (Or.inl ⟨⟨y i, b, hb⟩, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact mul_mem a.2 hx

theorem single_mem_hatL_pi (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  refine Submodule.subset_span ⟨Pi.single j 1, fun i _ => ?_, funext fun i => ?_⟩
  · by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, map_one]
    · simp only [Pi.single_eq_of_ne h, map_zero]

theorem entries_int_of_isFrame_pi (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hβ : Formalism.L2.DIV.IsFrame β (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) :
    (∀ i j, β.val i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (β⁻¹).val i j ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : Matrix.mulVec β.1 (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
        Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      refine (hβ _).2 fun l => ?_
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact int_of_mem_hatL_pi (single_mem_hatL_pi j) l
    have h2 := int_of_mem_hatL_pi h1 i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hβ _).1 (single_mem_hatL_pi j) i
    rwa [Matrix.mulVec_single_one] at h2

end Gen

theorem isIntM_of_isFrame_stdL : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)),
    Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val :=
  fun β hβ => entries_int_of_isFrame_pi β hβ

end GlobalTheory.StdRead
