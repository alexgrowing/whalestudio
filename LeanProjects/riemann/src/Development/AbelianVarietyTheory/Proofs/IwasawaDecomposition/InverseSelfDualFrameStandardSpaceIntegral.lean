import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrameInv

theorem inv_col_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (a j : Fin n) (hmem : (Pi.single j 1 : Fin n → E) ∈ Λ) : (β⁻¹).val a j ∈ Formalism.L2.Herm.intAf F E := by
  have hhat : (fun k => (Pi.single j 1 : Fin n → E) k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hmem, rfl⟩
  have e : (fun k => (Pi.single j 1 : Fin n → E) k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = Pi.single j 1 := by
    funext k
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  rw [e] at hhat
  have := (hfr _).1 hhat a
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem isIntM_inv : ∀ (D : D7) (i : Fin D.R.m) (β : GL (Fin (Vc D i).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)), VStd D i → IsSDFrame (Vc D i) β Λ 1 → IsIntM (β⁻¹).val := by
  intro D i β Λ hV hΛ a j
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hmem : (Pi.single j 1 : Fin (Vc D i).rank → D.host.E) ∈ Λ := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ, ← GlobalTheory.SplitReps.hLat_one, hV.2]
    intro k _
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  exact inv_col_int β Λ hfr a j hmem

end GlobalTheory.StdFrameInv
