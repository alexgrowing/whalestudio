import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChangeNonzero

theorem cuspOver_ne_bot : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T0 : Type) (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ (j : Fin D.R.m), OMPins T R κ v₀ O j → OneMapRow0 T R κ v₀ O j → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → GlobalTheory.OneMapAll.cuspOver (O j) (κ j) ≠ ⊥ := by
  intro D Γ _ _ Pl0 T0 A T _ R F κ v₀ O hnV hC hFW hIo j hP hrow hne
  obtain ⟨tie⟩ := hFW
  have hT : LawsJ T := tie.laws
  have hj : InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have hn : (κ j).n = (Vc D j).rank :=
    (tie.kap j (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) j.2).symm
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsec := cusp_le_sec _ _ _ _ _ hf
  have hBC := GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ (O j).hle _ (T.U ((j : ℕ) + 1)) _ _ f hsec
  have hmem : GlobalTheory.FieldBC.rulBC (O j).hle f ∈ GlobalTheory.OneMapAll.cuspOver (O j) (κ j) := by
    unfold GlobalTheory.OneMapAll.cuspOver
    rw [← hn]
    exact hBC.2.2 hf
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  obtain ⟨σ', hσ'⟩ := GlobalTheory.FieldBC.exists_emb_ext (O j).hle T.toCore.σ₀
  have hrd := hBC.1 σ'
  rw [hmem, map_zero] at hrd
  have hgood : GoodEmb T.Q.c (σ'.comp (incF T.Q.c (O j).c' (O j).hle)) := hσ' ▸ T.toCore.good_σ₀
  have hU : IsUnf (T.U ((j : ℕ) + 1) (σ'.comp (incF T.Q.c (O j).c' (O j).hle))) := hT.unf _ hj _ hgood
  refine hf0 ((GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ T.Q.c _ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U ((j : ℕ) + 1) (σ'.comp (incF T.Q.c (O j).c' (O j).hle))))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) _ _).2 f hsec (fun k x _ => ?_))
  show rdU (T.U ((j : ℕ) + 1) (σ'.comp (incF T.Q.c (O j).c' (O j).hle))) f k x = 0
  exact (congrFun (congrFun hrd k) x).symm

end GlobalTheory.BaseChangeNonzero
