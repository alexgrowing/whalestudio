import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeChar

theorem chi_mem_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m), ∀ PP ∈ Rl.Pg, ∀ x : (kP PP)ˣ, ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange := by
  classical
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F _ hCore _ _ hroot j PP hPP x
  obtain ⟨k, hk⟩ := (hCore.lev.Pg PP).1 hPP
  have hov := Rl.C.P.overP hk
  obtain ⟨hn, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP hov
  have hcard : Nat.card (kP PP) = D.host.g k := by
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (D.host.g_prime k).ne_zero)
  have : Fintype (kP PP) := Fintype.ofFinite _
  have hu : Nat.card (kP PP)ˣ = D.host.g k - 1 := by
    rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have : NeZero (Nat.card (kP PP)ˣ) := ⟨Nat.card_pos.ne'⟩
  have h1 : ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  rw [hu] at h1
  refine hroot k _ ?_
  rw [mul_comm, pow_mul, h1, one_pow]

end GlobalTheory.TypeChar
