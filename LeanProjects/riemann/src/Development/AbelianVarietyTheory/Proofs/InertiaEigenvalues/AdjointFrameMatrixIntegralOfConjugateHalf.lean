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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAdjInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

set_option synthInstance.maxHeartbeats 400000

theorem cA_smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    cA D e • genE (S := S) (T := T) c τ σ = genE (sR D (toEAf D e) * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, toEAf_cA, mul_assoc]

set_option maxHeartbeats 4000000 in

theorem frMapAdj_int_of_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ u : WO S T, u ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf (cA D e) u → IsIntM (frMapAdj S T βS βT u) := by
  intro D S T ΛS ΛT βS βT hS hT fS fT P e he hP u hu hh
  have hx : cA D e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapAdj S T βS βT (cA D e • genL S T α a s t))
    rw [genL_eq_genE, cA_smul_genE, frMapAdj_genE]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have h1 : sR D (sR D (toEAf D e) * (eToEAf D a * ((1 : D.host.E) ⊗ₜ[D.host.F] α))) =
        (toEAf D e * eToEAf D (D.sp.cm.sig a)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      rw [map_mul, map_mul, sR_sR, sR_eTo, mul_assoc]
      congr 2
      show (star (1 : D.host.E)) ⊗ₜ[D.host.F] α = _
      rw [star_one]
    rw [h1]
    refine mul_mem (mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP a ha)
      (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))) (mul_mem ?_ ?_)
    · exact (fS _).1 (mem_hatL_of_mem hs) i
    · rw [Matrix.vecMul_vecMul]
      have hcol : (fun l => (GE T * (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) l j) =
          GE T *ᵥ (fun i => (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (t k))) ⬝ᵥ
        (fun l => (GE T * (βT : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) l j) ∈ _
      rw [hcol]
      exact hform_int hT ht (col_mem_hatL fT j)
  | zero =>
    rw [smul_zero, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfAdjInt
