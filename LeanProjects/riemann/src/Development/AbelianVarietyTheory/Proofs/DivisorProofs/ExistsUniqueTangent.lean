import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSurjectiveOntoDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentInverseLimitCompatibleStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PDiv in

theorem GlobalTheory.PDivGroup.TorsionTower.existsUnique_tangent : ∀ (p : ℕ) (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (t : G.TorsionTower A) (x : G.Lie), ∃! v : epsR O ⟶ A, t.LieCorr x v := by
  intro p O _ _ G A _ _ t x
  have hfr := GlobalTheory.T.exists_cotangent_frame_smooth_groupScheme O A
  haveI hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.finite_projective_cotangentGlobalSections_groupScheme O A hfr
  have hnat := GlobalTheory.T.tangent_Phi_sqZero_naturality O
  have hinj := GlobalTheory.T.sqZeroPoint_eq_of_cotangentForm_eq O A hq
  have hsurj := GlobalTheory.T.tangent_Phi_surjective_onto_dual O A hq
  have hspec := GlobalTheory.T.tangent_Phi_naturality_module p O G A t (hnat · · A)
  have hl : ∀ n (c : O) w, cn t n (c • w) = c • cn t n w := fun n c w => GlobalTheory.T.tangent_Phi_smul O _ A _ _ c w
  have hres := GlobalTheory.T.tangent_Phi_naturality_linear p O G A t (hnat · · A)
  have hon := GlobalTheory.T.cotangent_inverse_limit_compatible p O G A t hfin (GlobalTheory.T.tangent_Phi_injective_criterion p O G A t hinj hspec)
    (GlobalTheory.T.tangent_Phi_naturality_family p O G A t hfin hproj (hnat · · A) hsurj hspec) hres hl
  have htan := GlobalTheory.T.tangent_Phi_naturality_pair p O G A t (hnat · · A) hspec
  let c : Wmod A →ₗ[O] G.omega :=
    { toFun := fun w => ⟨fun n => cn t n w, fun n => hres n w⟩
      map_add' := fun w w' => Subtype.ext (funext fun n => map_add (cn t n) w w')
      map_smul' := fun a w => Subtype.ext (funext fun n => hl n a w) }
  have hmk : ∀ (n : ℕ) (a b : O), a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      (Ideal.Quotient.mk _ a : ModPow p O n) = Ideal.Quotient.mk _ b := fun n a b => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.Quotient.eq]
  have hu : ∀ a b : O, (∀ n, (Ideal.Quotient.mk _ a : ModPow p O n) = Ideal.Quotient.mk _ b) →
      a = b := fun a b h => sub_eq_zero.1 <| IsHausdorff.haus' (I := Ideal.span {(p : O)}) _
        fun n => SModEq.zero.2 (SModEq.sub_mem.1 ((hmk n a b).2 (h n)))
  obtain ⟨v, hv0, hvμ⟩ := hsurj (x ∘ₗ c)
  have hv : IsTangent v := congrArg Over.Hom.left hv0
  refine ⟨v, (t.lieCorr_iff hv x).2 fun n u => ?_, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ := hon u
    have e : u = c w := Subtype.ext (funext fun n => (hw n).symm)
    rw [← hw n, htan v hv hv0 n w, hvμ, e]
    rfl
  · have hy' : IsTangent y := hy.1
    have hy0 : zeroSec O O ≫ y = η[A] := Over.OverMorphism.ext hy'
    refine hinj O y v hy0 hv0 fun w => ?_
    rw [hvμ]
    refine hu _ _ fun n => ?_
    rw [← htan y hy' hy0 n w]
    exact ((t.lieCorr_iff hy' x).1 hy n (c w)).symm
