import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackFstComm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_pullback_fst_comm : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V),
      letI := resAlg h
      ∀ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
        (hφ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
        φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec →
        ∀ (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)) (c : primDR (onAff A hV)), GlobalTheory.HodgeSub.Corr A hV s c →
          GlobalTheory.HodgeSub.Corr A hV' (GlobalTheory.Twist.resM _ h s) ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  first | exact @GlobalTheory.HodgeSub.Nat.corr_res | exact GlobalTheory.HodgeSub.Nat.corr_res | (intros; apply GlobalTheory.HodgeSub.Nat.corr_res <;> assumption)
