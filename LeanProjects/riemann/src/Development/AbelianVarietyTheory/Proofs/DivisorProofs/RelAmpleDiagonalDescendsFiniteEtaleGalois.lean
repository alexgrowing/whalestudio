import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.DescGal

theorem relAmple_diag_descends : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro X Y _ π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ _ hA₀ gp sq hP hP₀ hw hamp
  have hc : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left :=
    (GlobalTheory.DiagAmpleExt.diag_comm φ φ₂ sq).symm
  have H₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (P₀.pull φ₂) _ _ rfl) hw
  have H₂ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) _) H₁
  have H₃ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullOut P₀ (fun _ : PUnit => (lift (𝟙 A₀) (𝟙 A₀)).left) (fun _ => 1) φ
        (fun _ => (lift (𝟙 A) (𝟙 A)).left ≫ φ₂) fun _ => hc) H₂
  exact (GlobalTheory.relAmple_kTriv_of_finite_etale_cover Y X π A₀ A φ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left)
    (P.pull (lift (𝟙 A) (𝟙 A)).left) hπ.fin hπ.etale hπ.onto hA₀ (pull_isLB hP₀ _) (pull_isLB hP _) gp H₃).1 hamp

end GlobalTheory.DescGal
