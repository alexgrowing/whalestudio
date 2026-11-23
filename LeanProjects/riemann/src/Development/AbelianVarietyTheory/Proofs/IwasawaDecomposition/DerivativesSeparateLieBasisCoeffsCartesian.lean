import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSnd
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

theorem zeroPt_sc {S : Type} [CommRing S] (c : S) : GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc c = GlobalTheory.PowLie.zeroPt S := by
  ext1
  simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  simp [epsScaleR]

theorem isTangent_prod {S : Type} [CommRing S] {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {n : ℕ}
    (v : Fin n → (epsR S ⟶ G')) (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) :
    IsTangent (∏ k, GlobalTheory.PowLie.sc (c k) ≫ v k) := by
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G') (GlobalTheory.PowLie.zeroPt S)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k) Finset.univ
  refine (e.trans ?_)
  refine (Finset.prod_eq_one fun k _ => ?_).trans rfl
  change GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, zeroPt_sc, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  intro S _ X x G G' _ _ _ φ h n v hv V hA hV b hb
  set w₀ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc (b k) ≫ v k with hw₀
  set w₁ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc ((0 : Fin n → S) k) ≫ v k with hw₁
  have c₀ : IsLieComb b v w₀ := (GlobalTheory.PowLie.isLieComb_iff_prod b v w₀).2 rfl
  have c₁ : IsLieComb 0 v w₁ := (GlobalTheory.PowLie.isLieComb_iff_prod 0 v w₁).2 rfl
  have t₀ : IsTangent w₀ := isTangent_prod v hv.1 b
  have t₁ : IsTangent w₁ := isTangent_prod v hv.1 0
  have l₀ := tan_le h w₀ t₀ V hV
  have l₁ := tan_le h w₁ t₁ V hV
  have fst_eq : ∀ (w : epsR S ⟶ G'), IsTangent w → ∀ f : Γ(G.left, V),
      (valR (w.left ≫ φ) V f).fst = valR ((η[G']).left ≫ φ) V f := by
    intro w hw f
    have e1 := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom S S S).toRingHom (w.left ≫ φ) V (tan_le h w hw V hV) f
    have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (η[G']).left ≫ φ := by
      rw [← Category.assoc]
      exact congrArg (· ≫ φ) hw
    rw [e2] at e1
    rw [e1]
    rfl
  have e : w₀.left ≫ φ = w₁.left ≫ φ := by
    refine GlobalTheory.HolHom.point_ext hA l₀ l₁ fun f => ?_
    refine TrivSqZeroExt.ext ((fst_eq w₀ t₀ f).trans (fst_eq w₁ t₁ f).symm) ?_
    rw [comb_snd h v hv.1 b w₀ c₀ V hV f, comb_snd h v hv.1 0 w₁ c₁ V hV f, hb f]
    simp
  have hw : w₀ = w₁ := ReciprocityTheory.ChartRestriction.G.Chart.inj_over h e
  exact (hv.2 w₀ t₀).unique c₀ (hw ▸ c₁)

end GlobalTheory.ArcLieCoord
