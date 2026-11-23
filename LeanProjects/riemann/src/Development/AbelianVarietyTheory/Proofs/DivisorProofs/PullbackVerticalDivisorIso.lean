import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIsoStatement
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.NotExistsOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.DivPullStr

theorem resG_appLE {X Y : Scheme.{0}} (g : Y ⟶ X) (U : X.Opens) (V W : Y.Opens) (e : V ≤ g ⁻¹ᵁ U)
    (h' : W ≤ V) (h : W ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    resG Y h' ((g.appLE U V e).hom a) = resG Y h ((g.app U).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, GlobalTheory.LB.resG_resG]

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (I : B.effVert), Nonempty ((Scheme.Modules.pullback f.f).obj (divMod I.1) ≅ divMod (GlobalTheory.Vert.Model.effPull f.comp_str I).1) := by
  intro O _ _ _ B B' f I
  set D := Model.effData I with hD
  have hk : D.KeepsRegular f.f := Model.keepsRegular f.comp_str (Model.idealSheaf_effData I)
  have hL' : (D.lb.pull f.f).IsLB := Semi.LB.isLB_pull D.isLB_lb f.f
  obtain ⟨e₁⟩ := nonempty_cut_iso D
  rw [Model.idealSheaf_effData] at e₁
  obtain ⟨e₂⟩ := GlobalTheory.T.pullback_twisted_section_iso f.f (GlobalTheory.structureModule B.X) D.isLB_lb D.canonical hL'
  obtain ⟨eO⟩ := AbLaw.LbSheafModel.pullback_unit (X := B.X) f.f
  let G := (Scheme.Modules.pullback f.f).obj (GlobalTheory.structureModule B.X)
  haveI : G.IsQuasicoherent := isQuasicoherent_pullback f.f _
  haveI := Twist.isQuasicoherent_twist (F := G) (isLB_lbZPow hL' (-1))
  let φ : twistZ G (D.lb.pull f.f) (-1) ⟶ GlobalTheory.structureModule B'.X :=
    cutHom G hL' (secPull D.canonical f.f) ≫ eO.hom
  have hM : IsMulBy φ (D.pull f.f hk).canonical := by
    intro i V h
    have h' : V ≤ (D.lb.pull f.f).U (fun _ => i) := fun y hy => mem_pull.2 (h hy)
    obtain ⟨e, he⟩ := isMulBy_cutHom G hL' (secPull D.canonical f.f) (fun _ => i) V h'
    refine ⟨e ≪≫ₗ LB.appLinearEquiv eO V, fun t => ?_⟩
    have hs : resG B'.X h' ((secPull D.canonical f.f).f (fun _ => i)) =
        resG B'.X h ((D.pull f.f hk).canonical.f i) := by
      exact resG_appLE f.f (D.U i) _ V _ h' h (D.f i)
    change eO.hom.app V ((cutHom G hL' (secPull D.canonical f.f)).app V t) = _
    rw [he, hs]
    exact (LB.appLinearEquiv eO V).map_smul _ _
  obtain ⟨e₃⟩ := nonempty_cokernel_iso (D.pull f.f hk) hM
  have hI : (D.pull f.f hk).idealSheaf = (GlobalTheory.Vert.Model.effPull f.comp_str I).1 := by
    rw [EffCartierData.idealSheaf_pull, hD, Model.idealSheaf_effData]; rfl
  rw [hI] at e₃
  exact ⟨(Scheme.Modules.pullback f.f).mapIso e₁.symm ≪≫ e₂ ≪≫ (cokernelCompIsIso _ _).symm ≪≫ e₃⟩

end GlobalTheory.DivPullStr
