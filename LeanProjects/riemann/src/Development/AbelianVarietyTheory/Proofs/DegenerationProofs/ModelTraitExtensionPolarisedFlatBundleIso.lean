import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.ModelFacts

theorem exists_extend {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {W : Type} [CommRing W] [IsDomain W]
    [ValuationRing W] (y : Sp (FractionRing W) ⟶ X) (s : Sp W ⟶ B) (h : y ≫ f = jK W ≫ s) :
    ∃ χ : Sp W ⟶ X, y = jK W ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := W, K := FractionRing W, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_open {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull (y ≫ Y.j) Y.t
  obtain ⟨m₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m m₂
  have h₂ : LBIso PP'.L (Y.t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull Y.t.PP.isLB (pullback.fst Y.t.G.hom (y ≫ Y.j))
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem exists_rigPull {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {χ : S' ⟶ S} (m : SABMap t' t χ) :
    ∃ ω : LB.Iso t'.PP.L (t.PP.L.pull m.φ), RigPull t'.G t.G χ m.φ ω t'.PP.rig t.PP.rig := by
  obtain ⟨w, g, r, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
  rw [m.base] at r
  exact ⟨w, m.cart, (isGen_iff w).2 g, t'.PP.rigGen, r⟩

theorem model_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (y : Sp (FractionRing W) ⟶ Y.X) (s : Sp W ⟶ Sp O), y ≫ Y.s = jK W ≫ s → ∃ χ : Sp W ⟶ Y.X, y = jK W ≫ χ) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c), PolAt Y.t (y ≫ Y.j)) ∧ Flat Y.t.G.hom ∧ ∀ (S : Scheme.{0}) (t : SAB H S) (χ : S ⟶ Y.X) (m : SABMap t Y.t χ) (L : RigLB t.G), L = t.PP → ∃ ω : LB.Iso L.L (Y.t.PP.L.pull m.φ), RigPull t.G Y.t.G χ m.φ ω L.rig Y.t.PP.rig := by
  intro E _ _ _ H D l Xo c O _ β Y
  refine ⟨fun W _ _ _ y s h => exists_extend Y.s (projProper O _ _ Y.proj) y s h, fun K _ y => polAt_open Y y, ?_, ?_⟩
  · have := Y.t.semi.smooth
    infer_instance
  · rintro S t χ m L rfl
    exact exists_rigPull m

end GlobalTheory.ModelFacts
