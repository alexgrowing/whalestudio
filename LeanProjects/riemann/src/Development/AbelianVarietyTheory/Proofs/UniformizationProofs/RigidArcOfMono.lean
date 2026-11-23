import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsPullDegId
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitAgreeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPointsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
  {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
  {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}

theorem core (hL : Laws) (hL₂ : Laws2) (hL₅ : Laws5)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c)
    (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ) (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ')
    (hs : y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF)
    (hs' : y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) :
    y = y' ∧ ∃ ψ : W.t.G ≅ W'.t.G,
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left)
        (τ : T ⟶ Sp (FractionRing (PowerSeries k))),
        g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ W.m.φ = g₁ ≫ Y.m.φ →
        g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
        g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) ∧
      ((∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ) := by
  letI := H.starRing
  obtain ⟨hD, hdat⟩ := arcWit_data_iso hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W'
  have hI : Ideal.span {(PowerSeries.X : PowerSeries k)} = IsLocalRing.maximalIdeal (PowerSeries k) :=
    PowerSeries.maximalIdeal_eq_span_X.symm
  obtain ⟨ψ, bc, hψ, hbc, hfst, hU⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD
  have hx : ∀ (x : 𝓞 E) (z : W.P.D.toPre.X), hD.xe (x • z) = x • hD.xe z := by
    intro x z
    obtain ⟨z₀, rfl⟩ := W.e.surjective z
    rw [← W.e.map_smul, hdat.2.1, hdat.2.1]
    exact W'.e.map_smul x z₀
  have hB : ∀ x, (W.P.oD.onB.act x).left ≫
        (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) =
      (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
        (W'.P.oD.onB.act x).left := by
    intro x
    apply W'.spec.1.1.hom_ext
    · have h₁ : (W.P.oD.onB.act x).left ≫ W.φ = W.φ ≫ (a.oa.onB.act x).left := W.spec.2.2.2.1 x
      have h₂ : (W'.P.oD.onB.act x).left ≫ W'.φ = W'.φ ≫ (a.oa.onB.act x).left := W'.spec.2.2.2.1 x
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hdat.1).trans h₁)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hdat.1)))).symm
    · have e : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
          W'.P.D.toPre.P.A.hom = W.P.D.toPre.P.A.hom := by
        have w : hD.e.hom.left ≫ pullback.snd W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k))) =
          W.P.D.toPre.P.A.hom := Over.w hD.e.hom
        rw [Category.assoc, pullback.condition, ← Category.assoc, w, specOf_id, Category.comp_id]
      rw [Category.assoc, e, Over.w, Category.assoc, Over.w, e]
  have hlin := act_comm_of_isPullUnif_id hL.globalFns (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD bc hbc hU (𝓞 E) W'.P.oD W.P.oD W'.P.oA W.P.oA
    W'.t.act.toRingAct W.t.act.toRingAct W'.P.lin W.P.lin hx hB
  have hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x := by
    intro x
    have q := congrArg (fun z => z.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k)))) (hlin x)
    ext
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at q
    rw [hfst, ← Category.assoc, hfst] at q
    exact q
  have hlev := GlobalTheory.T.uniformisedArc_iso_matches_levelPoints hL hL₂ hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact
    y y' hy hy' hs hs'
  have hb : LBIso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hU.lg
    rw [← W.P.bundle, ← W'.P.bundle, ← hfst]
    exact ⟨w, hw⟩
  obtain ⟨e, h⟩ := ArcObj.point_eq hL W.m W'.m ψ hact hb _ y y' hy hy' (hs.trans hs'.symm) hlev
  exact ⟨e, ψ, h, arcWit_agree_of_isPullUnif E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact⟩

theorem exists_generic
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    {T : Scheme.{0}} (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (h₁ : g ≫ W.m.φ = g₁ ≫ Y.m.φ) :
    (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j ∧
      ∃ τ : T ⟶ Sp (FractionRing (PowerSeries k)), g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) := by
  have := ThetaShiftProofs.isOpenImmersion_jK_powerSeries k
  have q : (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j := by
    have h₁' : g ≫ W.m.cm.F = g₁ ≫ Y.m.cm.F := h₁
    rw [Category.assoc, ← W.m.cart.1.w, reassoc_of% h₁', Y.m.cart.1.w, Category.assoc]; rfl
  have hr : Set.range (g ≫ W.t.G.hom) ⊆ Set.range (jK (PowerSeries k)) := by
    rintro _ ⟨p, rfl⟩
    exact arcWit_mem_range_jK_of_mem_range_j E H D l Xo c k bF a O β Y χ W _
      ⟨(g₁ ≫ Y.oF.t.G.hom) p, congrArg (fun z => z p) q.symm⟩
  exact ⟨q, _, (IsOpenImmersion.lift_fac (jK (PowerSeries k)) _ hr).symm⟩

end ArcRigidity

theorem rigidArc_of_mono : Laws → Laws2 → Laws5 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β')
    (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
    y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' →
    y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) := by
  intro hL hL₂ hL₅ E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' y y' hy hy' hs hs'
  obtain ⟨e, ψ, h, hA⟩ := ArcRigidity.core hL hL₂ hL₅ W W' y y' hy hy' hs hs'
  refine ⟨e, fun hm => ⟨ψ, hA fun T g g₁ g₂ h₁ h₂ h₃ => ?_⟩⟩
  obtain ⟨q, τ, hτ⟩ := ArcRigidity.exists_generic W g g₁ h₁
  refine h T g g₁ g₂ τ hτ ?_ h₁ h₂ h₃
  rw [← cancel_mono Y.j, ← q, hτ, Category.assoc, Category.assoc, hy]

theorem uniqWit_of_laws : Laws → Laws2 → Laws5 → UniqWitSt := by
  intro hL hL₂ hL₅ E _ _ _ H D l Xo c k _ bF a O _ β Y χ W W' y hy hs
  obtain ⟨-, ψ, h, hA⟩ := ArcRigidity.core hL hL₂ hL₅ W W' y y hy hy hs hs
  refine ⟨ψ, hA fun T g g₁ g₂ h₁ h₂ h₃ => ?_⟩
  obtain rfl : g₁ = g₂ := Y.m0.toSABMap.cart.1.hom_ext h₂ h₃
  obtain ⟨-, τ, hτ⟩ := ArcRigidity.exists_generic W g g₁ h₁
  have w : (g ≫ W.m.cm.F) ≫ Y.t.G.hom = (τ ≫ y) ≫ Y.j := by
    rw [Category.assoc, W.m.cart.1.w, reassoc_of% hτ, Category.assoc, hy]
  obtain ⟨u, u₁, u₂⟩ : ∃ u : T ⟶ Y.oF.t.G.left, u ≫ Y.m.φ = g ≫ W.m.φ ∧ u ≫ Y.oF.t.G.hom = τ ≫ y :=
    ⟨Y.m.cart.1.lift _ _ w, Y.m.cart.1.lift_fst _ _ _, Y.m.cart.1.lift_snd _ _ _⟩
  rw [h T g u u τ hτ u₂ u₁.symm rfl rfl, u₁, h₁]

end GlobalTheory
