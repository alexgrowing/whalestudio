import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifTrait

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in

theorem exists_intFr_frBor (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt) (hzs : z ≫ pullback.snd _ _ = spMap io) :
    letI := io.toAlgebra
    ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1 := by
  let _ := io.toAlgebra
  intro y₀ hy0
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T io O β Y yt z hz hzs _ m
  have hx : (z ≫ pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨x₀, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ := y₀
  change x₀ = z ≫ pullback.fst _ _ at hy0
  subst hy0
  obtain ⟨ub, u, hub, htan, heig, hbas, htri⟩ := lieFree Xo c T io _ t' _ m1 m2 hx u₀ htan₀ heig₀ hbas₀
  obtain ⟨θ, s, hθ, hmatch, hgen, a, ha⟩ :=
    GlobalTheory.DepthSum.thetaFrame_trait Xo c T io O β Y yt z hz hzs _ m t' m1 m2 s₀ hgen₀
  let y : FrPt Xo c T.Fr := ⟨z ≫ pullback.fst _ _, hx, u, htan, heig, hbas, s, hgen⟩
  choose cf hcf using htri
  let tt : Ix Dw → T.Frˣ := fun o => match o with
    | none => a
    | some p => (hcf p.1 p.2).1.unit
  have hFB : FrBor tt ⟨z ≫ pullback.fst _ _, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ y := by
    refine ⟨rfl, fun τ i => ⟨cf τ i, (hcf τ i).1.unit_spec.symm, (hcf τ i).2.1, (hcf τ i).2.2⟩, 𝟙 _,
      Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    change (Scheme.Hom.appLE (𝟙 (Gx (z ≫ pullback.fst _ _))) _ _ h).hom
      (scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i) = s.f i
    rw [ha i, Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp, show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨⟨y, GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T.Fr y, _, t', m1, m2, ⟨ub, hub⟩, θ, hθ, hmatch⟩, tt, hFB⟩

end Frames

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

section Split

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem charZero_residue_of_map {K : Type} [Field K] [CharZero K] (V : Type) [CommRing V] [IsLocalRing V]
    (f : Sp V ⟶ Sp K) : CharZero (ResidueField V) :=
  charZero_of_injective_ringHom ((residue V).comp (Spec.preimage f).hom).injective

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, Sx, ⟨d⟩⟩ := GlobalTheory.UnifAfterExt.exists_finite_split _ h₀
  have : Algebra.IsSeparable (ResidueField W) k' := inferInstance
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, -, -, e, he⟩ := GlobalTheory.unramExt W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) Sx _ d)⟩

end Split

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

open IsLocalRing

set_option maxHeartbeats 1000000 in

theorem exists_ext_intFr_unif : Hypotheses2 → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  intro _ E _ _ _ H Dw l Xo c TF T io
  letI := io.toAlgebra
  intro P w hw
  have hz : FlagMod.frX P ≫ TF.Y.j = spMap (algebraMap T.V T.Fr) ≫ w := by
    rw [hw, (TF.X.lies_ptY P).1]
  have hzs : FlagMod.frX P ≫ pullback.snd _ _ = spMap io := FlagMod.frX_snd P
  obtain ⟨y₀, tt, hB⟩ := exists_intFr_frBor T io c.F (RingHom.id c.F) TF.Y w (FlagMod.frX P) hz hzs P
    (FlagMod.frX_fst P).symm
  obtain ⟨G₀, ⟨m₀⟩⟩ : ∃ G₀ : SAB H (Sp T.V), Nonempty (SABMap G₀ TF.Y.t w) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull w TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₀, m1₀, m2₀, -⟩ := genFibre Xo c Out.CubePf.cubePull T io c.F (RingHom.id c.F) TF.Y w _ hz hzs G₀ m₀
  have : CharZero (ResidueField T.V) := charZero_residue_of_map T.V (w ≫ TF.Y.s)
  obtain ⟨W, _, _, _, _, _, hf, hi, hS⟩ := exists_split_baseChange T.V G₀.G G₀.semi
  have : CharZero W := charZero_of_injective_ringHom hi
  let T' : CDVR := { V := W }
  let j : T.V →+* T'.V := algebraMap T.V W
  have hfin : j.Finite := RingHom.finite_algebraMap.2 hf
  obtain ⟨i, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' j hi hfin
  letI := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
    T.Fr T'.Fr ψ y₀.1
  let y' : IntFr Xo c T' (i.comp io) := ⟨z', GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T'.Fr z',
    GlobalTheory.IntegralExt.integral_baseChange T T' io (i.comp io) j hi ψ hφ y₀.1 z' hz' y₀.2.2⟩
  obtain ⟨G, ⟨mG⟩⟩ : ∃ G : SAB H (Sp T'.V), Nonempty (SABMap G TF.Y.t (spMap j ≫ w)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap j ≫ w) TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  have hι : i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j := RingHom.ext hφ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap j = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.EtaVal.spMap_comp_spMap, GlobalTheory.EtaVal.spMap_comp_spMap, hι]
  have hz2 : (spMap i ≫ FlagMod.frX P) ≫ TF.Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap j ≫ w := by
    rw [Category.assoc, hz, ← Category.assoc, ← hio, Category.assoc]
  have hzs2 : (spMap i ≫ FlagMod.frX P) ≫ pullback.snd _ _ = spMap (i.comp io) := by
    rw [Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap]
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T' (i.comp io) c.F (RingHom.id c.F) TF.Y
    (spMap j ≫ w) _ hz2 hzs2 G mG
  have hx' : y'.1.x = (spMap i ≫ FlagMod.frX P) ≫ pullback.fst _ _ := by
    rw [Category.assoc, FlagMod.frX_fst, ← hB.1]
    exact hz'.1
  obtain ⟨Pu, -⟩ := GlobalTheory.IntegralExt.exists_unif_of_split T T' j i hφ m1₀ m2₀ (Category.assoc _ _ _) m1 m2 hS
  have hloc : IsLocalHom j := hfin.to_isIntegral.isLocalHom hi
  refine ⟨T', i, j, r, y', G, mG, Pu, t', (by rw [hx']; exact m1), m2, hr0, hv, hι, fun a ha => map_nonunit j a ha,
    ?_⟩
  rw [TF.X.ptY_frBor hB, ← TF.X.ptY_frMap hz']

end GlobalTheory.UnifTrait
