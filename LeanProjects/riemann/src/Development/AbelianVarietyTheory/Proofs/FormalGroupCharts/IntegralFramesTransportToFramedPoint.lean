import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompatiStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameAdjointnessSeriesOfPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTripleStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCubeFramesFromPullbackTripleStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTripleStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidifiedIsoMapsCubicalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameMove

theorem corr_trans {Z Y : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
    {φ : K → (Y ⟶ Z)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Z)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ Z)} {ε'' : K'' → ℤ}
    {a : LB.Gen (LB.LinComb L φ ε)} {b : LB.Gen (LB.LinComb L φ' ε')} {c : LB.Gen (LB.LinComb L φ'' ε'')}
    (h : LB.Gen.Corr L φ ε φ' ε' a b) (h' : LB.Gen.Corr L φ' ε' φ'' ε'' b c) : LB.Gen.Corr L φ ε φ'' ε'' a c :=
  corr_of_val hL fun _ _ hJ => (val_corr hJ h _).trans (val_corr hJ h' _)

theorem ad_const {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O) (a : O) :
    MvPowerSeries.constantCoeff (B.ad a) = 1 := by
  have h := GlobalTheory.GaugeAdjoint.constantCoeff_ev (a := (![0, pt R d 0] : Fin 2 → Pt R 1 d)) (fun j i => by
    fin_cases j
    · simp
    · simp [pt]) (B.ad a)
  rw [B.adjoint_zero_fst a, map_one] at h
  exact h.symm

theorem isFrame_pull_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0)
    (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)) (hw : RigIso mp w) (hab : IsAbelianScheme t'.G) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G)
    (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left)
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m) (he : ∀ m, (e m).IsGen)
    (he' : ∀ m, (e' m).IsGen)
    (tie : ∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)),
      LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧
      LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁))
    (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (hact : ∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) (had : ∀ a, MvPowerSeries.constantCoeff (ad a) = 1)
    (h0 : homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1)
    (hl : ∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m =
      jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))
    (ha : ∀ m (b : 𝓞 E), x' m ≫ t'.act.act b =
      homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) :
    IsFrameG t x0 d x F act ph1 ph2 sy ad e ↔ IsFrameG t' (𝟙 (Sp S)) d x' F act ph1 ph2 sy ad e' := by
  have laws : Laws := GlobalTheory.firstFiveLaws.1
  have cub := GlobalTheory.T.rigidifiedIso_maps_cubical_generator laws.globalFns E H X0 (Sp S) t t' x0 mp w hw hab
  have p1 := GlobalTheory.T.frame_firstPartialLaw_iff_pullback E H X0 t S x0 t' mp w hw d x x' hx cub e e' he he' tie F ph1
  have p2 := GlobalTheory.T.frame_second_partial_law_iff_pullback_alt E H X0 t S x0 t' mp w hw d x x' hx cub e e' he he' tie F ph2
  have p3 := GlobalTheory.T.frame_symmetry_iff_pullback E H X0 t S x0 t' mp w hw d x x' hx e e' he he' tie sy
  constructor
  · intro h
    refine ⟨he', ?_, ?_, p3.1 h.sy, fun a =>
      GlobalTheory.T.adjointSeries_frames_pullback E H X0 t S x0 t' mp w hw d x x' hx e e' he he' tie act ad a hact ha (h.ad a)⟩
    · first | exact (p1 hF hl).1 h.ph1 | exact p1.1 fun _ _ => h.ph1
    · first | exact (p2 hF hl).1 h.ph2 | exact p2.1 fun _ _ => h.ph2
  · intro h
    refine ⟨he, ?_, ?_, p3.2 h.sy, fun a =>
      GlobalTheory.T.frame_adjointness_series_of_pullback laws E H X0 t S x0 t' mp w hw d x x' hx hab h0 e e' he he' tie act ad a ha hact (had a) (h.ad a)⟩
    · first | exact (p1 hF hl).2 h.ph1 | exact p1.2 h.ph1 hF hl
    · first | exact (p2 hF hl).2 h.ph2 | exact p2.2 h.ph2 hF hl

end GlobalTheory.FrameMove

open GlobalTheory.FrameMove in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.chartFrameTransport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartFrameTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ _ T io y I d B B' tgT xT eT wPT hF hA h1 h2 hs had hch hfr hpr _ hrig
  letI := io.toAlgebra
  intro x x' hx2 hx1
  obtain ⟨wP, hwP, wP', hwP', tw2, tw1⟩ := GlobalTheory.T.integralFramedPoint_diagonalBiextensionIso_compatible E H Dw l Xo c T io y I wPT hpr
  have hab : IsAbelianScheme I.t'.G := GlobalTheory.T.isAbelianScheme_pullback_universalTriple E H Dw l Xo _ I.t' _ I.m1
  let ψ : T.V →+* T.Fr := algebraMap T.V T.Fr
  have hb : spMap ψ = spMap ψ ≫ 𝟙 (Sp T.V) := (Category.comp_id _).symm
  obtain ⟨x'', hx''⟩ : ∃ x'' : ∀ m, jOG (spMap ψ) d m 1 ⟶ I.G.G, ∀ m, (x' m).left ≫ I.m2.φ = (x'' m).left :=
    ⟨fun m => Over.homMk ((x' m).left ≫ I.m2.φ) (by
      have h := Over.w (x' m)
      rw [Category.assoc, I.m2.cart.1.w, ← Category.assoc, h]
      simp [ψ]), fun m => rfl⟩
  have hx3 : ∀ m, (x'' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (xT m).left :=
    fun m => (hx'' m).symm.trans (hx2 m)
  have eF : B'.G.F = fun i => MvPowerSeries.map ψ (B.G.F i) := funext hF
  have eA : B'.A.act = fun a i => MvPowerSeries.map ψ (B.A.act a i) := funext fun a => funext (hA a)
  have ead : B'.ad = fun a => MvPowerSeries.map ψ (B.ad a) := funext had

  obtain ⟨e'', he'', hc''⟩ := GlobalTheory.T.exists_frames_coefficientRing_baseChange E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3 eT hfr.gen
  have fr'' : IsFrameG I.G (spMap ψ) d x'' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e'' := by
    rw [eF, eA, ead, h1, h2, hs]
    exact GlobalTheory.T.isFrameG_coefficientRing_baseChange E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3 eT e'' hfr.gen he'' hc'' _ _ _ _ _ _ hfr
  have rig'' : Rig0G I.G (spMap ψ) d x'' B'.A.act e'' wPT := by
    rw [eA]
    exact GlobalTheory.T.rigidificationAtOrigin_baseChange_alt E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3 eT e'' hfr.gen he'' hc'' _ wPT hpr.1 hrig
  obtain ⟨z'', l'', a''⟩ := GlobalTheory.T.jetPoints_unit_law_action_baseChange E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3

  obtain ⟨z', l', a'⟩ := GlobalTheory.T.jetPoints_unit_law_action_iff_pullback E H _ I.G T.Fr _ I.t' I.m2 I.w2 I.rig2 d x'' x' hx''
  have h0 := z'.1 (z'' hch.zero) 0
  have hl := (l' B'.G.F).1 (by rw [eF]; exact l'' _ B.G.const hch.law)
  have ha := (a' B'.A.act).1 (by rw [eA]; exact a'' _ B.A.const hch.act)
  obtain ⟨e', he', tie2⟩ := GlobalTheory.T.cubeFrames_move_to_pullback_triple E H _ I.G T.Fr _ I.t' I.m2 I.w2 I.rig2 d x'' x' hx'' e'' he''
  have fr' := (isFrame_pull_iff I.G _ I.t' I.m2 I.w2 I.rig2 hab d x'' x' hx'' e'' e' he'' he' tie2 _ _ _ _ _ _
    B'.G.const B'.A.const (ad_const B') h0 hl ha).1 fr''
  have rig' := (GlobalTheory.T.rigidificationAtOrigin_iff_pullback E H _ I.G T.Fr _ I.t' I.m2 I.w2 I.rig2 d x'' x' hx'' e'' e' he'' he' tie2 wPT wP' hpr.1
    hwP' tw2 _ h0 B'.A.const).1 rig''

  obtain ⟨e, he, tie1⟩ := GlobalTheory.T.exists_cubeFrames_from_pullback_triple E H _ Xo.univ.t T.Fr _ I.t' I.m1 I.w1 I.rig1 d x x' hx1 e' he'
  have fr := (isFrame_pull_iff Xo.univ.t _ I.t' I.m1 I.w1 I.rig1 hab d x x' hx1 e e' he he' tie1 _ _ _ _ _ _
    B'.G.const B'.A.const (ad_const B') h0 hl ha).2 fr'
  have rig := (GlobalTheory.T.rigidificationAtOrigin_iff_pullback E H _ Xo.univ.t T.Fr _ I.t' I.m1 I.w1 I.rig1 d x x' hx1 e e' he he' tie1 wP wP'
    ((isPrim_iff wP).1 hwP).1 hwP' tw1 _ h0 B'.A.const).2 rig'
  refine ⟨e, wP, (isFrame_iff y.1 d x _ _ _ _ _ _ e).2 fr, hwP, rig, ⟨e', fun m => ⟨he' m, ?_, tie1 m⟩⟩,
    wP', hwP', tw2, tw1⟩
  obtain ⟨c₂, k₁, k₂⟩ := tie2 m
  exact ⟨c₂, corr_trans I.G.PP.isLB k₁ (hc'' m), k₂⟩
