import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusLabelsShapeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimesStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelBlockPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLineStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2Statement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ImageCptReflOfGenPt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubsetStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightBoundOfArithVarStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonThreeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonTwoStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoEqRelinedIsometricVertStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.Link

theorem mCoordIdeal_map {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (i : Ω₀ →+* Ω) (y₀ : (Σ k, J k) → Ω₀) : mCoordIdeal (fun p => i (y₀ p)) = mCoordIdeal y₀ := by
  have key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp]; simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap _ f = 0
  rw [key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

theorem imageZ_of_restr {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
    [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
    {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (hy : ∀ p, y (v p) = i (y₀ p)) :
    imageZ v (mCoordIdeal y) = mCoordIdeal y₀ := by
  rw [← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v hv y, ← mCoordIdeal_map i y₀]
  congr 1
  funext p
  exact hy p

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]

open Classical in

theorem link_step (hSeg : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement) (hM3 : HodgeLatticeFlagBound) (hTv : TrivFlagOnHodge)
    (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (hS : S₀ ⊆ S) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S₀)
    (hom₀ : o₀.𝔐.OmVB) (hom₁ : o₁.𝔐.OmVB) (hR : ∀ p ∈ S₀, o₀.𝔐.R p = o₁.𝔐.R p) (hdeg : oR.Fl.deg = 1)
    (hJ₀ : o₀.Re.J = ⊤) (hJ₁ : o₁.Re.J = ⊤) (hJR : oR.Re.J = ⊤)
    (hc₀ : M₀.Converges II) (hc₁ : M₁.Converges II) (h2 : ∀ p ∈ S, p ∉ S₀ → p ≠ 2)
    (φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H)) (hφ : ∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) :
    ∃ (M : RootModel (CMType H) (D.p + D.q)) (R : SecondRoots M),
      M.Converges II ∧ R.model.Converges II ∧
      (∀ F : RP (CMType H) (D.p + D.q), M.PP II (toA F) = M₀.PP II (toA F)) ∧
      (∀ F : RP (CMType H) (D.p + D.q), R.model.PP II (toA F) = M₁.PP II (toA F)) ∧
      (∀ F : RP (CMType H) (D.p + D.q), M.geoFun (toA F) = M₀.geoFun (toA F)) ∧
      R.IsChange ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧
      R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  obtain ⟨Ω, _, _, K, _, J, _, y, κ₀, v₀, κ₁, v₁, κR, vR, i₀, i₁, iR, 𝔐, Fl, hv₀, hv₁, hvR, hy₀, hy₁, hyR, hg₀, hg₁,
    hd0, hdeq, ⟨h, hvb, hsub, hl₀⟩, hl₁, hfr⟩ := GlobalTheory.T.root_origin_comparison_subset E H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR hS hdisc hom₀ hom₁ hR hdeg
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  haveI : Nonempty K := ⟨κ₀ o₀.k₀⟩
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl hβ
  have ha : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) := harith
  have hδ : 0 < IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) * M₀.δ :=
    Nat.mul_pos (Nat.pos_of_ne_zero hd0) M₀.δ_pos
  let M : RootModel (CMType H) (D.p + D.q) := pullModel M₀ y ha hbir hv₀ _ hδ
  obtain ⟨f, g, hfg, hvert⟩ := GlobalTheory.T.flag_height_bound_of_arith_var E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐 _ ha Fl S₀ h hvb hsub _ _ _ _ hl₀ hl₁
  let Sp : Finset Nat.Primes := (S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn
  let Tr : CMType H × Fin (D.p + D.q) → LocPair J ℤ Unit := fun r =>
    ⟨fun _ => pullDeg κ₀ (M₀.xdeg r), fun _ => pullDeg κ₁ (M₁.xdeg r), fun _ => f r, fun _ => g r⟩
  have hTr : ∀ r, (Tr r).IsVertOff (mCoordIdeal y) Sp := fun r _ => hvert r
  have htw : ∀ (t : ℝ) (r : CMType H × Fin (D.p + D.q)), ∃ A' : HermLine J, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧
      (Tr r).IsIsometric (mCoordIdeal y) (fun _ => M.x t r) (fun _ => A') := fun t r =>
    GlobalTheory.T.exists_isometric_herm_line K J (mCoordIdeal y) _ ha Sp (Tr r) (hTr r) (M.x t r) (M.x_deg t r) (M.x_smooth t r) (M.x_conj t r)
  choose tw tws twc twi using htw
  have ht₀ : 0 < Sys.t₀ := (Sys.reg none).1
  let x' : ℝ → CMType H × Fin (D.p + D.q) → HermLine J := fun t r =>
    if 0 < t ∧ t ≤ Sys.t₀ then pullHerm hv₁ (M₁.x t r) else tw t r
  have hx'deg : ∀ t r, (x' t r).a = pullDeg κ₁ (M₁.xdeg r) := fun t r => by
    by_cases ht : 0 < t ∧ t ≤ Sys.t₀
    · simp only [x', if_pos ht]
      show pullDeg κ₁ (M₁.x t r).a = _
      rw [M₁.x_deg]
    · simp only [x', if_neg ht]
      exact ((twi t r) ()).2.1
  have hx's : ∀ t r, IsSmoothHerm (x' t r) := fun t r => by
    by_cases ht : 0 < t ∧ t ≤ Sys.t₀
    · simp only [x', if_pos ht]
      exact Chg.isSmoothHerm_pull hv₁ (M₁.x_smooth t r)
    · simp only [x', if_neg ht]
      exact tws t r
  have hx'c : ∀ t r, IsConjInvariantH (x' t r) := fun t r => by
    by_cases ht : 0 < t ∧ t ≤ Sys.t₀
    · simp only [x', if_pos ht]
      exact Chg.isConj_pull hv₁ (M₁.x_conj t r)
    · simp only [x', if_neg ht]
      exact twc t r
  let R : SecondRoots M :=
    { xdeg := fun r => pullDeg κ₁ (M₁.xdeg r), x := x', x_deg := hx'deg, x_smooth := hx's, x_conj := hx'c, f := f, g := g }
  have hTL : Fl.TwoLevels S₀ (⟨fun r => pullDeg κ₀ (M₀.xdeg r), fun r => pullDeg κ₁ (M₁.xdeg r), f, g⟩ :
      LocPair J ℤ (CMType H × Fin (D.p + D.q))) :=
    ⟨h, hvb, hsub, _, _, hl₀, hl₁, hfg, hvert⟩
  obtain ⟨hvert', hloc⟩ := GlobalTheory.T.hodge_comp_root_model_primes hSeg hM3 hTv E H D l Xo c _ _ Y S S₀ M 𝔐 Fl R hTL
    (fun p hp hp' => ⟨hfr p hp, h2 p hp hp', fun hd => hp' (hdisc p (𝔐.S_prime p hp) hd)⟩) φ hφ
  have hIso : ∀ t, 0 < t → R.pairs.IsIsometric M.P (M.x t) (R.x t) := fun t ht r => by
    refine ⟨M.x_deg t r, R.x_deg t r, fun z hz => ?_⟩
    by_cases ht' : t ≤ Sys.t₀
    · obtain ⟨⟨bf, bg, hbf, hbg, hb⟩, hfP, hgP, -⟩ := hvert r
      have e1 : (R.x t r).h z = (M₁.x t r).h (fun p => z (v₁ p)) := by
        show (x' t r).h z = _
        simp only [x', if_pos (And.intro ht ht')]
        rfl
      rw [e1]
      exact GlobalTheory.T.root_origin_height_comparison_three E H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR Ω K J y κ₀ v₀ κ₁ v₁ κR vR i₀ i₁ iR hv₀ hv₁ hvR hy₀ hy₁ hyR hg₀ hg₁
        hJ₀ hJ₁ hJR hdeg ha r (f r) (g r) bf bg hbf hbg hb hfP hgP (hfg r) t ht ht' z hz
    · have e1 : R.x t r = tw t r := by
        show x' t r = _
        simp only [x', if_neg (fun hh : 0 < t ∧ t ≤ Sys.t₀ => ht' hh.2)]
      rw [e1]
      exact ((twi t r) ()).2.2 z hz

  obtain ⟨T, hTx, hTx', hTv', hTi⟩ := GlobalTheory.T.root_origin_height_comparison_two E H D l Xo c Y S₀ S M₀ M₁ Sys Fx o₀ o₁ Ω K J y κ₀ v₀ κ₁ v₁ i₀ i₁ hv₀ hv₁ hy₀ hy₁
    (by rw [hg₀, hg₁]) ha
  have hAs := Chg.isSmoothHerm_pull hv₁ M₁.A_smooth
  have hAc := Chg.isConj_pull hv₁ M₁.A_conj
  let Rm := R.model
  let R2 := reline Rm Rm.xdeg Rm.x Rm.x_deg Rm.x_smooth Rm.x_conj (pullHerm hv₁ M₁.A) hAs hAc
  let M₁' := reline Rm Rm.xdeg (fun t r => pullHerm hv₁ (M₁.x t r))
    (fun t r => by
      show pullDeg κ₁ (M₁.x t r).a = _
      rw [M₁.x_deg]
      rfl) (fun t r => Chg.isSmoothHerm_pull hv₁ (M₁.x_smooth t r))
    (fun t r => Chg.isConj_pull hv₁ (M₁.x_conj t r)) (pullHerm hv₁ M₁.A) hAs hAc
  have hkA : M₁'.kA = M₁.kA := by
    show M₀.kA = M₁.kA
    rw [o₀.kA_eq, o₁.kA_eq]
  haveI : CharZero M₁'.Ω := ‹CharZero Ω›
  obtain ⟨-, hPP₁, hCv₁, -⟩ := GlobalTheory.T.root_model_block_pullback _ _ M₁ M₁' II hII κ₁ v₁ hv₁ (imageZ_of_restr i₁ M₁.y y hv₁ hy₁)
    (fun t r => by
      cases r with
      | none => exact ⟨rfl, fun _ => rfl⟩
      | some r => exact ⟨rfl, fun _ => rfl⟩) hkA hdeq
  have hev : ∀ m, ∀ᶠ t in 𝓝[>] (0 : ℝ), M₁'.arMono II t m = Rm.arMono II t m := fun m => by
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
    rw [GlobalTheory.T.arMono_eq_relined_isometric_vert _ _ Rm II hII (pullHerm hv₁ M₁.A) hAs hAc T hTv' hTi t m]
    refine arMono_reline Rm II t m (fun r => ?_) rfl
    show pullHerm hv₁ (M₁.x t r) = x' t r
    simp only [x', if_pos (And.intro ht.1 ht.2.le)]
  have hCv : Rm.Converges II := fun m => by
    obtain ⟨L, hL⟩ := hCv₁ hc₁ m
    exact ⟨L, hL.congr' (hev m)⟩
  haveI : CharZero M.Ω := ‹CharZero Ω›
  obtain ⟨-, hPP₀, hCv₀, hgeo⟩ := GlobalTheory.T.root_model_block_pullback _ _ M₀ M II hII κ₀ v₀ hv₀ (imageZ_of_restr i₀ M₀.y y hv₀ hy₀)
    (fun t r => by
      cases r with
      | none => exact ⟨rfl, fun _ => rfl⟩
      | some r => exact ⟨rfl, fun _ => rfl⟩) rfl rfl
  refine ⟨M, R, hCv₀ hc₀, hCv, fun F => by rw [hPP₀], fun F => ?_, fun F => by rw [hgeo], ⟨hvert', hIso⟩, hloc⟩
  rw [← hPP₁]
  refine (Indep.pp_toA_eq_of_tendsto M₁' Rm II (hCv₁ hc₁) (fun m => ?_) F).symm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev (m.mapDomain some)] with t ht
  rw [ht, sub_self]

end GlobalTheory.CompanionTheory.Ar.Top.Link

namespace GlobalTheory.CompanionTheory.Ar.Top.Link

theorem goodOrigin_linked : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → PB.AgreementPos → HodgeLatticeFlagBound → TrivFlagOnHodge → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), FrobShape (fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ)) ∧ Num.LinkedTower T II φ := by
  intro _ hA hM3 hTv hG E _ _ _ _ H D Xo l c Y _ T o II _ hX hII _ _
  obtain ⟨-, -, -, hSeg, -, -, -, -, -, hIn, -⟩ := hG
  obtain ⟨φ, hφ, hsh⟩ := GlobalTheory.T.frobenius_labels_shape E (fun a b => IsMulCommutative.is_comm.comm a b) H l c
  refine ⟨φ, hsh, ?_⟩
  intro B₀ B h2 hB a
  have hConv : T.Conv II := (GlobalTheory.T.real_tower_conv_I2 hA hIn II hII _ _ T (realOf o.toTowerOrigin)).1
  have hmem : ∀ (B' p : ℕ), p ∈ o.S B' ↔ p.Prime ∧ (p ≤ B' ∨ p ∈ T.bad) := fun B' p => o.S_iff B' p
  have hsub : o.S B₀ ⊆ o.S B := fun p hp => by
    obtain ⟨h1, h3⟩ := (hmem _ _).1 hp
    exact (hmem _ _).2 ⟨h1, h3.imp (fun h => h.trans hB) id⟩
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.S B₀ := fun p hp hd =>
    (hmem _ _).2 ⟨hp, Or.inr ((o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩)⟩
  have hRR : ∀ p ∈ o.S B₀, (o.Or B₀ a).𝔐.R p = (o.Or B a).𝔐.R p := fun p hp => by
    rw [hX.2 B₀ a p hp, hX.2 B a p (hsub hp)]
  have h2' : ∀ p ∈ o.S B, p ∉ o.S B₀ → p ≠ 2 := fun p _ hp' e => by
    subst e
    exact hp' ((hmem _ _).2 ⟨Nat.prime_two, Or.inr T.two_mem⟩)
  obtain ⟨M, R, c1, c2, c3, c4, c5, c6, c7⟩ := link_step hSeg hM3 hTv (o.S B₀) (o.S B) (T.M B₀ a) (T.M B a) (o.R a) (o.Sys a) (o.Fx a)
    (o.Or B₀ a) (o.Or B a) (o.refOr a) II hII hsub hdisc (o.omVB B₀ a) (o.omVB B a) hRR (o.ref_deg a) (o.smooth B₀ a).1
    (o.smooth B a).1 (o.ref_top a) (hConv B₀ a) (hConv B a) h2' φ (fun p hp _ => hφ p ((hmem _ _).1 hp).1)
  refine ⟨M, R, _, fun p => ?_, c1, c2, c3, c4, c5, c6, ?_⟩
  · refine Finset.mem_preimage.trans ?_
    rw [Finset.mem_sdiff, hmem, hmem]
    have hp : (p : ℕ).Prime := p.2
    constructor
    · rintro ⟨⟨-, h3⟩, h4⟩
      have h5 : ¬ ((p : ℕ) ≤ B₀ ∨ (p : ℕ) ∈ T.bad) := fun h => h4 ⟨hp, h⟩
      push_neg at h5
      exact ⟨h5.1, h3.resolve_right h5.2, h5.2⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨hp, Or.inl h4⟩, fun h => h.2.elim (fun h' => absurd h' (not_le.2 h3)) h5⟩
  · rw [o.j_eq]
    exact c7

end GlobalTheory.CompanionTheory.Ar.Top.Link
