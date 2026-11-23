import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirstStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecondStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumLatticeWedgeComapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomainStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThirdStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem mem_Vgen (𝔐 : HodgeCpt Y S₀ Dc.y) (t : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {x : 𝔐.Li}
    (hx : x ∈ 𝔐.V t p) : x ∈ 𝔐.Vgen t := by
  obtain ⟨U, hU, b, hs, hf⟩ := 𝔐.vb t p trivial
  have e : 𝔐.V t p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p trivial hU).2
  have hx' : x ∈ Submodule.span (regAt 𝔐.ξ p) (Set.range b) := e ▸ hx
  clear hx
  show x ∈ 𝔐.Vgen t
  have hs' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t := hs
  rw [← hs']
  induction hx' using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | smul a x _ h => exact Submodule.smul_mem _ (a : Ω) h

theorem disjoint_blocks (Or : CptOrigin Y S₀ Dc Hd) (τ : CMType H) :
    Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := by
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S₀ Ω K J Dc.y Or.𝔐
    (FaithfulSMul.algebraMap_injective _ _)
  exact hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)

theorem exists_smallPart (Or : CptOrigin Y S₀ Dc Hd) {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) :
    ∃ s, Or.IsSmallPart d s := by
  have h : ∀ τ k, ∃ x, x ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - x ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have hm : Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 hm
    exact ⟨e, he, by rw [← hae]; simpa using ha⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem frames (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (d : MuFrameAt Hd w) {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li}
    (hs : Or.IsSmallPart d s) (τ : CMType H) (h : genPt Or.𝔐.ξ ⤳ centre z) :
    (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt (d.b τ) ⟨centre z, h⟩ ∧
    (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩ ∧
    ∀ k, Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩ := by
  have hfr := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ d.c d.f (d.b τ) h hw (d.adapted τ).1 d.inDom
  have hb := GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
    (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (d.b τ) (s τ) ⟨centre z, h⟩ (Or.i_inj τ)
    (Or.i_range τ) (disjoint_blocks Or τ) (fun _ hx => mem_Vgen _ _ _ hx) (fun _ hx => mem_Vgen _ _ _ hx) hfr
    (by rw [(d.adapted τ).2.2, Or.F_eq τ]) (hs τ)
  exact ⟨hfr, hb.1, hb.2.1⟩

theorem norm_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s) :
    ∃ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) ∧ (∀ τ, (Γ τ).PosDef) ∧
      d.norm = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have key : ∀ τ, ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) Γ ∧ Γ.PosDef ∧
        quotNormSq Dc.j_le_N (gramAt (Dc.h τ) (d.b τ) w) = Γ.det.re := fun τ => by
    obtain ⟨h1, h2, h3⟩ := frames Or hw d hs τ h
    obtain ⟨G, hG, hGp⟩ := GlobalTheory.T.component_data_hodge_third E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) h hi h1
    rw [GlobalTheory.T.intersection_system_hodge_data E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ (d.b τ) h G hw hi h1 hG]
    exact GlobalTheory.T.intersection_system_hodge_bound E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) (s τ) h G hi h1
      ((d.adapted τ).2.2) (fun k => (hs τ k).1) h3 h2 hG hGp
  choose Γ h1 h2 h3 using key
  refine ⟨Γ, h1, h2, ?_⟩
  unfold MuFrameAt.norm
  simp_rw [h3]

theorem det_re_pos {n : ℕ} {Γ : Matrix (Fin n) (Fin n) ℂ} (h : Γ.PosDef) : 0 < Γ.det.re :=
  (Complex.pos_iff.1 h.det_pos).1

theorem phMu_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ}
    (hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      (∑ τ, Real.log (Γ τ).det.re) / 2 := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  haveI : CharZero Ω := algebraRat.charZero Ω
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  obtain ⟨cv, hcv, hwc⟩ := exists_eq_smul_orbitRep w
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = orbitRep w := ⟨_, rfl⟩
  rw [← hw₀def] at hwc
  have hwk : ∀ p, w p = cv p.1 * w₀ p := fun p => congrFun hwc p
  have hw₀ : CoordsAt Or.𝔐.ξ Dc.y z w₀ := by
    have := RootHt.ArchB.coordsAt_smul (fun k => (cv k)⁻¹) (fun k => inv_ne_zero (hcv k)) hw
    convert this using 1
    funext p
    rw [hwc]
    simp [torusSmul, inv_mul_cancel_left₀ (hcv p.1)]
  have hval : ∀ (a : Ω) (v : ℂ), IsValueAt Dc.y a w v ↔ IsValueAt Dc.y a w₀ v := fun a v =>
    ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw a v).symm).trans
      (GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w₀ h hw₀ a v)
  have hne₀ : ∀ k, w₀ ⟨k, d.c k⟩ ≠ 0 := fun k h0 => d.inDom.1 k (by rw [hwk ⟨k, d.c k⟩]; simp [h0])
  let d₁ : MuFrameAt Hd w₀ :=
    { c := d.c, f := d.f
      inDom := ⟨hne₀, d.inDom.2.imp fun v hv => ⟨(hval _ _).1 hv.1, hv.2⟩⟩
      b := d.b, adapted := d.adapted, u := d.u, unit := d.unit, eq := d.eq }
  have hs₁ : Or.IsSmallPart d₁ s := hs
  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hmc₀ : w₀ ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie w₀).2 ⟨z, h, hw₀⟩
  have hu₀ : valAt Dc.y d.u w₀ = valAt Dc.y d.u w :=
    valAt_eq hmc₀ ((hval _ _).1 ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw _ _).1 hu.2))

  have hne := GlobalTheory.T.component_data_hodge_first E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hw₀
  obtain ⟨s₀, hs₀⟩ := exists_smallPart Or hne.some
  obtain ⟨Γ₀, g₀, p₀, n₀⟩ := norm_eq Or hw₀ hi hne.some hs₀
  obtain ⟨Γ₁, g₁, p₁, -⟩ := norm_eq Or hw₀ hi d₁ hs₁
  have e₁ : Γ₁ = Γ := funext fun τ =>
    GlobalTheory.T.gram_matrix_change_frame E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z _ (s τ) _ _ hpol (g₁ τ) (hΓ τ)
  subst e₁
  have hind := GlobalTheory.T.intersection_system_hodge_degree E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hne.some d₁ s₀ s Γ₀ Γ₁ hw₀ hi hs₀ hs₁ g₀ g₁ p₀
  have hF : muMetric Hd w₀ = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    unfold muMetric
    rw [dif_pos hne, n₀, hind]
    show ‖valAt Dc.y d.u w₀‖ * _ * _ = _
    rw [hu₀]
  have hA : 0 < ‖valAt Dc.y d.u w‖ := norm_pos_iff.2 hu.1
  have hsq : 0 < ∏ τ, Real.sqrt (Γ₁ τ).det.re :=
    Finset.prod_pos fun τ _ => Real.sqrt_pos.2 (det_re_pos (p₁ τ))
  have hprod₀ : 0 < ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hne₀ k)) _
  have hprod : 0 < ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _
  have hpos : 0 < muMetric Hd w₀ := by
    rw [hF]
    positivity
  have hnz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => ⟨d.c k, d.inDom.1 k⟩
  have hh : (muLine Hd).h w = (∏ k, ‖cv k‖ ^ Hd.aMu k) * muMetric Hd w₀ := by
    subst hw₀def
    exact TopNPoly.hermOfFun_h_smul hcv hwc hnz hpos
  have hcw : (∏ k, ‖cv k‖ ^ Hd.aMu k) * ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k = ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← norm_mul]
    rw [hwk ⟨k, d.c k⟩]
  have hfin : (muLine Hd).h w = (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    rw [hh, hF, ← hcw]
    ring
  show Real.log ((muLine Hd).h w) = _
  rw [hfin, Real.log_mul (by positivity) hsq.ne', Real.log_prod (fun τ _ => (Real.sqrt_pos.2 (det_re_pos (p₁ τ))).ne')]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun τ _ => Real.log_sqrt (det_re_pos (p₁ τ)).le

theorem phMu_small : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  intro _ E _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hw
  have htie : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  refine ⟨GlobalTheory.T.component_data_hodge_first E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or z w hw, fun d => ⟨exists_smallPart Or d, fun s hs => ⟨
    fun τ h => (frames Or hw d hs τ h).2.1, ?_, fun hi Γ hΓ => phMu_eq Or hw hi d hs hΓ⟩⟩⟩
  exact (GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie (Or.𝔐.all _) hw d.inDom d.unit).1

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
