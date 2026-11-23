import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightRightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRatioProductFormula
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointAltBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralLatticeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLatticeEigenCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorLatticeCoordDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFromLocalMatricesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

section Field

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L : Type} [Field L]

theorem centre_field_map (zL : Sp L ⟶ X) (e : L →+* ℂ) : centre (spMap e ≫ zL) = centre zL := by
  refine (Scheme.Hom.comp_apply (spMap e) zL _).trans ?_
  exact congrArg zL (Subsingleton.elim _ _)

theorem val_descend (ξ : Sp Ω ⟶ X) (zL : Sp L ⟶ X) (e : L →+* ℂ) {a : Ω} {r : ℂ}
    (h : ValAt ξ (spMap e ≫ zL) a r) : ∃ t : L, ValAt ξ zL a t ∧ e t = r := by
  have hc : centre zL = centre (spMap e ≫ zL) := (centre_field_map zL e).symm
  obtain ⟨h', s, hs, rfl⟩ := h
  have h'' : genPt ξ ⤳ centre zL := hc ▸ h'
  have hv : ValAt ξ zL a (Scheme.stalkClosedPointTo zL |>.hom (X.presheaf.stalkSpecializes (specializes_of_eq hc) s)) :=
    ⟨h'', _, (genMap_stalkSpecializes ξ hc h' h'' s).trans hs, rfl⟩
  exact ⟨_, hv, CxVal.unique (valAt_of_field_map ξ zL _ e rfl hv) ⟨h', s, hs, rfl⟩⟩

theorem coords_field_map (ξ : Sp Ω ⟶ X) {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {zL : Sp L ⟶ X}
    {w : (Σ k, J k) → L} (hw : CoordsAt ξ y zL w) (e : L →+* ℂ) :
    CoordsAt ξ y (spMap e ≫ zL) (fun p => e (w p)) := by
  refine ⟨fun k => (hw.1 k).imp fun c hc => hc.map e, fun k c hc => ?_⟩
  have hne : w ⟨k, c⟩ ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨hy, hi⟩ := hw.2 k c (isUnit_iff_ne_zero.2 hne)
  refine ⟨hy, fun i => ?_⟩
  obtain ⟨ρ, hρ, hr⟩ := hi i
  exact ⟨e ρ, valAt_of_field_map ξ zL _ e rfl hρ, by simp only [hr, map_mul]⟩

theorem not_inFibre [CharZero Ω] [CharZero L] (ξ : Sp Ω ⟶ X) (zL : Sp L ⟶ X) (h : genPt ξ ⤳ centre zL) {p : ℕ}
    (hp : p ≠ 0) : ¬ InFibre ξ p ⟨centre zL, h⟩ := by
  unfold InFibre
  rw [not_not]
  have hv : ValAt ξ zL (p : Ω) (p : L) := ⟨h, (p : X.presheaf.stalk (centre zL)), map_natCast _ _, map_natCast _ _⟩
  exact ⟨Nat.cast_ne_zero.2 hp, ⟨(p : X.presheaf.stalk (centre zL)), map_natCast _ _⟩,
    GlobalTheory.CompanionTheory.Ar.RootHt.inv_mem_regAt_of_isUnit h hv (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hp))⟩

end Field

section Datum

theorem datum (hG : Top.Given) (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E)
    (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)]
    [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ)
    (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (zL : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L)
    (hw : CoordsAt Or.𝔐.ξ Dc.y zL w) :
    ∃ (cc : (k : K) → J k) (f : Ω) (b : ∀ τ, Fin Dc.N → W τ) (u : Ω) (uL : L)
      (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li),
      (∀ k, w ⟨k, cc k⟩ ≠ 0) ∧
      (∀ τ, IsAdaptedFrame Dc.y (Dc.W τ) (Hd.F τ) Dc.j_le_N cc f (b τ)) ∧ IsUnitOn Dc.y cc f u ∧
      Hd.Λ = (u * chartMono Dc.y cc Hd.aMu) • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (b τ)) ∧
      uL ≠ 0 ∧ ValAt Or.𝔐.ξ zL u uL ∧ (∀ e : L →+* ℂ, InFrameDomain Dc.y cc f fun p => e (w p)) ∧
      (∀ e : L →+* ℂ, valAt Dc.y u (fun p => e (w p)) = e uL) ∧
      (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) ∧
      ∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre zL, Or.𝔐.all _⟩ := by
  classical
  obtain ⟨e₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have hw₀ := coords_field_map Or.𝔐.ξ hw e₀
  obtain ⟨⟨d⟩, hall⟩ := GlobalTheory.T.intersection_system_weight_right hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or _ _ hw₀
  obtain ⟨⟨s, hs⟩, hs2⟩ := hall d
  obtain ⟨hfr, hu0, -⟩ := hs2 s hs
  have hT := Or.𝔐.tie
  have tv : ∀ (e : L →+* ℂ) (a : Ω) (r : ℂ), ValAt Or.𝔐.ξ (spMap e ≫ zL) a r ↔ IsValueAt Dc.y a (fun p => e (w p)) r :=
    fun e a r => GlobalTheory.T.valAt_iff_value_at _ _ _ K J _ hT _ _ (Or.𝔐.all _) (coords_field_map Or.𝔐.ξ hw e) a r

  obtain ⟨vf, hvf, hvf0⟩ := d.inDom.2
  obtain ⟨fL, hfL, hfe⟩ := val_descend _ _ _ ((tv e₀ _ _).2 hvf)
  have hfL0 : fL ≠ 0 := fun h0 => hvf0 (by rw [← hfe, h0, map_zero])

  have hex : ∃ v, IsValueAt Dc.y d.u (fun p => e₀ (w p)) v := by
    by_contra hn
    exact hu0 (by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_neg hn])
  have hu1 : valAt Dc.y d.u (fun p => e₀ (w p)) = hex.choose := by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_pos hex]
  obtain ⟨uL, huL, hue⟩ := val_descend _ _ _ ((tv e₀ _ _).2 hex.choose_spec)
  have huL0 : uL ≠ 0 := fun h0 => hu0 (by rw [hu1, ← hue, h0, map_zero])
  refine ⟨d.c, d.f, d.b, d.u, uL, s, fun k h0 => ?_, d.adapted, d.unit, d.eq, huL0, huL, fun e => ⟨fun k h0 => ?_, ?_⟩, fun e => ?_,
    hs, fun τ => ?_⟩
  · exact d.inDom.1 k (by simp [h0])
  · have hne : w ⟨k, d.c k⟩ ≠ 0 := fun h1 => d.inDom.1 k (by simp [h1])
    exact hne (by simpa using h0)
  · exact ⟨e fL, (tv e _ _).1 (valAt_of_field_map _ zL _ e rfl hfL), by simpa using hfL0⟩
  · have h1 : ValAt Or.𝔐.ξ (spMap e ≫ zL) d.u (e uL) := valAt_of_field_map _ zL _ e rfl huL
    have hex' : ∃ v, IsValueAt Dc.y d.u (fun p => e (w p)) v := ⟨_, (tv e _ _).1 h1⟩
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_pos hex']
    exact CxVal.unique ((tv e _ _).2 hex'.choose_spec) h1
  · have hq : (⟨centre (spMap e₀ ≫ zL), Or.𝔐.all _⟩ : Cpt Or.𝔐.ξ) = ⟨centre zL, Or.𝔐.all _⟩ :=
      Subtype.ext (centre_field_map zL e₀)
    exact hq ▸ hfr τ (Or.𝔐.all _)

end Datum

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem cm_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : Nonempty (CMType H) := by
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hr : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : (τ₀ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hr, H.sqrt_neg_disc_sq]; simp
  have hre : H.rt0.re = 0 := by
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
    simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.natCast_im,
      Complex.natCast_re, neg_zero] at h2 h3
    have h4 : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exfalso
      rw [h] at h3
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact ⟨⟨τ₀, h⟩⟩
  · refine ⟨⟨(starRingEnd ℂ).comp τ₀, ?_⟩⟩
    simp [h, hconj]

theorem logIdx_congr {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (F : Submodule R V) {A₁ A₂ : Type}
    (b : A₁ → V) (b' : A₂ → V) (h : Set.range b = Set.range b') : logIdx F b = logIdx F b' := by
  unfold logIdx
  rw [h]

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem g_height : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (w : (Σ k, J k) → L) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), Or.Good → CoordsAt Or.𝔐.ξ Dc.y (spMap (algebraMap (𝓞 L) L) ≫ z) w → Or.𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → ∃ x : (L →+* ℂ) → ℝ, (∀ e : L →+* ℂ, Or.PhiWeight (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) (x e)) ∧ Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L w + (∑ e : L →+* ℂ, x e) / Module.finrank ℚ L = -A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B L _ _ z P V _ _ _ _ MV A w r k v q hGood hw hLP hO hAd
  classical
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨cc, f, b, u, uL, s, hc, had, hun, heq, huL, hval, hdom, hvalC, hsm, hfr⟩ :=
    datum hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or L (spMap (algebraMap (𝓞 L) L) ≫ z) w hw

  have hS₀ : ∀ p ∈ S₀, p ≠ 0 := fun p hp => (Or.𝔐.S_prime p hp).ne_zero
  have hvs := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hS' : ∀ p ∈ S₀ ∪ Dc.SB B, p ≠ 0 := fun p hp => (hvs.1 p hp).ne_zero
  have hV : ∀ t', Or.𝔐.V t' ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), Or.𝔐.all _⟩ =
      Or.𝔐.dR t' ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), Or.𝔐.all _⟩ := fun t' =>
    Lat.patch_of_not _ _ _ fun p hp => not_inFibre _ _ _ (hS₀ p hp)
  have hVS : ∀ t', Or.𝔐.VS (S₀ ∪ Dc.SB B) t' ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), Or.𝔐.all _⟩ =
      Or.𝔐.dR t' ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), Or.𝔐.all _⟩ := fun t' =>
    Lat.patch_of_not _ _ _ fun p hp => not_inFibre _ _ _ (hS' p hp)
  have hdr : ∀ τ, (Or.𝔐.dR (Or.sm τ)).IsFrameAt (s τ) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), Or.𝔐.all _⟩ :=
    fun τ => ⟨(hfr τ).1, (hV _).symm.trans (hfr τ).2⟩
  have hfrS : ∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt (s τ)
      ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), Or.𝔐.all _⟩ :=
    fun τ => ⟨(hfr τ).1, (hVS _).trans (hdr τ).2⟩
  choose sL hsLv hsLi hsLs using fun τ => GlobalTheory.T.abelian_part_integral_point_alt E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L z P V MV A (Or.sm τ) _ (s τ) hLP (hdr τ)

  obtain ⟨τ₀⟩ := cm_nonempty H
  have hrk : r + k = Dc.N - Dc.j := by
    have h1 := finrank_span_eq_card (hAd τ₀).1.1
    have h2 := finrank_span_eq_card (hsLi τ₀)
    rw [(hAd τ₀).1.2] at h1
    rw [hsLs τ₀, h1] at h2
    simpa using h2

  have hCex : ∀ τ, ∃ C : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) L,
      (∀ i, A.fam (Or.sm τ) v (q τ) i = ∑ j, C j (Fin.cast hrk i) • sL τ j) ∧ C.det ≠ 0 := by
    intro τ
    have hmem : ∀ i : Fin (Dc.N - Dc.j), ∃ a : Fin (Dc.N - Dc.j) → L,
        ∑ j, a j • sL τ j = A.fam (Or.sm τ) v (q τ) (Fin.cast hrk.symm i) := by
      intro i
      have : A.fam (Or.sm τ) v (q τ) (Fin.cast hrk.symm i) ∈ Submodule.span L (Set.range (sL τ)) := by
        rw [hsLs τ, ← (hAd τ).1.2]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact (Submodule.mem_span_range_iff_exists_fun L).1 this
    choose a ha using hmem
    refine ⟨Matrix.of fun j i => a i j, fun i => ?_, fun h0 => ?_⟩
    · have := ha (Fin.cast hrk i)
      simpa using this.symm
    · obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have h3 : ∑ i, x i • A.fam (Or.sm τ) v (q τ) (Fin.cast hrk.symm i) = 0 := by
        have : ∀ i, x i • A.fam (Or.sm τ) v (q τ) (Fin.cast hrk.symm i) = ∑ j, (x i * a i j) • sL τ j := by
          intro i
          rw [← ha i, Finset.smul_sum]
          simp [smul_smul]
        simp only [this]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.sum_smul]
        have h4 := congrFun hx j
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h4
        rw [show ∑ i, x i * a i j = ∑ i, a i j * x i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, h4, zero_smul]
      have hli : LinearIndependent L fun i : Fin (Dc.N - Dc.j) => A.fam (Or.sm τ) v (q τ) (Fin.cast hrk.symm i) :=
        (hAd τ).1.1.comp _ (Fin.cast_injective _)
      exact hx0 (funext fun i => (Fintype.linearIndependent_iff.1 hli x h3 i))
  choose C hC1 hC2 using hCex

  have hvb : ∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsVB (Dc.N - Dc.j) (Or.𝔐.Vgen (Or.sm τ)) := by
    intro τ
    have := hvs.2.2.2 (Or.sm τ)
    rwa [Or.rk_sm] at this
  choose T T' b' hb1 hb2 hb3 hb4 hb5 hb6 using fun τ =>
    GlobalTheory.T.abelian_part_lattice_eigen_compat E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L z P V MV (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) _ _ (s τ) (sL τ)
      (hvb τ) (hfrS τ) (hsLv τ) (hsLi τ)
  have hidx : ∀ τ, logIdx (Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) (A.fam (Or.sm τ) v (q τ)) =
      (∑ᶠ x : FinitePlace L, Real.log (x (T τ x).det)) + ∑ σ : L →+* ℂ, Real.log ‖σ (C τ).det‖ := by
    intro τ
    rw [← GlobalTheory.T.glued_lattice_from_local_matrices L V _ (sL τ) _ (T τ) (C τ) (hsLi τ) (hb4 τ) (hC2 τ) (hb5 τ) (hb6 τ)]
    refine logIdx_congr _ _ _ ?_
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hrk i, (hC1 τ i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hrk.symm i, by rw [hC1 τ]; simp⟩

  have hvert : ∀ p ∈ Dc.SB B, _ := fun p hp =>
    GlobalTheory.T.exists_val_at_vert_factor_eq_norm_mul_prod E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or L (spMap (algebraMap (𝓞 L) L) ≫ z) w cc p hw hc (Finset.mem_filter.1 hp).1
  choose! t ht0 htv htf using hvert
  set g : L := uL * ∏ p ∈ Dc.SB B, t p with hg
  have hg0 : g ≠ 0 := mul_ne_zero huL (Finset.prod_ne_zero_iff.2 ht0)
  have hmd := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B b s (u * chartMono Dc.y cc Hd.aMu) hsm heq

  have hy : ∀ k, Dc.y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (isUnit_iff_ne_zero.2 (hc k))).1
  have cm_ne : ∀ x : K → ℤ, chartMono Dc.y cc x ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have cm_add : ∀ x x' : K → ℤ, chartMono Dc.y cc (x + x') = chartMono Dc.y cc x * chartMono Dc.y cc x' := by
    intro x x'
    simp only [chartMono, Pi.add_apply, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hy k) _ _
  have cm_neg : ∀ x : K → ℤ, chartMono Dc.y cc (-x) = (chartMono Dc.y cc x)⁻¹ := by
    intro x
    simp only [chartMono, Pi.neg_apply, _root_.zpow_neg, Finset.prod_inv_distrib]
  have cm_sum : ∀ sF : Finset ℕ, chartMono Dc.y cc (∑ p ∈ sF, Dc.vdeg p) = ∏ p ∈ sF, chartMono Dc.y cc (Dc.vdeg p) := by
    intro sF
    induction sF using Finset.induction_on with
    | empty => simp [chartMono]
    | insert p sF hp ih => rw [Finset.sum_insert hp, Finset.prod_insert hp, cm_add, ih]
  have hid : (((u * chartMono Dc.y cc Hd.aMu)⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) /
        MvPolynomial.aeval Dc.y (Dc.vnum p)) * chartMono Dc.y cc (muTwDeg Hd B))⁻¹ =
      u * ∏ p ∈ Dc.SB B, (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
        chartMono Dc.y cc (-Dc.vdeg p)) := by
    rw [show muTwDeg Hd B = Hd.aMu + ∑ p ∈ Dc.SB B, Dc.vdeg p from rfl, cm_add, cm_sum]
    simp only [cm_neg]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    have e1 : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) =
        (∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp only [inv_div]
    rw [e1]
    have hM := cm_ne Hd.aMu
    generalize (∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) = a₁
    generalize (∏ p ∈ Dc.SB B, chartMono Dc.y cc (Dc.vdeg p)) = a₂
    generalize chartMono Dc.y cc Hd.aMu = a₃ at hM
    simp only [mul_inv, inv_inv]
    field_simp
  have hΘ : ValAt Or.𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z)
      (((u * chartMono Dc.y cc Hd.aMu)⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) /
        MvPolynomial.aeval Dc.y (Dc.vnum p)) * chartMono Dc.y cc (muTwDeg Hd B))⁻¹ g := by
    rw [hid, hg]
    refine GlobalTheory.CompanionTheory.Ar.RootHt.valAt_mul hval ?_
    have hsub : ∀ sF : Finset ℕ, sF ⊆ Dc.SB B → ValAt Or.𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z)
        (∏ p ∈ sF, (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
          chartMono Dc.y cc (-Dc.vdeg p))) (∏ p ∈ sF, t p) := by
      intro sF
      induction sF using Finset.induction_on with
      | empty => intro _; simpa using GlobalTheory.CompanionTheory.Ar.RootHt.valAt_one (Or.𝔐.all _)
      | insert p sF hp ih =>
        intro hs
        rw [Finset.prod_insert hp, Finset.prod_insert hp]
        exact GlobalTheory.CompanionTheory.Ar.RootHt.valAt_mul (htv p (hs (Finset.mem_insert_self _ _)))
          (ih fun x hx => hs (Finset.mem_insert_of_mem hx))
    exact hsub _ subset_rfl
  have hunit : ∀ x : FinitePlace L, (∏ τ, x (T τ x).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio (muTwDeg Hd B) w cc x = x g :=
    fun x => GlobalTheory.T.tensor_lattice_coord_degree Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (CMType H) Or.𝔐.Li (fun τ => Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) _ s
      (muTwDeg Hd B) _ Or.𝔐.all Or.𝔐.tie hmd.1 hmd.2 L w z cc g x (fun τ => b' τ x) (fun τ => T' τ x) (fun τ => T τ x)
      hw hc hΘ hg0 (fun τ => hb1 τ x) (fun τ => hb2 τ x) (fun τ => hb3 τ x) (fun τ => hb4 τ x)
  obtain ⟨hρ, hfin, hsum⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum.ratio_sum L K J (muTwDeg Hd B) w cc g
    (fun k => ⟨cc k, hc k⟩) hc hg0

  have hLsum : ∑ τ, ∑ᶠ x : FinitePlace L, Real.log (x (T τ x).det) =
      -((∑ᶠ x : FinitePlace L, ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log (⨆ i, x (w ⟨k', i⟩))) +
        ∑ σ : L →+* ℂ, (Real.log ‖σ g‖ + ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log ‖σ (w ⟨k', cc k'⟩)‖)) := by
    rw [← hsum, ← finsum_neg_distrib, ← finsum_sum_comm]
    · refine finsum_congr fun x => ?_
      have hp : ∀ τ, 0 < x (T τ x).det := fun τ => FinitePlace.pos_iff.2 (hb4 τ x)
      have hx := hunit x
      rw [← Real.log_prod (fun τ _ => (hp τ).ne'), ← hx, Real.log_mul (Finset.prod_pos fun τ _ => hp τ).ne' (hρ x).ne']
      ring
    · intro τ _
      refine (hb5 τ).subset fun x hx => ?_
      intro hbad
      exact hx (by simp [hbad.2])

  have harch := GlobalTheory.T.abelian_part_integral_lattice E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L z P V MV A Or.sm r k _ hrk v q s sL C hLP hO hAd hsLv hC1 hC2
  choose hgram ν hGeo hν0 hνe using harch
  refine ⟨fun e => Real.log (‖GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y u (fun p => e (w p))‖ * ∏ k', ‖e (w ⟨k', cc k'⟩)‖ ^ Hd.aMu k') + Real.log (ν e) / 2,
    fun e => ⟨⟨cc, f, hdom e, b, had, u, hun, heq⟩, s, ν e, hsm, hGeo e, hν0 e, rfl⟩, ?_⟩
  have hrI : (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hO.2.2
  have hwe : ∀ (e : L →+* ℂ) k', ‖e (w ⟨k', cc k'⟩)‖ ≠ 0 := fun e k' => norm_ne_zero_iff.2 (by simpa using hc k')
  have hdet : ∀ (e : L →+* ℂ) τ, ‖e (C τ).det‖ ≠ 0 := fun e τ => norm_ne_zero_iff.2 (by simpa using hC2 τ)
  have hpi : (4 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)

  have hlogν : ∀ e : L →+* ℂ, Real.log (ν e) = Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) +
      ∑ τ, ((r : ℝ) * Real.log (4 * Real.pi)⁻¹ + Real.log (A.gramDet e (q τ)) - 2 * Real.log ‖e (C τ).det‖) := by
    intro e
    have hf : ∀ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (C τ).det‖ ^ 2 ≠ 0 := fun τ =>
      div_ne_zero (mul_ne_zero (pow_ne_zero _ hpi) (hgram e τ).ne') (pow_ne_zero _ (hdet e τ))
    rw [hνe e, Real.log_mul hrI (Finset.prod_ne_zero_iff.2 fun τ _ => hf τ), Real.log_prod (fun τ _ => hf τ)]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hpi) (hgram e τ).ne') (pow_ne_zero _ (hdet e τ)),
      Real.log_mul (pow_ne_zero _ hpi) (hgram e τ).ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hcast : ∀ k', (muTwDeg Hd B k' : ℝ) = (Hd.aMu k' : ℝ) + ∑ p ∈ Dc.SB B, (Dc.vdeg p k' : ℝ) := by
    intro k'
    show (((Hd.aMu + ∑ p ∈ Dc.SB B, Dc.vdeg p) k' : ℤ) : ℝ) = _
    rw [Pi.add_apply, Finset.sum_apply]
    push_cast
    rfl

  have hone : ∀ e : L →+* ℂ, twW (D := Dc) B (fun _ => 0) (fun p => e (w p)) +
      (Real.log (‖GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y u (fun p => e (w p))‖ * ∏ k', ‖e (w ⟨k', cc k'⟩)‖ ^ Hd.aMu k') + Real.log (ν e) / 2) =
      (Real.log ‖e g‖ + ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖) +
      (Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 + Fintype.card (CMType H) * r / 2 * Real.log (4 * Real.pi)⁻¹) +
      (∑ τ, Real.log (A.gramDet e (q τ))) / 2 - ∑ τ, Real.log ‖e (C τ).det‖ := by
    intro e
    have huE : e uL ≠ 0 := by simpa using huL
    have htE : ∀ p ∈ Dc.SB B, ‖e (t p)‖ ≠ 0 := fun p hp => norm_ne_zero_iff.2 (by simpa using ht0 p hp)
    have hlw : Real.log (∏ k', ‖e (w ⟨k', cc k'⟩)‖ ^ Hd.aMu k') = ∑ k', (Hd.aMu k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖ := by
      rw [Real.log_prod (fun k' _ => zpow_ne_zero _ (hwe e k'))]
      exact Finset.sum_congr rfl fun k' _ => Real.log_zpow _ _
    have hvf : ∀ p ∈ Dc.SB B, Real.log (Dc.vertFactor p (fun i => e (w i))) =
        Real.log ‖e (t p)‖ + ∑ k', (Dc.vdeg p k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖ := by
      intro p hp
      rw [htf p hp e, Real.log_mul (htE p hp) (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (hwe e k')),
        Real.log_prod (fun k' _ => zpow_ne_zero _ (hwe e k'))]
      congr 1
      exact Finset.sum_congr rfl fun k' _ => Real.log_zpow _ _
    have hge : Real.log ‖e g‖ = Real.log ‖e uL‖ + ∑ p ∈ Dc.SB B, Real.log ‖e (t p)‖ := by
      rw [hg, map_mul, norm_mul, map_prod, norm_prod, Real.log_mul (norm_ne_zero_iff.2 huE)
        (Finset.prod_ne_zero_iff.2 htE), Real.log_prod htE]
    have hsplit : ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖ =
        ∑ k', (Hd.aMu k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖ +
          ∑ p ∈ Dc.SB B, ∑ k', (Dc.vdeg p k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖ := by
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [hcast, add_mul, Finset.sum_mul]
    have htw : twW (D := Dc) B (fun _ => 0) (fun p => e (w p)) = ∑ p ∈ Dc.SB B, Real.log ‖e (t p)‖ +
        ∑ p ∈ Dc.SB B, ∑ k', (Dc.vdeg p k' : ℝ) * Real.log ‖e (w ⟨k', cc k'⟩)‖ := by
      unfold twW
      rw [zero_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hvf
    rw [htw, hvalC e, Real.log_mul (norm_ne_zero_iff.2 huE) (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (hwe e k')),
      hlw, hlogν e, hge, hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp only [Finset.card_univ, nsmul_eq_mul]
    ring

  have hN : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (L →+* ℂ) : ℝ) = Module.finrank ℚ L := by
    exact_mod_cast NumberField.Embeddings.card L ℂ
  have hS : (∑ σ : L →+* ℂ, twW (D := Dc) B (fun _ => 0) (fun p => σ (w p))) +
      (∑ e : L →+* ℂ, (Real.log (‖GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y u (fun p => e (w p))‖ * ∏ k', ‖e (w ⟨k', cc k'⟩)‖ ^ Hd.aMu k') + Real.log (ν e) / 2)) =
      (∑ σ : L →+* ℂ, (Real.log ‖σ g‖ + ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log ‖σ (w ⟨k', cc k'⟩)‖)) +
      (Module.finrank ℚ L : ℝ) * (Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 + Fintype.card (CMType H) * r / 2 * Real.log (4 * Real.pi)⁻¹) +
      (∑ τ, ∑ ι' : L →+* ℂ, Real.log (A.gramDet ι' (q τ))) / 2 - ∑ τ, ∑ σ : L →+* ℂ, Real.log ‖σ (C τ).det‖ := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun e _ => hone e, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.sum_div,
      Finset.sum_comm (f := fun (e : L →+* ℂ) τ => Real.log (A.gramDet e (q τ))),
      Finset.sum_comm (f := fun (e : L →+* ℂ) τ => Real.log ‖e (C τ).det‖)]
  have hsum2 : ∑ τ, (logIdx (Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) (A.fam (Or.sm τ) v (q τ)) -
      (∑ ι' : L →+* ℂ, Real.log (A.gramDet ι' (q τ))) / 2) / Module.finrank ℚ L =
      ((∑ τ, ∑ᶠ x : FinitePlace L, Real.log (x (T τ x).det)) + (∑ τ, ∑ σ : L →+* ℂ, Real.log ‖σ (C τ).det‖) -
        (∑ τ, ∑ ι' : L →+* ℂ, Real.log (A.gramDet ι' (q τ))) / 2) / Module.finrank ℚ L := by
    simp only [hidx]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
  show (Module.finrank ℚ L : ℝ)⁻¹ * ((∑ᶠ x : FinitePlace L, ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log (⨆ i, x (w ⟨k', i⟩))) +
      ∑ σ : L →+* ℂ, twW (D := Dc) B (fun _ => 0) (fun p => σ (w p))) + _ / _ =
    -(∑ τ, (logIdx (Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) (A.fam (Or.sm τ) v (q τ)) -
      (∑ ι' : L →+* ℂ, Real.log (A.gramDet ι' (q τ))) / 2) / Module.finrank ℚ L -
      Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 + Fintype.card (CMType H) * r / 2 * Real.log (4 * Real.pi))
  rw [hsum2, hLsum]
  rw [Real.log_inv] at hS
  generalize (∑ᶠ x : FinitePlace L, ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log (⨆ i, x (w ⟨k', i⟩))) = Pf at *
  generalize (∑ σ : L →+* ℂ, twW (D := Dc) B (fun _ => 0) (fun p => σ (w p))) = TW at *
  generalize (∑ e : L →+* ℂ, (Real.log (‖GroundTheory.Heights₂.Heights.LowerBoundFree.valAt Dc.y u (fun p => e (w p))‖ * ∏ k', ‖e (w ⟨k', cc k'⟩)‖ ^ Hd.aMu k') + Real.log (ν e) / 2)) = Xs at *
  generalize (∑ σ : L →+* ℂ, (Real.log ‖σ g‖ + ∑ k', (muTwDeg Hd B k' : ℝ) * Real.log ‖σ (w ⟨k', cc k'⟩)‖)) = As at *
  generalize (∑ τ, ∑ ι' : L →+* ℂ, Real.log (A.gramDet ι' (q τ))) = Gs at *
  generalize (∑ τ, ∑ σ : L →+* ℂ, Real.log ‖σ (C τ).det‖) = Cs at *
  generalize Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) = lr at *
  generalize Real.log (4 * Real.pi) = l4 at *
  generalize (Fintype.card (CMType H) : ℝ) = cf at *
  generalize (Module.finrank ℚ L : ℝ) = N at *
  have hN' : N ≠ 0 := hN.ne'
  have e2 : Xs = As + N * (lr / 2 + cf * r / 2 * -l4) + Gs / 2 - Cs - TW := by linarith
  rw [e2]
  field_simp
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
