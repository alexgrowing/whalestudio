import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScalingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVarietyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsOverNumberFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PhiDegFibLatLeOfIsOFamilyOfIsAdaptedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspaceStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventuallyStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopHt

open MvPolynomial

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_iSup_support {Jx : Type} [Fintype Jx] (x : Jx → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty Jx := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.mulSupport_finite (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

lemma blocks_support {K : Type} [Fintype K] {Jx : K → Type} [∀ k, Fintype (Jx k)] (a : K → ℝ)
    (x : ∀ k, Jx k → L) (hx : ∀ k, ∃ i, x k i ≠ 0) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (x k i))).Finite := by
  refine (Set.finite_iUnion fun k => log_iSup_support (x k) (hx k)).subset fun v hv => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_iUnion.2 ⟨k, right_ne_zero_of_mul hk⟩

end Places

variable {K : Type} [Fintype K] {Jx : K → Type} [∀ k, Fintype (Jx k)]

lemma lineHt_decomp (M A : HermLine Jx) (a : K → ℤ) (p q : ℕ) (φ G : ((Σ k, Jx k) → ℂ) → ℝ) (L : Type) [Field L]
    [NumberField L] (w : (Σ k, Jx k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (ha : M.a = (q : ℤ) • a + (p : ℤ) • A.a)
    (hh : ∀ σ : L →+* ℂ, Real.log (M.h fun x => σ (w x)) =
      q * (φ (fun x => σ (w x)) + G (fun x => σ (w x))) + p * Real.log (A.h fun x => σ (w x))) :
    Ht.lineHt M L w = q * (Ht.ptHt (fun k => (a k : ℝ)) φ L w +
      (∑ σ : L →+* ℂ, G (fun x => σ (w x))) / Module.finrank ℚ L) + p * Ht.lineHt A L w := by
  classical
  have hd : (Module.finrank ℚ L : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have s1 := blocks_support (L := L) (fun k => (a k : ℝ)) (fun k i => w ⟨k, i⟩) hw
  have s2 := blocks_support (L := L) (fun k => (A.a k : ℝ)) (fun k i => w ⟨k, i⟩) hw
  have hfin : (∑ᶠ v : FinitePlace L, ∑ k, (M.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      q * (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        p * ∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [mul_finsum, mul_finsum, ← finsum_add_distrib]
    · refine finsum_congr fun v => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ha]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      ring
    · exact s1.subset (Function.support_mul_subset_right _ _)
    · exact s2.subset (Function.support_mul_subset_right _ _)
  have harch : ∑ σ : L →+* ℂ, Real.log (M.h fun x => σ (w x)) =
      q * (∑ σ : L →+* ℂ, φ (fun x => σ (w x)) + ∑ σ : L →+* ℂ, G (fun x => σ (w x))) +
        p * ∑ σ : L →+* ℂ, Real.log (A.h fun x => σ (w x)) := by
    rw [Finset.sum_congr rfl fun σ _ => hh σ, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_add_distrib]
  unfold Ht.lineHt Ht.ptHt
  simp only []
  rw [hfin, harch]
  field_simp
  ring

lemma mem_mcPts_of_ptsOver {P : Ideal (MRing Jx)} {L : Type} [Field L] (σ : L →+* ℂ) {w : (Σ k, Jx k) → L}
    (hw : w ∈ Small.ptsOver L P) : (fun p => σ (w p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hw.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · have h1 : aeval (fun p => σ (w p)) f = σ (aeval w f) :=
      (comp_aeval_apply (R := ℤ) (f := w) σ.toIntAlgHom f).symm
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def, h1, hw.2 f hf, map_zero]

end GlobalTheory.CompanionTheory.Ar.Cusp.TopHt

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopHt

theorem htU_of_given : Top.Given → Fl.FlatDegree → ∃ Ch : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H)
    (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type)
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc)
    (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc)
    (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ →
      Or.𝔐.IsCuspWeight Or.sm U → S'.IsTied → HtU S' Ch (hostRd E) (hostLval H) := by
  intro hG hF
  obtain ⟨C, -, hU4⟩ := GlobalTheory.T.phiDeg_fibLat_le_of_isOFamily_of_isAdapted hG hF
  refine ⟨C, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hTied
  intro B p q hB hp hpq
  have hq0 : 0 < q := by omega
  have hq : (0 : ℝ) < q := by exact_mod_cast hq0
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (GlobalTheory.T.regularized_weight_dominates_eventually K J II (CMType H) Ω W Dc Hd M _ S' hTied)
  refine ⟨u / 2, half_pos hu, fun t' ht' ht'u P hP hyP => ?_⟩
  obtain ⟨hge, -, hreg⟩ := hsub ⟨ht', by linarith⟩
  obtain ⟨hsm, hdeg, hlog⟩ := hreg B p q
  obtain ⟨L₀, _, _, w, -, hw, hII'⟩ := GlobalTheory.T.height_of_zero_dim_variety K J II hII.1 P hP
  have hdeg0 : (0 : ℝ) < degC P := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hP)
  have hMU : htMUc Hd S' B p q t' P = Ht.lineHt (MUc Hd S' B p q t') L₀ w / q := by
    unfold htMUc
    rw [← hII' _ hsm]
    field_simp
  have hA' : -Dc.KA ≤ Ht.lineHt Dc.A' L₀ w := by
    rw [← hII' _ Dc.A'_pos.1, le_div_iff₀ hdeg0]
    linarith [Dc.heights P hP hyP]
  have hwy : w ∈ Small.ptsOver L₀ (mCoordIdeal Dc.y) := ⟨hw.1, fun f hf => hw.2 f (hyP hf)⟩
  have hpq1 : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  obtain ⟨L, _, _, e, z, Pa, V, _, _, _, _, MV, A, hco, hlin, hrk, hBq⟩ :=
    GlobalTheory.T.small_points_over_number_field hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L₀ hpq1 w hwy
  obtain ⟨-, -, -, -, -, hcard, -⟩ :=
    GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L (spMap (algebraMap (𝓞 L) L) ≫ z)
  obtain ⟨⟨r, v, hv⟩, hadp⟩ := GlobalTheory.T.adapted_family_exists_on_eigenspace E L (CMType H) V A hcard
  have hne : Nonempty (CMType H) := by
    have h1 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [← hcard] at h1
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ₀⟩ := hne
  have hrj : r + (Dc.j' - r) = Dc.j' := by
    obtain ⟨k, -, -, -, h3, -⟩ := hadp r v hv (Or.sm τ₀)
    rw [hrk, Or.rk_sm] at h3
    unfold ComponentData.j'
    omega
  have hk : ∀ τ, ∃ qq : Fin (Dc.j' - r) → A.Λ, (∀ i, (qq i : V) ∈ A.eig (Or.sm τ)) ∧
      A.IsAdapted (Or.sm τ) v qq := by
    intro τ
    obtain ⟨k, qq, h1, h2, h3, -⟩ := hadp r v hv (Or.sm τ)
    have hk' : k = Dc.j' - r := by
      rw [hrk, Or.rk_sm] at h3
      unfold ComponentData.j'
      omega
    subst hk'
    exact ⟨qq, h1, h2⟩
  choose qq hqq1 hqq2 using hk
  obtain ⟨x, hx, hht⟩ := GlobalTheory.T.cusp_intersection_height hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B L z Pa V MV A
    (fun p => e (w p)) r (Dc.j' - r) v qq hAdm.2.1 hco hlin hv (fun τ => ⟨hqq2 τ, hqq1 τ⟩)
  have hu4 := hU4 E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ B L z Pa V MV A r (Dc.j' - r) v qq hAdm hB hlin hBq
    hrj hv (fun τ => ⟨hqq2 τ, hqq1 τ⟩)
  have hxe : ∀ σ : L →+* ℂ, x σ ≤ Real.log (S'.ref.h fun p => σ (e (w p))) +
      S'.bregWeight t' (M.proj fun p => σ (e (w p))) := by
    intro σ
    have hc := RootHt.PullCoords.coordsAt_embedding _ _ Or.𝔐.ξ K J Dc.y L (fun p => e (w p)) z σ hco
    have e1 : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e1] at hc
    have h1 := GlobalTheory.T.cusp_intersection_finite hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U M S' _ _ (x σ) hU hc (hx σ)
    linarith [hge (M.proj fun p => σ (e (w p)))]
  have hext : ∀ A₀ : HermLine J, Ht.lineHt A₀ L (fun p => e (w p)) = Ht.lineHt A₀ L₀ w := by
    intro A₀
    have h1 := GlobalTheory.T.line_height_invariant_scaling K J A₀ L₀ L e w (fun _ => 1) hw.1 (fun _ => one_ne_zero)
    simpa using h1
  have hw' : ∀ k, ∃ i, e (w ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw.1 k
    exact ⟨i, (map_ne_zero e).2 hi⟩
  have hdec := lineHt_decomp (MUc Hd S' B p q t') Dc.A' (muTwDeg Hd B) p q (twW (D := Dc) B fun _ => 0)
    (fun z' => Real.log (S'.ref.h z') + S'.bregWeight t' (M.proj z')) L (fun p => e (w p)) hw'
    (by rw [hdeg, Dc.A'_deg]) (fun σ => by
      have hm := mem_mcPts_of_ptsOver (σ.comp e) hwy
      simp only [RingHom.comp_apply] at hm
      rw [hlog _ hm]
      simp only [twW, RingHom.comp_apply, zero_add]
      ring)
  rw [hext, hext] at hdec
  have hsum : ∑ σ : L →+* ℂ, x σ ≤ ∑ σ : L →+* ℂ, (Real.log (S'.ref.h fun p => σ (e (w p))) +
      S'.bregWeight t' (M.proj fun p => σ (e (w p)))) := Finset.sum_le_sum fun σ _ => hxe σ
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hdiv := div_le_div_of_nonneg_right hsum hn.le
  have hpq' : (0 : ℝ) ≤ p / q := div_nonneg (Nat.cast_nonneg _) hq.le
  rw [hMU, hdec]
  have hAq : -(p / q * Dc.KA) ≤ p / q * Ht.lineHt Dc.A' L₀ w := by nlinarith
  rw [show (q * (Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L (fun p => e (w p)) +
      (∑ σ : L →+* ℂ, (Real.log (S'.ref.h fun p => σ (e (w p))) + S'.bregWeight t' (M.proj fun p => σ (e (w p))))) /
        Module.finrank ℚ L) + p * Ht.lineHt Dc.A' L₀ w) / q =
      Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L (fun p => e (w p)) +
      (∑ σ : L →+* ℂ, (Real.log (S'.ref.h fun p => σ (e (w p))) + S'.bregWeight t' (M.proj fun p => σ (e (w p))))) /
        Module.finrank ℚ L + p / q * Ht.lineHt Dc.A' L₀ w by field_simp]
  linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.TopHt
