import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializationCoordRatioValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameRelayBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLatticeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatioStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompleteDvrBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedeanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedeanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameCombinedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameTotalBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightEstimateStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem reg_val {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A : Subring Ω} {T : CDVR}
    {evT : A →+* T.Fr} {zV : Spec (CommRingCat.of T.V) ⟶ X} (hξ : IsCptGen ξ) (hR : ReadsPt ξ A T evT zV)
    (h : genPt ξ ⤳ centre zV) (a : A) (ha : (a : Ω) ∈ regAt ξ ⟨centre zV, h⟩) :
    evT a ∈ (algebraMap T.V T.Fr).range := by
  obtain ⟨s, hs⟩ := ha
  have h1 : ValAt ξ zV (a : Ω) ((Scheme.stalkClosedPointTo zV).hom s) := ⟨h, s, hs, rfl⟩
  exact ⟨_, LieTangent.valAt_unique hξ (LieTangent.valAt_base hξ (algebraMap T.V T.Fr) h1) (hR a)⟩

theorem log_bound {S m x y θ : ℝ} (hS : 0 < S) (hx : 0 < x) (hy : 0 < y) {n : ℤ} (hn : n = 1 ∨ n = -1)
    (hm : m = x ^ n) (hb : |Real.log x - Real.log y| ≤ θ) :
    |Real.log S - Real.log (S / m / y⁻¹ ^ n)| ≤ θ := by
  have hm0 : 0 < m := hm ▸ zpow_pos hx n
  have hy' : 0 < y⁻¹ ^ n := zpow_pos (inv_pos.2 hy) n
  rw [Real.log_div (div_pos hS hm0).ne' hy'.ne', Real.log_div hS.ne' hm0.ne', hm, Real.log_zpow, Real.log_zpow,
    Real.log_inv]
  rcases hn with rfl | rfl
  · simp only [Int.cast_one, one_mul]
    rw [show Real.log S - (Real.log S - Real.log x - -Real.log y) = Real.log x - Real.log y by ring]
    exact hb
  · simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    rw [show Real.log S - (Real.log S - -Real.log x - - -Real.log y) = -(Real.log x - Real.log y) by ring, abs_neg]
    exact hb

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem compare : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → Or.𝔐.OmVB → 0 < Dw.p + Dw.q →
    (∀ p' : ℕ, p'.Prime → (p' : ℤ) ∣ discr E → p' ∈ SS) →
    ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC]
      (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC →
    ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) →
    ∃ d d' : T.V, (∀ w ∈ lieEig Or MC ρC σ, d • w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC) ∧
      (∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC, d' • w ∈ lieEig Or MC ρC σ) ∧
      (p : ℝ) ^ (-Small.latExp E SS p) ≤ absT p la T e (algebraMap T.V T.Fr d) ∧
      (p : ℝ) ^ (-Small.latExp E SS p) ≤ absT p la T e (algebraMap T.V T.Fr d') := by
  intro hG E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hA la T io e y evT zT t hI zV hR hOm hpq
    hSS EC _ _ _ _ MC ρC hact s σ hσ
  have hpla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have he : 0 < e := hI.2.1.1
  obtain ⟨hmul, hone, hpos, hle⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e he (ram_pos hpla)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hθ := Small.latExp_nonneg E SS (Fact.out : p.Prime)
  have hle1 : (p : ℝ) ^ (-Small.latExp E SS p) ≤ absT p la T e (algebraMap T.V T.Fr 1) := by
    rw [map_one, hone]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  by_cases hpS : p ∈ SS
  · obtain ⟨κz, h1, h2, h3⟩ := GlobalTheory.T.root_origin_frame_total_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT
      zT t hI zV hR hOm hpq hpS EC MC ρC hact s σ hσ
    obtain ⟨h4, D, h5, h6⟩ := GlobalTheory.T.root_origin_frame_height_estimate E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT
      zT t hI zV hR hpS EC MC ρC s
    refine ⟨1, κz * D, fun w hw => ?_, fun w hw => ?_, hle1, ?_⟩
    · rw [one_smul]
      exact h4 (h1 hw)
    · rw [mul_smul]
      exact h2 _ (h6 w hw)
    · rw [map_mul, hmul, h3]
      have e1 : Small.latExp E SS p = Small.htExp p + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E := if_pos hpS
      rw [e1, neg_add, Real.rpow_add hp0]
      exact mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp0.le _)
  · have hd : ¬ (p : ℤ) ∣ discr E := fun h => hpS (hSS p Fact.out h)
    have h1 := GlobalTheory.T.root_origin_frame_combined E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI zV hR hpS hd
      EC MC ρC hact s σ hσ
    refine ⟨1, 1, fun w hw => ?_, fun w hw => ?_, hle1, hle1⟩
    · rw [one_smul, h1]
      exact hw
    · rw [one_smul, ← h1]
      exact hw

theorem diag_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → Or.𝔐.OmVB → 0 < Dw.p + Dw.q →
    (∀ p' : ℕ, p'.Prime → (p' : ℤ) ∣ discr E → p' ∈ SS) →
    ∀ (s : CMType H ⊕ CMType H) (b : Fin (labelRk Dw s) → Or.𝔐.Li)
      (Tm : Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω) (hT : ∀ i j, Tm i j ∈ A),
      (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b s) i) →
      (Or.𝔐.V s).IsFrameAt b ⟨centre zV, Or.𝔐.all _⟩ → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b s j) →
      (∀ i, evT ⟨Tm i i, hT i i⟩ ≠ 0) → ∀ i,
      |Real.log (absT p la T e (evT ⟨Tm i i, hT i i⟩)) - Real.log (absT p la T e (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr))| ≤
        Small.latExp E SS p * Real.log p := by
  intro hG E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hA la T io e y evT zT t hI zV hR hOm hpq
    hSS s b Tm hT hfl hfr hb hd i
  have hpla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have he : 0 < e := hI.2.1.1
  obtain ⟨hmul, hone, hpos, hle⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e he (ram_pos hpla)
  obtain ⟨EC, _, _, MC, ρC, hact⟩ := GlobalTheory.T.root_origin_complete_dvr_bound E H Dw l Xo c O β Y SS RM Sys Fx Or T zV
  letI : Module T.V EC := Module.compHom EC (algebraMap T.V T.Fr)
  haveI : IsScalarTower T.V T.Fr EC := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.root_origin_frame_archimedean E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI
    zV hR s
  choose u hu huv using GlobalTheory.T.root_origin_frame_local_bound E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI
    zV hR EC MC s
  obtain ⟨hli, yb, htri, hspan⟩ := GlobalTheory.T.root_origin_frame_relay_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y
    evT zT t hI zV hR EC MC ρC hact s u σ hu hσ
  haveI := Or.𝔐.t.semi.smooth
  have hW := GlobalTheory.T.complete_dvr_lie_model_lattice Or.𝔐.X Or.𝔐.t.G RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M T zV EC MC A evT Or.𝔐.tie.gen inferInstance
    (Or.𝔐.all _) (Or.𝔐.all _) hR (Or.𝔐.V s) _ b (Or.Fl.b s) Tm u hT hfr hb huv
  obtain ⟨d, d', hd1, hd2, hμ, hμ'⟩ := compare hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y
    evT zT t hI zV hR hOm hpq hSS EC MC ρC hact s σ hσ
  have hlow := (GlobalTheory.T.flag_equal_change_lower_triangular RM.Ω Or.𝔐.Li _ b (Or.Fl.b s) Tm hfr.1 hfl hb).2
  have htri2 : TriIn u (fun i => evT ⟨Tm i i, hT i i⟩) (fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • u j) := fun i =>
    ⟨fun j => evT ⟨Tm i j, hT i j⟩, rfl, fun j hij => by
      have : (⟨Tm i j, hT i j⟩ : A) = 0 := Subtype.ext (hlow i j hij)
      show evT ⟨Tm i j, hT i j⟩ = 0
      rw [this, map_zero], rfl⟩
  have c1 := GlobalTheory.T.triangular_span_coeff_ratio T.V T.Fr EC _ u yb _ _ _ d hli htri htri2 hd
    (fun x hx => by
      rw [← hW]
      exact hd1 x (hspan ▸ hx)) i
  have c2 := GlobalTheory.T.triangular_span_coeff_ratio T.V T.Fr EC _ u _ yb _ _ d' hli htri2 htri (fun j => Units.ne_zero _)
    (fun x hx => by
      rw [← hspan]
      exact hd2 x (hW ▸ hx)) i
  obtain ⟨g1, hg1⟩ := c1
  obtain ⟨g2, hg2⟩ := c2
  set a := evT ⟨Tm i i, hT i i⟩ with ha
  set τ : T.Fr := (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr) with hτ
  replace hg1 : algebraMap T.V T.Fr d * τ = algebraMap T.V T.Fr g1 * a := hg1
  replace hg2 : algebraMap T.V T.Fr d' * a = algebraMap T.V T.Fr g2 * τ := hg2
  have hx : 0 < absT p la T e a := hpos _ (hd i)
  have hy : 0 < absT p la T e τ := hpos _ (Units.ne_zero _)
  have hg1' : absT p la T e (algebraMap T.V T.Fr g1) ≤ 1 := (hle _).2 ⟨g1, rfl⟩
  have hg2' : absT p la T e (algebraMap T.V T.Fr g2) ≤ 1 := (hle _).2 ⟨g2, rfl⟩
  have e1 := congrArg (absT p la T e) hg1
  have e2 := congrArg (absT p la T e) hg2
  rw [hmul, hmul] at e1 e2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set P := (p : ℝ) ^ (-Small.latExp E SS p) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hp0 _
  have hlogP : Real.log P = -(Small.latExp E SS p * Real.log p) := by
    rw [hP, Real.log_rpow hp0]
    ring
  have b1 : P * absT p la T e τ ≤ absT p la T e a := by
    calc P * absT p la T e τ ≤ absT p la T e (algebraMap T.V T.Fr d) * absT p la T e τ :=
          mul_le_mul_of_nonneg_right hμ hy.le
      _ = absT p la T e (algebraMap T.V T.Fr g1) * absT p la T e a := e1
      _ ≤ 1 * absT p la T e a := mul_le_mul_of_nonneg_right hg1' hx.le
      _ = _ := one_mul _
  have b2 : P * absT p la T e a ≤ absT p la T e τ := by
    calc P * absT p la T e a ≤ absT p la T e (algebraMap T.V T.Fr d') * absT p la T e a :=
          mul_le_mul_of_nonneg_right hμ' hx.le
      _ = absT p la T e (algebraMap T.V T.Fr g2) * absT p la T e τ := e2
      _ ≤ 1 * absT p la T e τ := mul_le_mul_of_nonneg_right hg2' hy.le
      _ = _ := one_mul _
  have l1 := Real.log_le_log (mul_pos hP0 hy) b1
  have l2 := Real.log_le_log (mul_pos hP0 hx) b2
  rw [Real.log_mul hP0.ne' hy.ne', hlogP] at l1
  rw [Real.log_mul hP0.ne' hx.ne', hlogP] at l2
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem reads_roots : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → (∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → Small.ReadsRootsFin Or z (FinRd.tOf p la T e t) (Small.latExp E SS p) := by
  intro hG E _ _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr hOm hSS A p _ z ev hz hval hA hrat la T io e y evT zT t hI
  have hpla : (p : 𝓞 c.F) ∈ la.asIdeal := hI.1
  have he : 0 < e := hI.2.1.1
  obtain ⟨hmul, hone, hpos, hle⟩ := GlobalTheory.T.finite_residue_absolute_value E H l c p la T e he (ram_pos hpla)
  have habs : ∀ x : A, ‖ev x‖ = absT p la T e (evT x) := hI.2.2.2.2.2.1
  have hzp := hz.1
  have hmax : ∀ k, ∃ ck : RM.ι k, z ⟨k, ck⟩ ≠ 0 ∧ ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, ck⟩‖ := by
    intro k
    obtain ⟨u, hu⟩ := hzp.1 k
    haveI : Nonempty (RM.ι k) := ⟨u⟩
    obtain ⟨m, hm⟩ := Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
    refine ⟨m, fun h0 => ?_, hm⟩
    have h1 := hm u
    rw [h0, norm_zero] at h1
    exact hu (norm_le_zero_iff.1 h1)
  choose ch hc0 hcm using hmax
  classical
  have hy : ∀ k, RM.y ⟨k, ch k⟩ ≠ 0 := by
    intro k h0
    have hmem : (MvPolynomial.X ⟨k, ch k⟩ : MRing RM.ι) ∈ mCoordIdeal RM.y := by
      show mConeMap RM.y _ = 0
      rw [Small.ReadFinTest.mConeMap_form RM.y (TiePrimes.homog_X _)]
      simp [h0]
    have h1 := hzp.2 _ hmem
    rw [MvPolynomial.aeval_X] at h1
    exact hc0 k h1
  have hr : ∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, ch k⟩ ∈ A := fun k i => hrat k i (ch k) (hy k)
  obtain ⟨hevr, hden⟩ := GlobalTheory.T.specialization_coord_ratio_value RM.K RM.ι RM.Ω RM.y (PadicAlgCl p) z A ev hzp hval ch hc0 hy hr
  have hVr : ∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range := fun k i => (hle _).1 (by
    rw [← habs, hevr, norm_div]
    exact div_le_one_of_le₀ (hcm k i) (norm_nonneg _))
  have hne : ∀ x : A, ev x ≠ 0 → evT x ≠ 0 := fun x hx h0 => by
    have h1 := habs x
    rw [h0, show absT p la T e (0 : T.Fr) = 0 from if_pos rfl] at h1
    exact hx (norm_eq_zero.1 h1)
  obtain ⟨zV, h, hch, hRd⟩ := GlobalTheory.T.complete_dvr_coord_ratio_value Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.all Or.𝔐.tie A T evT ch hy hr hVr
    (fun a => by
      obtain ⟨b, h1, h2, h3⟩ := hden a
      exact ⟨b, hne b h1, h2, h3⟩)
  have hunit : ∀ u u' : A, (u : RM.Ω) ∈ regAt Or.𝔐.ξ ⟨centre zV, h⟩ → (u' : RM.Ω) ∈ regAt Or.𝔐.ξ ⟨centre zV, h⟩ →
      u * u' = 1 → ‖ev u‖ = 1 := by
    intro u u' h1 h2 h3
    have a1 : ‖ev u‖ ≤ 1 := by
      rw [habs]
      exact (hle _).2 (reg_val Or.𝔐.tie.gen hRd h u h1)
    have a2 : ‖ev u'‖ ≤ 1 := by
      rw [habs]
      exact (hle _).2 (reg_val Or.𝔐.tie.gen hRd h u' h2)
    have a3 : ‖ev u‖ * ‖ev u'‖ = 1 := by
      rw [← norm_mul, ← map_mul, h3, map_one, norm_one]
    nlinarith [norm_nonneg (ev u), norm_nonneg (ev u')]
  have hsingle : ∀ k, Small.HasVal RM.y (Pi.single k 1) (RM.y ⟨k, ch k⟩) z (z ⟨k, ch k⟩) := fun k =>
    ⟨Pi.single k 1, 0, MvPolynomial.X ⟨k, ch k⟩, 1, TiePrimes.homog_X _, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one,
      fun j => by
        by_cases hj : j = k
        · subst hj
          simp
        · simp [Pi.single_eq_of_ne hj], by simp, by simp, by simp⟩
  intro ρ
  have hpq : 0 < Dw.p + Dw.q := lt_of_le_of_lt (Nat.zero_le _) ρ.2.2
  have hsg : HodgeCpt.rootSgn Dw ρ = 1 ∨ HodgeCpt.rootSgn Dw ρ = -1 := by
    unfold HodgeCpt.rootSgn
    split_ifs <;> simp
  obtain ⟨b, Tm, hfl, hfr, hb, hTA, hTd⟩ := hA.2.2.2 (HodgeCpt.rootIdx Dw ρ).1 ⟨centre zV, h⟩
  obtain ⟨hM, hMi⟩ := hA.2.2.1 ρ ch hy
  have hne' : ∀ j, evT ⟨Tm j j, hTA j j⟩ ≠ 0 := fun j h0 => by
    have h1 : (⟨Tm j j, hTA j j⟩ : A) * ⟨_, (hTd j).2⟩ = 1 := Subtype.ext (mul_inv_cancel₀ (hTd j).1)
    have h2 := congrArg evT h1
    rw [map_mul, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  have hP0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have he0 : Or.e ρ ≠ 0 := (Or.lines ρ).1
  have hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0 := mul_ne_zero hP0 he0
  obtain ⟨hu1, hu2⟩ := GlobalTheory.T.root_origin_root_index_bound E H Dw l Xo c O β Y SS RM Sys Fx Or ρ ⟨centre zV, h⟩ ch hch b Tm hfl hfr hb
    (fun j => (hTd j).1)
  have hT0 := (hTd (HodgeCpt.rootIdx Dw ρ).2).1
  have hTi := (hTd (HodgeCpt.rootIdx Dw ρ).2).2
  let Ma : A := ⟨_, hM⟩
  let Mi : A := ⟨_, hMi⟩
  let Ta : A := ⟨_, hTA (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2⟩
  let Ti : A := ⟨_, hTi⟩
  have hMM : Ma * Mi = 1 := Subtype.ext (mul_inv_cancel₀ hM0)
  have hTT : Ta * Ti = 1 := Subtype.ext (mul_inv_cancel₀ hT0)
  have nMM : ‖ev Ma‖ * ‖ev Mi‖ = 1 := by rw [← norm_mul, ← map_mul, hMM, map_one, norm_one]
  have nTT : ‖ev Ta‖ * ‖ev Ti‖ = 1 := by rw [← norm_mul, ← map_mul, hTT, map_one, norm_one]
  have hx : 0 < ‖ev Ta‖ := by
    by_contra h0
    have h1 : ‖ev Ta‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h1, zero_mul] at nTT
    exact zero_ne_one nTT
  have hm0 : 0 < ‖ev Ma‖ := by
    by_contra h0
    have h1 : ‖ev Ma‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h1, zero_mul] at nMM
    exact zero_ne_one nMM
  have hm : ‖ev Ma‖ = ‖ev Ta‖ ^ HodgeCpt.rootSgn Dw ρ := by
    rcases hsg with hs | hs
    · rw [hs] at hu1 hu2 ⊢
      have h1 := hunit (Ma * Ti) (Mi * Ta) (by simpa [Ma, Ti] using hu1) (by
        simpa [Mi, Ta, mul_comm] using hu2) (by
          rw [show Ma * Ti * (Mi * Ta) = (Ma * Mi) * (Ta * Ti) by ring, hMM, hTT, one_mul])
      rw [map_mul, norm_mul] at h1
      rw [zpow_one]
      have hTi0 : ‖ev Ti‖ ≠ 0 := fun h0 => by
        rw [h0, mul_zero] at nTT
        exact zero_ne_one nTT
      exact mul_right_cancel₀ hTi0 (h1.trans nTT.symm)
    · rw [hs] at hu1 hu2 ⊢
      have h1 := hunit (Ma * Ta) (Mi * Ti) (by simpa [Ma, Ta] using hu1) (by
        simpa [Mi, Ti, mul_comm] using hu2) (by
          rw [show Ma * Ta * (Mi * Ti) = (Ma * Mi) * (Ta * Ti) by ring, hMM, hTT, one_mul])
      rw [map_mul, norm_mul] at h1
      rw [zpow_neg_one]
      exact eq_inv_of_mul_eq_one_left h1
  have hseg : Small.HasVal RM.y (RM.xdeg ρ) (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) z
      (∏ k, z ⟨k, ch k⟩ ^ RM.xdeg ρ k) := by
    have h1 := hv_prod (Finset.univ) (fun k _ => hv_zpow hzp (hsingle k) (hy k) (hc0 k) (RM.xdeg ρ k))
    convert h1 using 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hS : 0 < Small.supMet (RM.xdeg ρ) z := Finset.prod_pos fun k _ =>
    zpow_pos (norm_pos_iff.2 fun h0 => hc0 k (congrFun h0 (ch k))) _
  have hsup : Small.supMet (RM.xdeg ρ) z = ∏ k, ‖z ⟨k, ch k⟩‖ ^ RM.xdeg ρ k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hcm k))
      (norm_le_pi_norm (fun i => z ⟨k, i⟩) (ch k))]
  refine ⟨ev Mi * ∏ k, z ⟨k, ch k⟩ ^ RM.xdeg ρ k, ?_, ?_, ?_⟩
  · have h1 := hv_mul (hval Mi) hseg
    rw [zero_add] at h1
    convert h1 using 1
    show (Or.e ρ)⁻¹ = ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ)⁻¹ * _
    field_simp
  · refine mul_ne_zero (fun h0 => ?_) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc0 k))
    rw [h0, norm_zero, mul_zero] at nMM
    exact zero_ne_one nMM
  · have hw : ‖ev Mi * ∏ k, z ⟨k, ch k⟩ ^ RM.xdeg ρ k‖ = Small.supMet (RM.xdeg ρ) z / ‖ev Ma‖ := by
      rw [norm_mul, norm_prod, hsup]
      simp only [norm_zpow]
      rw [eq_div_iff hm0.ne']
      linear_combination (∏ k, ‖z ⟨k, ch k⟩‖ ^ RM.xdeg ρ k) * nMM
    have hb' := diag_bound hG E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI zV hRd
      hOm hpq hSS _ b Tm hTA hfl hfr hb (fun j => hne' j) (HodgeCpt.rootIdx Dw ρ).2
    have hyy : 0 < absT p la T e (t (Small.rootFrameIx Dw ρ) : T.Fr) := hpos _ (Units.ne_zero _)
    rw [hw]
    have := log_bound (m := ‖ev Ma‖) (θ := Small.latExp E SS p * Real.log p) hS (x := ‖ev Ta‖) hx hyy hsg hm
      (by rw [habs]; exact hb')
    exact this

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
