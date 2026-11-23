import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ChartCentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExistsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivializationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.GVal

open LevelTowerAlt
open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric
open GroundTheory.Heights₂.Heights.Regular (logCover expCover logLift)

def aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def affInv {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  ((ρ : ℂ)⁻¹ • (t - t₀)) ∘ π.symm

theorem aff_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    aff t₀ ρ π (affInv t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [aff, affInv, Function.comp, h]

open scoped ComplexOrder in

theorem gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) :
    0 < (R.gram u).det.re := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  have hM : (R.Hmᵀ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := R.pos x hx
    have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
    rw [Complex.pos_iff]
    exact ⟨by rw [e]; exact h1, him.symm⟩
  let C : Matrix (Fin g) (Fin m) ℂ := (Matrix.of u)ᵀ
  have hC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hu
  have e : R.gram u = Cᴴ * R.Hmᵀ * C := by
    ext a b
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply, C]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hp := (hM.conjTranspose_mul_mul_same hC).det_pos
  rw [← e] at hp
  exact (Complex.pos_iff.1 hp).1

theorem hodgeInnerProduct_of_fibreLatticeVector {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem point_formula (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (co : CoordsAt Or.𝔐.ξ Dc.y z w) (hI : Or.𝔐.Interior z) (hG : Top.Given) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
    (x : CMType H → Fin (Dc.N - Dc.j) → Fin g → ℂ) (hx : ∀ τ, LinearIndependent ℂ (x τ))
    (v : CMType H × Fin (Dc.N - Dc.j) → (epsAt z ⟶ Or.𝔐.t.G)) (hv : ∀ i, Or.𝔐.M.ValAt z (s i.1 i.2) (v i))
    (hfib : FibreLatVec Or.𝔐.t z R (fun i => x i.1 i.2) v) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      ((Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi) + R.logDet x) / 2 := by
  obtain ⟨-, hP⟩ := GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z w co
  obtain ⟨-, hP2⟩ := hP d
  obtain ⟨-, -, hform⟩ := hP2 s hs
  let Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ := fun τ =>
    Matrix.of fun p q => (Real.pi : ℂ) * R.ip (x τ p) (x τ q)
  have hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ) := fun τ =>
    ⟨fun p => v (τ, p), fun p => hv (τ, p), fun p q =>
      hodgeInnerProduct_of_fibreLatticeVector hfib (fun i => (hv i).isTanAt) (τ, p) (τ, q)⟩
  have hdet : ∀ τ, Real.log (Γ τ).det.re = ((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi +
      Real.log (R.gram (x τ)).det.re := by
    intro τ
    have hpos := gram_det_pos R (x τ) (hx τ)
    have e1 : Γ τ = (Real.pi : ℂ) • R.gram (x τ) := by
      ext p q; rfl
    rw [e1, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hpos.ne', Real.log_pow]
  have h1 := hform hI Γ hΓ
  simp only [hdet, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  exact h1

theorem fibreLat_of_vec {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) : FibreLat t z R := by
  obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun i => i.elim⟩

end Pt

open GroundTheory.Heights₂.Heights.Regular (logCover expCover logLift)

namespace Val

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_torus {cc : (k : K) → J k} {f : Ω} {z : (Σ k, J k) → ℂ} (h : InFrameDomain y cc f z)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : InFrameDomain y cc f (torusSmul c z) := by
  obtain ⟨h1, v, ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩, hv⟩ := h
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨fun k => mul_ne_zero (hc k) (h1 k), _, ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩, hv⟩
  · unfold torusSmul
    rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · unfold torusSmul
    rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem torusSmul_inv {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
  funext p
  simp [torusSmul, hc]

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem torusSmul_inv' {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    torusSmul c (torusSmul (fun k => (c k)⁻¹) z) = z := by
  funext p
  simp [torusSmul, hc]

theorem factor_near {u : Ω} {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) (hv : valAt y u w ≠ 0)
    (cc : (k : K) → J k) (hc : ∀ k, w ⟨k, cc k⟩ ≠ 0) (a : K → ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w' in 𝓝 w, w' ∈ mcPts (mCoordIdeal y) →
      Real.log (‖valAt y u w‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ a k) - ε ≤
        Real.log (‖valAt y u w'‖ * ∏ k, ‖w' ⟨k, cc k⟩‖ ^ a k) := by
  have hex : ∃ v, IsValueAt y u w v := by
    by_contra hn
    exact hv (dif_neg hn)
  obtain ⟨v₀, dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩ := hex
  have e0 : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = v₀ :=
    valAt_eq hw ⟨dg, pg, ph, hpg, hph, hne, heq, hhne, hv₀⟩
  have c1 := (MvPolynomial.continuous_eval (MvPolynomial.map (Int.castRingHom ℂ) pg)).continuousAt (x := w)
  have c2 := (MvPolynomial.continuous_eval (MvPolynomial.map (Int.castRingHom ℂ) ph)).continuousAt (x := w)
  have c3 : ContinuousAt (fun w' : (Σ k, J k) → ℂ => ∏ k, ‖w' ⟨k, cc k⟩‖ ^ a k) w :=
    tendsto_finsetProd _ fun k _ =>
      ((continuous_apply (⟨k, cc k⟩ : Σ k, J k)).norm.continuousAt.zpow₀ _ (Or.inl (norm_ne_zero_iff.2 (hc k))))
  have hne0 : ‖MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) pg) /
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) ph)‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ a k ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.2 (by rw [← hv₀, ← e0]; exact hv))
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))
  have c4 := (((c1.div c2 hhne).norm.mul c3).log hne0).eventually (lt_mem_nhds (sub_lt_self _ hε))
  filter_upwards [c4, c2.eventually_ne hhne] with w' h1 h2 hw'
  have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w' = _ :=
    valAt_eq hw' ⟨dg, pg, ph, hpg, hph, hne, heq, h2, rfl⟩
  rw [e0, hv₀, e1]
  exact h1.le

end Free

theorem exists_lift {n a : ℕ} (h : a ≤ n) {u : Fin n → ℂ} (hu : u ∈ Flat.punct n a 1) :
    ∃ w ∈ logCover h, expCover a w = u := by
  have h1 : ∀ k, ‖u k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hu.1)
  refine ⟨logLift a u, ⟨fun i => ?_, fun k hk => ?_⟩, funext fun k => ?_⟩
  · have hi : ((Fin.castLE h i : Fin n) : ℕ) < a := i.2
    simp only [logLift, if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.2 (hu.2 _ hi)) (h1 _)
  · simp only [logLift, if_neg (not_lt.2 hk)]
    exact h1 k
  · by_cases hk : (k : ℕ) < a
    · simp only [expCover, logLift, if_pos hk]
      exact Complex.exp_log (hu.2 k hk)
    · simp only [expCover, logLift, if_neg hk]

theorem neg_log_nz_le {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) {m : ℕ} (hσ : IsCMFam σ)
    (hr : R.HasRank σ m) (hm : 1 ≤ m) {I : Submodule (𝓞 E) Λ} (h1 : IsSaturated I) (h2 : IsIsoSub R.form I) :
    -Real.log (R.nz σ I) ≤ R.cuspW σ := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ R σ m hσ hr hm
  by_cases hI : I = ⊥
  · have : R.nz σ I = 1 := by
      refine dif_neg ?_
      rintro ⟨r, v, hr1, hv, hli, -⟩
      have := hv ⟨0, hr1⟩
      rw [hI, Submodule.mem_bot] at this
      exact hli.ne_zero _ this
    rw [this, Real.log_one, neg_zero]
    exact h4
  · exact (h3 I ⟨hI, h1, h2⟩).1

end Val

open Val in

theorem corrW_lower_near : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ w' ∈ Dc.Xo, ‖w' - w‖ < δ → x - ε ≤ corrW Hd U w' := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U z w x hU hz hx ε hε
  obtain ⟨d, s, ν, hs, hν, -, rfl⟩ := hx
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, Or.𝔐.all _, hz⟩
  obtain ⟨a, t₀, ht, cw, hcw, hwe⟩ := Dc.chart_cover w hw
  have ht₀ : t₀ ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := mem_ball_zero_iff.2 (by linarith)
  have hγ : (Dc.chart a).γ t₀ = torusSmul (fun k => (cw k)⁻¹) w := by rw [hwe, torusSmul_inv hcw]
  have hci : ∀ k, (cw k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hcw k)
  have hz₀ : CoordsAt Or.𝔐.ξ Dc.y z ((Dc.chart a).γ t₀) := by
    rw [hγ]
    exact WeightSheet.coordsAt_torusSmul _ hz hci
  have hd₀ : InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ t₀) := by
    rw [hγ]
    exact inFrameDomain_torus d.inDom hci
  obtain ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, σ, pt, b, hρ, hσ, hb, hu, hfib, I, hI1, hI2, hlim⟩ :=
    chart_centre hG Or a t₀ ht₀ z hz₀ { d with inDom := hd₀ } s hs ν hν
  obtain ⟨δ₁, hδ₁, hlim⟩ := hlim ε hε
  obtain ⟨V, T, hV, hV0, hT, hT0, hVT⟩ := GlobalTheory.T.chart_local_analytic_trivialization K J II (CMType H) Ω W Dc a t₀ ht₀
  have hv0 : valAt Dc.y d.u w ≠ 0 :=
    (((GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z w hz).2 d).2 s hs).2.1
  have c1 : Tendsto (torusSmul (fun k => (cw k)⁻¹)) (𝓝 w) (𝓝 ((Dc.chart a).γ t₀)) := by
    rw [hγ]
    refine Continuous.tendsto ?_ _
    unfold torusSmul
    fun_prop
  have c2 : Tendsto (fun w' => T (torusSmul (fun k => (cw k)⁻¹) w')) (𝓝 w) (𝓝 t₀) := by
    have := (hT _ hV0).continuousAt.tendsto
    rw [hT0] at this
    exact this.comp c1
  have c3 : Tendsto (fun w' => affInv t₀ ρ π (T (torusSmul (fun k => (cw k)⁻¹) w'))) (𝓝 w) (𝓝 0) := by
    have hc : Continuous (affInv t₀ ρ π) := by
      unfold affInv
      fun_prop
    refine (hc.tendsto' t₀ 0 ?_).comp c2
    funext i
    simp [affInv]
  have hev : ∀ᶠ w' in 𝓝 w, w' ∈ Dc.Xo → Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      Real.log ν / 2 - ε ≤ corrW Hd U w' := by
    filter_upwards [c1.eventually (hV.mem_nhds hV0), c3.eventually (Metric.ball_mem_nhds 0 hδ₁),
      c3.eventually (Metric.ball_mem_nhds 0 one_pos), ChartGeo.inFrameDomain_eventually Dc.y d.c d.f d.inDom,
      factor_near hw hv0 d.c d.inDom.1 Hd.aMu (half_pos hε)] with w' a1 a2 a3 a4 a5 hw'
    obtain ⟨-, c', hc', he⟩ := hVT _ ⟨a1, mcPts_smul Dc.arith.2.1.2.1 _ hci hw'.1⟩
    set u := affInv t₀ ρ π (T (torusSmul (fun k => (cw k)⁻¹) w')) with hud
    obtain ⟨-, -, co, hL, hint⟩ := hu u a3
    have e1 : t₀ + (ρ : ℂ) • (u ∘ π) = T (torusSmul (fun k => (cw k)⁻¹) w') := aff_affInv t₀ hρ π _
    rw [e1] at co
    have co' : CoordsAt Or.𝔐.ξ Dc.y (pt u) w' := by
      have := WeightSheet.coordsAt_torusSmul _ (WeightSheet.coordsAt_torusSmul _ co hc') hcw
      rwa [← he, torusSmul_inv' hcw] at this
    have hI : Or.𝔐.Interior (pt u) := not_not.1 fun hn => hw'.2 ((Or.bd _ _ co').2 hn)
    obtain ⟨q, hq, hqu⟩ := exists_lift L.a_le (hint.1 hI)
    clear_value u
    subst hqu
    obtain ⟨v, hv, hf⟩ := hfib q hq
    have k1 := point_formula Or co' hI hG { d with inDom := a4 } hs (L.riem q hq)
      (fun τ i => b τ i (expCover a₀ q)) (fun τ => (hb.2 _ a3 τ).1) v hv hf
    have k2 := WeightSheet.eq_cuspW_of_fibre Or hU co' hI _ (fibreLat_of_vec hf) hL
    have hr : (L.riem q hq).HasRank σ (Dc.N - Dc.j) := fun τ => by
      have h1 := finrank_span_eq_card (hb.2 _ a3 τ).1
      rw [(hb.2 _ a3 τ).2, Fintype.card_fin] at h1
      exact h1
    have hm : 1 ≤ Dc.N - Dc.j := by
      have h1 := Dc.j_le
      have h2 := Dc.two_le_N
      omega
    have k3 := neg_log_nz_le (L.riem q hq) σ hσ hr hm hI1 hI2
    have k4 := hlim q hq (mem_ball_zero_iff.1 a2)
    have k5 := a5 hw'.1
    unfold corrW
    rw [k1, k2]
    dsimp only
    linarith
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨δ, hδ, fun w' h1 h2 => h w' (by rwa [Metric.mem_ball, dist_eq_norm]) h1⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.GVal
