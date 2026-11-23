import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorWedgeDetChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormulaStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem mh_inv {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b₀ b : Fin r → V}
    {T : Matrix (Fin r) (Fin r) Ω} (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (hT : T.det ≠ 0) (k : Fin r) :
    b₀ k = ∑ k', T⁻¹ k' k • b k' := by
  have e : ∑ k', T⁻¹ k' k • b k' = ∑ k', (T * T⁻¹) k' k • b₀ k' := by
    simp only [h, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [e, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hT)]
  simp [Matrix.one_apply]

section Q

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type}
  (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ)

def MhQ (c : ∀ k, J k) (a : K → ℤ) (ρ : Ω) (x : ℝ) : Prop :=
  ∃ u : ℂ, ValAt ξ z (ρ / ∏ k, y ⟨k, c k⟩ ^ a k) u ∧ x = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

variable {ξ y z w}

theorem mh_chg (h : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) {c c' : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) {a : K → ℤ} {ρ : Ω} {x : ℝ} (hQ : MhQ ξ y z w c a ρ x) : MhQ ξ y z w c' a ρ x := by
  obtain ⟨u, hu, rfl⟩ := hQ
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k _ (IsUnit.mk0 _ (hc k))).1
  choose r hrv hrw using fun k => (hw.2 k _ (IsUnit.mk0 _ (hc' k))).2 (c k)
  have hr0 : ∀ k, r k ≠ 0 := fun k h0 => hc k (by rw [hrw k, h0, zero_mul])
  refine ⟨u * ∏ k, r k ^ a k, ?_, ?_⟩
  · have h1 := CxVal.mul hu (MuIndep.valAt_prod h Finset.univ fun k => CxVal.zpow (hrv k) (hr0 k) (a k))
    have h2 : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
    simp only [div_zpow, Finset.prod_div_distrib] at h1
    rwa [div_mul_div_cancel₀ h2] at h1
  · rw [norm_mul, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_zpow, ← mul_zpow, ← norm_mul, ← hrw k]

theorem mh_mul (hw : CoordsAt ξ y z w) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {a a' : K → ℤ} {ρ ρ' : Ω} {x x' : ℝ}
    (hQ : MhQ ξ y z w c a ρ x) (hQ' : MhQ ξ y z w c a' ρ' x') : MhQ ξ y z w c (a + a') (ρ * ρ') (x * x') := by
  obtain ⟨u, hu, rfl⟩ := hQ
  obtain ⟨u', hu', rfl⟩ := hQ'
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k _ (IsUnit.mk0 _ (hc k))).1
  refine ⟨u * u', ?_, ?_⟩
  · have h1 := CxVal.mul hu hu'
    simp only [Pi.add_apply, zpow_add₀ (hy _), Finset.prod_mul_distrib]
    rwa [div_mul_div_comm] at h1
  · simp only [Pi.add_apply, zpow_add₀ (norm_ne_zero_iff.2 (hc _)), Finset.prod_mul_distrib, norm_mul]
    ring

theorem mh_prod (h : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (S : Finset ℕ) {a : ℕ → K → ℤ} {ρ : ℕ → Ω} {x : ℕ → ℝ} (hQ : ∀ p ∈ S, MhQ ξ y z w c (a p) (ρ p) (x p)) :
    MhQ ξ y z w c (∑ p ∈ S, a p) (∏ p ∈ S, ρ p) (∏ p ∈ S, x p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simpa using CxVal.one h, by simp⟩
  | insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.prod_insert hp, Finset.prod_insert hp]
    exact mh_mul hw hc (hQ p (Finset.mem_insert_self _ _)) (ih fun q hq => hQ q (Finset.mem_insert_of_mem hq))

end Q

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem mh_change (Or : CptOrigin Y S₀ Dc Hd) {bb : ∀ τ, Fin Dc.N → W τ}
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} {lam : Ω}
    (hs : ∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ))
    (hΛ : Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)))
    {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) {s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs' : Or.IsSmallPart d s') :
    ∃ T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω,
      (∀ τ k, s τ k = ∑ k', T τ k' k • s' τ k') ∧ d.u * chartMono Dc.y d.c Hd.aMu = lam * ∏ τ, (T τ).det := by
  have hq' := fun τ => MuIndep.quot_basis Dc.j_le_N (b := d.b τ) (F := Hd.F τ) (d.adapted τ).1.2.2.2.1 (d.adapted τ).2.1
    (d.adapted τ).2.2
  have hco : ∀ τ k, ∃ t : Fin (Dc.N - Dc.j) → Ω, ∑ a, t a • (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N a)) =
      (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N k)) := fun τ k =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [(hq' τ).2]; trivial)
  choose t ht using hco
  refine ⟨fun τ => Matrix.of fun a k => t τ k a, fun τ k => ?_, ?_⟩
  · have h1 : bb τ (tailIdx Dc.j_le_N k) - ∑ a, t τ k a • d.b τ (tailIdx Dc.j_le_N a) ∈ Hd.F τ := by
      refine (Submodule.Quotient.eq (Hd.F τ)).1 ?_
      have := ht τ k
      simp_rw [← map_smul] at this
      rw [← map_sum] at this
      exact this.symm
    rw [Or.F_eq τ, Submodule.mem_comap, map_sub, map_sum] at h1
    rw [← sub_eq_zero]
    refine (Submodule.disjoint_def.1 (MuIndep.blocks_disjoint Or τ)) _ ?_
      (sub_mem (hs τ k).1 (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).1))
    have e : s τ k - ∑ a, t τ k a • s' τ a =
        (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - ∑ a, Or.i τ (t τ k a • d.b τ (tailIdx Dc.j_le_N a))) -
          (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k) +
          ∑ a, t τ k a • (Or.i τ (d.b τ (tailIdx Dc.j_le_N a)) - s' τ a) := by
      simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    show s τ k - ∑ a, t τ k a • s' τ a ∈ _
    rw [e]
    exact add_mem (sub_mem h1 (hs τ k).2) (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).2)
  · exact GlobalTheory.T.tensor_wedge_det_change (CMType H) Ω (fun τ => W τ ⧸ Hd.F τ) (Dc.N - Dc.j)
      (fun τ a => (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N a)))
      (fun τ a => (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N a))) (fun τ => Matrix.of fun a k => t τ k a) _ _
      (fun τ => (hq' τ).1) (fun τ => (hq' τ).2) (fun τ k => (ht τ k).symm) (d.eq.symm.trans hΛ)

end Main

theorem mh_char0 {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X}
    (h : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) : ¬ InFibre ξ p ⟨centre z, h⟩ := by
  have h1 : ValAt ξ z (p : Ω) (p : ℂ) := ⟨h, p, map_natCast _ p, map_natCast _ p⟩
  obtain ⟨_, x, hx, -⟩ := CxVal.inv h1 (Nat.cast_ne_zero.2 hp.ne_zero)
  exact not_not.2 ⟨Nat.cast_ne_zero.2 hp.ne_zero, natCast_mem _ _, x, hx⟩

theorem muHodge : MuHodge := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B bb s lam hs hΛ z w hw hi
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have : CharZero Ω := algebraRat.charZero Ω
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have hmc : w ∈ mcPts (mCoordIdeal Dc.y) := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie w).2 ⟨z, h, hw⟩
  obtain ⟨d⟩ := GlobalTheory.T.component_data_hodge_first E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or z w hw
  obtain ⟨s', hs'⟩ := PhMuFree.exists_smallPart Or d
  obtain ⟨Γ, hΓ, hpd, -⟩ := PhMuFree.norm_eq Or hw hi d hs'
  have hph := PhMuFree.phMu_eq Or hw hi d hs' hΓ
  obtain ⟨T, hT, hΩ⟩ := mh_change Or hs hΛ d hs'
  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hy : ∀ k, Dc.y ⟨k, d.c k⟩ ≠ 0 := fun k => (hw.2 k _ (IsUnit.mk0 _ (d.inDom.1 k))).1
  have hm : chartMono Dc.y d.c Hd.aMu ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have n₀ : lam * ∏ τ, (T τ).det ≠ 0 := hΩ ▸ mul_ne_zero d.unit.1 hm
  have hlam : lam ≠ 0 := left_ne_zero_of_mul n₀
  have hd : ∀ τ, (T τ).det ≠ 0 := fun τ => Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul n₀) τ (Finset.mem_univ τ)
  have hex : ∃ c : (k : K) → J k, ∀ k, w ⟨k, c k⟩ ≠ 0 := ⟨d.c, d.inDom.1⟩
  have hvert : ∀ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) ≠ 0 ∧
      MhQ Or.𝔐.ξ Dc.y z w d.c (Dc.vdeg p)
        (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p)) (Dc.vertFactor p w) := by
    intro p hp
    have hv := Dc.vertical p (hS p hp)
    obtain ⟨v, -, hv1⟩ := VertFactorPos.exists_value hmc (Dc.S_prime p (hS p hp)).ne_zero hv hex.choose hex.choose_spec
    refine ⟨?_, mh_chg h hw hex.choose_spec d.inDom.1 ⟨v, ?_, ?_⟩⟩
    · obtain ⟨bf, bg, hf, hg, -⟩ := hv.degrees
      exact div_ne_zero (fun h0 => hv.num_not_mem ((VertFactorPos.mem_mCoordIdeal_iff_of_homog _ hf).2 h0))
        fun h0 => hv.den_not_mem ((VertFactorPos.mem_mCoordIdeal_iff_of_homog _ hg).2 h0)
    · have h1 := (GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw _ _).2 hv1
      simp only [chartMono, Pi.neg_apply, _root_.zpow_neg, Finset.prod_inv_distrib] at h1
      rwa [← div_eq_mul_inv] at h1
    · rw [ComponentData.vertFactor, dif_pos hex, valAt_eq hmc hv1, zMono, norm_prod]
      simp only [norm_zpow]
  have hQ1 : MhQ Or.𝔐.ξ Dc.y z w d.c Hd.aMu (lam * ∏ τ, (T τ).det)
      (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) := by
    refine ⟨_, ?_, rfl⟩
    rw [← hΩ]
    show ValAt _ _ (d.u * chartMono Dc.y d.c Hd.aMu / chartMono Dc.y d.c Hd.aMu) _
    rw [mul_div_cancel_right₀ _ hm]
    exact hu.2
  have hQ := mh_mul hw d.inDom.1 hQ1 (mh_prod h hw d.inDom.1 (Dc.SB B) fun p hp => (hvert p hp).2)
  have hA : 0 < ‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    mul_pos (norm_pos_iff.2 hu.1) (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _)
  have hsq : ∀ τ, 0 < Real.sqrt (Γ τ).det.re := fun τ => Real.sqrt_pos.2 (PhMuFree.det_re_pos (hpd τ))
  have hsq' : 0 < ∏ τ, Real.sqrt (Γ τ).det.re := Finset.prod_pos fun τ _ => hsq τ
  have hvp : ∀ p ∈ Dc.SB B, 0 < Dc.vertFactor p w := fun p hp => VertFactorPos.proof II _ K J Ω W Dc p (hS p hp) w hmc
  have hvp' : 0 < ∏ p ∈ Dc.SB B, Dc.vertFactor p w := Finset.prod_pos hvp
  have hh : (muVert Hd B).h w = (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      (∏ p ∈ Dc.SB B, Dc.vertFactor p w) * ∏ τ, Real.sqrt (Γ τ).det.re := by
    refine Real.log_injOn_pos ((muVert Hd B).pos w hmc.1) (mul_pos (mul_pos hA hvp') hsq') ?_
    rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II _ Ω W Dc Hd B w hmc, Real.log_mul (mul_pos hA hvp').ne' hsq'.ne', Real.log_mul hA.ne' hvp'.ne',
      Real.log_prod fun p hp => (hvp p hp).ne', Real.log_prod fun τ _ => (hsq τ).ne']
    have e : ∑ τ, Real.log (Real.sqrt (Γ τ).det.re) = (∑ τ, Real.log (Γ τ).det.re) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun τ _ => Real.log_sqrt (PhMuFree.det_re_pos (hpd τ)).le
    have e' : Real.log ((muLine Hd).h w) = phMu Hd w := rfl
    rw [e, e', hph]
    ring
  have hP : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (hvert p hp).1
  have hP' : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p) =
      (∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => (inv_div _ _).symm
  refine ⟨h, s', fun τ => (T τ)⁻¹, Γ, fun τ => ⟨?_, mh_inv (hT τ) (hd τ), hΓ τ, hpd τ⟩, ?_, hw, fun c' hc' => ?_⟩
  · have hf := (PhMuFree.frames Or hw d hs' τ h).2.1
    refine ⟨hf.1, Eq.trans ?_ hf.2⟩
    refine (Lat.patch_of_not _ _ _ fun p hp => mh_char0 h ?_).trans
      (Lat.patch_of_not _ _ _ fun p hp => mh_char0 h (Or.𝔐.S_prime p hp)).symm
    exact (Finset.mem_union.1 hp).elim (Or.𝔐.S_prime p) fun hp => Dc.S_prime p (hS p hp)
  · rw [hP']
    exact mul_ne_zero (inv_ne_zero hlam) (inv_ne_zero hP)
  · obtain ⟨u, hu1, hu2⟩ := mh_chg h hw d.inDom.1 hc' hQ
    refine ⟨u, ?_, ?_⟩
    · convert hu1 using 1
      have e : ∏ τ, ((T τ)⁻¹).det = (∏ τ, (T τ).det)⁻¹ := by
        rw [← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun τ _ => by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      rw [hP', e, inv_inv]
      show _ / ((∏ k, Dc.y ⟨k, c' k⟩ ^ (Hd.aMu + ∑ p ∈ Dc.SB B, Dc.vdeg p) k) * _) = _
      field_simp
    · rw [hh]
      refine Eq.trans ?_ hu2
      field_simp

end LevelTowerAlt.Comparison₂
