import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchSecOfUnf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KoecherPrincipleUnitConstant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryUnitValuationIntegral

section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom
noncomputable section
namespace GlobalTheory.FlatDenom
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.DetLine GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal in
theorem exists_horizontal_section_flat_model (hp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpos : 1 ≤ Dw.p + Dw.q) (hgeo : FnAlgClosed Xo c) (Z : Comp Xo c)
    (τ : Psi H) : ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1),
      (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧
        GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hpos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hgeo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
theorem exists_archimedean_section_of_unramified (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hgeo : FnAlgClosed Xo c) (x : ℝ) (Z : Comp Xo c) (τ : Psi H) :
    ∃ (s : ArchSec U x Z (flatWt Dw τ)) (m : ℕ), 0 < m ∧
      ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := _root_.GlobalTheory.FlatDenom.exists_horizontal_section_flat_model hP hpq hgeo Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.BdryUnit.ReadDet.exists_reads E H Dw l Xo c Y Z V τ sig hV hs hnv
  choose b hb hb' using fun σ => const_length (U _) x (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) hgeo hV hnv hh hR
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, archSec_denom hpq hA _ fun T io y₀ h0 hZ =>
    _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
theorem GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ (s : GlobalTheory.FlatCore.ArchSec Y.U (xiR D) Z (GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ)) (m : ℕ), 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s.sig) ∧ 0 ≤ v ((m : Y.d.c₂.F) • s.inv) := by
  intro hP D T j Y e o hG _ Z τ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have h1 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
  exact _root_.GlobalTheory.FlatDenom.exists_archimedean_section_of_unramified hP (by omega) hG.lev.2 hG.unf hG.geo _ Z τ
namespace GlobalTheory.FlatDenom
section Powers
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)
variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}
end Powers
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  intro hP D T j Y e o hY hE n Z τ s i ⟨hs, hi, hIs, hIi, hsi, hb⟩
  have h₁ : HasBddSec Y.U (xiR D) Z (flatWt (T.Q.Dw j) τ) := _root_.GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator hP D T j Y e o hY hE Z τ
  obtain ⟨s₀, m₀, hm₀, h₀⟩ := h₁.zsmul n
  generalize n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ = la at *
  have hw : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) (-la) 0 = 0 := by
    rw [← GlobalTheory.FlatLine.wtOf_add', add_neg_cancel, GlobalTheory.AllWt.wtOf_zero]
  have hg : s * s₀.inv ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hs s₀.inv_mem
    have h0 : Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + -GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      add_neg_cancel _
    rwa [h0] at h
  have hh : i * s₀.sig ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hi s₀.sig_mem
    have h0 : -Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      neg_add_cancel _
    rwa [h0] at h
  have hIg : GlobalTheory.FlatLine.idem Z * (s * s₀.inv) = s * s₀.inv := by rw [← mul_assoc, hIs]
  have hIh : GlobalTheory.FlatLine.idem Z * (i * s₀.sig) = i * s₀.sig := by rw [← mul_assoc, hIi]
  have hgh : s * s₀.inv * (i * s₀.sig) = GlobalTheory.FlatLine.idem Z := by
    calc s * s₀.inv * (i * s₀.sig) = (s * i) * (s₀.sig * s₀.inv) := by ring
      _ = _ := by rw [hsi, s₀.mul_inv, GlobalTheory.FlatLine.idem_mul_idem]
  have hbd : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z,
      GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (s * s₀.inv) z ≤ C ∧
        GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (i * s₀.sig) z ≤ C := by
    intro σ hσ
    obtain ⟨C, hC⟩ := hb σ hσ
    have hgo : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ := if_pos hσ
    have hN : ∀ σ'' (_ : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ''), ∀ z ∈ framesOn (Y.U σ'') Z,
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) la 0) s₀.sig z = s₀.cInf σ ∧
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) (-la) 0) s₀.inv z = (s₀.cInf σ)⁻¹ := by
      rintro _ rfl z hz
      exact ⟨homN_sig s₀ hz, homN_inv s₀ hz⟩
    have hpos := s₀.cInf_pos σ
    refine ⟨max (C * (s₀.cInf σ)⁻¹) (C * s₀.cInf σ), fun z hz => ?_⟩
    have hd : z.2 ∈ ((Y.U σ).X z.1).dom := hz.1
    obtain ⟨h1, h2⟩ := hN σ hgo z hz
    obtain ⟨c1, c2⟩ := hC z hz
    have hev : Even (-(wtOf (T.Q.Dw j) la 0)).2 := by
      simpa using (GlobalTheory.AllWt.even_wtOf (Dw := T.Q.Dw j) la 0).neg
    have e1 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) (GlobalTheory.AllWt.even_wtOf la 0) (GlobalTheory.AllWt.even_wtOf (-la) 0)
      s s₀.inv z hd
    rw [hw, h2] at e1
    have e2 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) hev (GlobalTheory.AllWt.even_wtOf la 0) i s₀.sig z hd
    rw [neg_add_cancel, h1] at e2
    constructor
    · rw [e1]; exact (mul_le_mul_of_nonneg_right c1 (inv_pos.2 hpos).le).trans (le_max_left _ _)
    · rw [e2]; exact (mul_le_mul_of_nonneg_right c2 hpos.le).trans (le_max_right _ _)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CovTop.koecher_principle_unit_constant hP D T j Y e o hY hE Z _ _ hg hh hIg hIh hgh hbd
  have hsa : s = a • s₀.sig := by
    calc s = s * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIs]
      _ = (s * s₀.inv) * s₀.sig := by rw [← s₀.mul_inv]; ring
      _ = a • s₀.sig := by rw [ha, smul_mul_assoc, s₀.idem_sig]
  by_cases ha0 : a = 0
  · refine ⟨1, one_pos, fun w v hv => ?_⟩
    exfalso
    have h1 := GlobalTheory.FlatLine.val_idem hv
    rw [← hsi, hsa, ha0, zero_smul, zero_mul, (GlobalTheory.FlatLine.isVal_valOn hv).zero] at h1
    exact EReal.top_ne_zero h1
  have hia : i = a⁻¹ • s₀.inv := by
    calc i = i * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIi]
      _ = i * (a • s₀.sig * a⁻¹ • s₀.inv) := by rw [GlobalTheory.FlatLine.smul_mul_inv_smul ha0, s₀.mul_inv]
      _ = (s * i) * a⁻¹ • s₀.inv := by rw [← hsa]; ring
      _ = a⁻¹ • s₀.inv := by rw [hsi, mul_smul_comm, s₀.idem_inv]
  obtain ⟨n₁, hn₁, k₁⟩ := exists_nat_vAdd ha0
  obtain ⟨n₂, hn₂, k₂⟩ := exists_nat_vAdd (inv_ne_zero ha0)
  have hnat : ∀ (k : ℕ), 0 < k → ∀ w, 0 ≤ vAdd w (k : Y.d.c₂.F) := fun k hk w => by
    have := Formalism.L2.Pj.vAdd_int_nonneg w (a := (k : 𝓞 Y.d.c₂.F)) (by
      have : (k : Y.d.c₂.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      simpa using this)
    simpa using this
  have key : ∀ (b : Y.d.c₂.F) (k k' : ℕ) (f : Rul Y.d.Xo₂ Y.d.c₂), b ≠ 0 → 0 < k → 0 < k' → ∀ w, ∀ v ∈ valOn Z w,
      0 ≤ vAdd w ((k : Y.d.c₂.F) * b) → 0 ≤ v ((m₀ : Y.d.c₂.F) • f) →
      0 ≤ v (((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f) := fun b k k' f hb hk hk' w v hv h1 h2 => by
    have hV := GlobalTheory.FlatLine.isVal_valOn hv
    have e1 : ((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f = (k' : Y.d.c₂.F) • ((k : Y.d.c₂.F) * b) • (m₀ : Y.d.c₂.F) • f := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e1, hV.smul _ _ (Nat.cast_ne_zero.2 hk'.ne'), hV.smul _ _ (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') hb)]
    exact add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast hnat k' hk' w))
      (add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast h1)) h2)
  refine ⟨n₂ * n₁ * m₀, Nat.mul_pos (Nat.mul_pos hn₂ hn₁) hm₀, fun w v hv => ⟨?_, ?_⟩⟩
  · rw [hsa]
    exact key a n₁ n₂ _ ha0 hn₁ hn₂ w v hv (k₁ w) (h₀ w v hv).1
  · rw [hia, mul_comm n₂]
    exact key a⁻¹ n₂ n₁ _ (inv_ne_zero ha0) hn₂ hn₁ w v hv (k₂ w) (h₀ w v hv).2
end
end
