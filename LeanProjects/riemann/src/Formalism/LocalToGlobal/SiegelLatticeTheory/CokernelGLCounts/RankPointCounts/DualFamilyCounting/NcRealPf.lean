import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

noncomputable section

namespace Formalism.L2.SG.Pf.NcReal

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {D : D7} (X : HidaSetting D)

theorem muInf_compact_pos : ∃ K : Set X.B.I.Ginf, IsCompact K ∧ 0 < Formalism.L2.SG.ProjRows.muInf X.B.I K ∧
    Formalism.L2.SG.ProjRows.muInf X.B.I K < ⊤ := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  refine ⟨K, hK, ?_, hK.measure_lt_top⟩
  first
    | exact Measure.measure_pos_of_mem_nhds _ hKn
    | exact MeasureTheory.Measure.measure_pos_of_mem_nhds _ hKn
    | exact (measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.mpr hKn⟩)

theorem cooOf_eq (u u' : D.what₂.Word) (sc C : ℝ) (hC : 0 < C) (h : Disint X u u' sc C) : DisintegrationConstant X u u' sc = C := by
  have hex : ∃ C, 0 < C ∧ Disint X u u' sc C := ⟨C, hC, h⟩
  unfold DisintegrationConstant
  rw [dif_pos hex]
  obtain ⟨hC1, hD1⟩ := hex.choose_spec
  obtain ⟨K, hK, hK0, hKt⟩ := muInf_compact_pos X
  have hKm : MeasurableSet K := hK.measurableSet
  obtain ⟨Iv, hIv⟩ : ∃ Iv : ENNReal, Iv = ∫⁻ c in Good X u u', ENNReal.ofReal (wt X u u' c) *
      ∫⁻ s, ∫⁻ s', K.indicator 1 (s * hOf X u u' sc c * s'⁻¹) ∂(muS X u') ∂(muS X u) ∂(dcInf X) := ⟨_, rfl⟩
  have key : ∀ C', 0 < C' → Disint X u u' sc C' →
      Formalism.L2.SG.ProjRows.muInf X.B.I K = ENNReal.ofReal C' * Iv := by
    intro C' hC' hD
    rw [hIv, ← lintegral_indicator_one hKm, hD _ (measurable_one.indicator hKm),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun c => ?_
    rw [ENNReal.ofReal_mul hC'.le, mul_assoc]
  have e1 := key _ hC1 hD1
  have e2 := key C hC h
  have hI0 : Iv ≠ 0 := right_ne_zero_of_mul (e1 ▸ hK0.ne')
  have hIt : Iv ≠ ⊤ := by
    intro hI
    rw [e1, hI, ENNReal.mul_top (by simpa using hC1)] at hKt
    exact lt_irrefl _ hKt
  have e3 : ENNReal.ofReal hex.choose * Iv = ENNReal.ofReal C * Iv := e1.symm.trans e2
  have e4 : ENNReal.ofReal hex.choose = ENNReal.ofReal C :=
    calc ENNReal.ofReal hex.choose = ENNReal.ofReal hex.choose * Iv * Iv⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hI0 hIt, mul_one]
      _ = ENNReal.ofReal C * Iv * Iv⁻¹ := by rw [e3]
      _ = ENNReal.ofReal C := by rw [mul_assoc, ENNReal.mul_inv_cancel hI0 hIt, mul_one]
  exact (ENNReal.ofReal_eq_ofReal_iff hC1.le hC.le).mp e4

section Steps

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf.WFL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.MainNotions.S Matrix

variable {k r : ℕ}

def refN (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) : Measure (Formalism.REAL.UJ ε) :=
  Measure.comap (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) (Formalism.MainNotions.S.haarLie (Nset k r) 1)

def HLoc {n r' : ℕ} (ε : Fin n → Bool) (e f : Fin r' → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {s | (∀ a, uMat s *ᵥ e a = e a ∧ uMat s *ᵥ f a = f a) ∧ uMat s *ᵥ z = z}

def muSL {n : ℕ} {ε : Fin n → Bool} (μH μN : Measure (Formalism.REAL.UJ ε)) : Measure (Formalism.REAL.UJ ε) :=
  (μN.prod μH).map fun p => p.1 * p.2

def JacLocX : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 zB zB' : Fin (2 * r + k + 1) → ℂ),
    IsFrameJ ε e f wf z0 → 1 ≤ k → inWb k r zB → inWb k r zB' → 0 < Tz k r zB → 0 < Tz k r zB' →
    Formalism.MainNotions.S.Gauge.GaugeDens ε →
    ∀ μH μH' : Measure (Formalism.REAL.UJ ε), IsLocHaar (HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH →
      IsLocHaar (HLoc ε e f (Qm e f wf z0 *ᵥ zB')) μH' →
    ∀ a a' : ℝ, 0 < a → 0 < a' → μH Set.univ = ENNReal.ofReal a → μH' Set.univ = ENNReal.ofReal a' →
    ∀ κ : ℝ, 0 < κ →
    ∀ h, IsSecLoc ε 1 e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') h →
      DisintLoc ε k (Tz k r zB) (Tz k r zB') (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0))
        (muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)) h
        (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
          ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2))

end Steps

section StepsX

open Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.MainNotions.S Matrix

variable {D : D7} (X : HidaSetting D)

def eV (v : NumberField.InfinitePlace X.B.I.F) : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)

def ProdExact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (μN μN' μH μH' : ∀ v : NumberField.InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (C : NumberField.InfinitePlace X.B.I.F → ℝ),
    (∀ v, SigmaFinite (μN v)) → (∀ v, SigmaFinite (μN' v)) → (∀ v, SigmaFinite (μH v)) → (∀ v, SigmaFinite (μH' v)) →
    (∀ v, 0 < C v) →
    X.muN u = Measure.pi μN → X.muN u' = Measure.pi μN' → X.muH u = Measure.pi μH → X.muH u' = Measure.pi μH' →
    (∀ v h, IsSecLoc (X.B.I.ε v) 1 (eV X v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (Tw u) (Tw u') h →
      DisintLoc (X.B.I.ε v) D.R.k (Tw u) (Tw u') (muSL (μH v) (μN v)) (muSL (μH' v) (μN' v)) h (C v)) →
    Disint X u u' 1 (∏ v, C v)

def AprimeInf : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
    (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) →
    ∀ hT a', 0 < a' → AinfClause X ψ u' hT a' →
      a' = Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        Tw u' ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) / (X.muH u' Set.univ).toReal

end StepsX

section Reduction

open Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.MainNotions.S Matrix

def PlaceData {D : D7} (X : HidaSetting D) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) : Prop :=
  ∃ (μN μN' μH μH' : ∀ v : NumberField.InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (a a' κ κ' : NumberField.InfinitePlace X.B.I.F → ℝ) (cN cN' : ℝ),
    (∀ v, SigmaFinite (μN v)) ∧ (∀ v, SigmaFinite (μN' v)) ∧ (∀ v, SigmaFinite (μH v)) ∧ (∀ v, SigmaFinite (μH' v)) ∧
    (∀ v, 0 < a v ∧ 0 < a' v ∧ 0 < κ v ∧ 0 < κ' v) ∧
    X.muN u = Measure.pi μN ∧ X.muN u' = Measure.pi μN' ∧ X.muH u = Measure.pi μH ∧ X.muH u' = Measure.pi μH' ∧
    (∀ v, μH v Set.univ = ENNReal.ofReal (a v)) ∧ (∀ v, μH' v Set.univ = ENNReal.ofReal (a' v)) ∧
    (∀ v h, IsSecLoc (X.B.I.ε v) 1 (eV X v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (Tw u) (Tw u') h →
      DisintLoc (X.B.I.ε v) D.R.k (Tw u) (Tw u') (muSL (μH v) (μN v)) (muSL (μH' v) (μN' v)) h
        (Formalism.MainNotions.S.Gauge.gaugeU (X.B.I.ε v) * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ 2 /
          ((Tw u * Tw u') ^ D.R.k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (D.R.k - 1) * a v * a' v * (κ v * κ' v)))) ∧
    (X.muN u FdN).toReal = (∏ v, κ v) * cN ∧ (X.muN u' FdN').toReal = (∏ v, κ' v) * cN' ∧
    cN * cN' = |(NumberField.discr X.B.I.F : ℝ)| ^ eDF D.R.k D.R.rS

def PlaceSplit : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
    (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) → PlaceData X FdN FdN' u u'

theorem volU_succ (k : ℕ) : Formalism.MainNotions.S.UnitaryVolumeMass.volU (k + 1) =
    Formalism.MainNotions.S.UnitaryVolumeMass.volU k * ((2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)) := by
  unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
  rw [Finset.prod_range_succ]

theorem volU_pos' (j : ℕ) : 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU j := by
  unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
  exact Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (Nat.cast_pos.mpr (Nat.factorial_pos i))

private theorem prod_two_pi_pow_div_factorial_eq_two_pow_mul_prod (k : ℕ) : Formalism.MainNotions.S.UnitaryVolumeMass.volU k =
    Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * ((2 * Real.pi) ^ k / ((k - 1).factorial : ℝ)) := by
  cases k with
  | zero => simp [Formalism.MainNotions.S.UnitaryVolumeMass.volU]
  | succ j => rw [Nat.add_sub_cancel]; exact volU_succ j

theorem realBracket_of (hP : ProdExact) (hA : AprimeInf) (hS : PlaceSplit)
    (hG : ∀ (n : ℕ) (ε : Fin n → Bool), Formalism.MainNotions.S.Gauge.GaugeDens ε) : RealBracket := by
  intro D X hb FdN FdN' u u' ψ hX hM hs hT a' ha' hAc
  have hGv : ∀ v : NumberField.InfinitePlace X.B.I.F, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v) := fun v => hG _ _
  obtain ⟨μN, μN', μH, μH', a, b, κ, κ', cN, cN', hsN, hsN', hsH, hsH', hpos, hN, hN', hH, hH', haH, hbH,
    hloc, hvN, hvN', hcN⟩ := hS X hb FdN FdN' u u' ψ hX hM hs hGv
  have hA' := hA X hb FdN FdN' u u' ψ hX hM hs hGv hT a' ha' hAc
  have hTu : 0 < Formalism.L2.SG.RealObj.Tw u := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos u
  have hTu' : 0 < Formalism.L2.SG.RealObj.Tw u' := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos u'
  have hV0 := volU_pos' D.R.k
  have hW0 := volU_pos' (D.R.k - 1)
  have hVW := prod_two_pi_pow_div_factorial_eq_two_pow_mul_prod D.R.k
  set T := Formalism.L2.SG.RealObj.Tw u with hTd
  set T' := Formalism.L2.SG.RealObj.Tw u' with hT'd
  set V := Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k with hVd
  set W := Formalism.MainNotions.S.UnitaryVolumeMass.volU (D.R.k - 1) with hWd
  set Cv : NumberField.InfinitePlace X.B.I.F → ℝ := fun v => Formalism.MainNotions.S.Gauge.gaugeU (X.B.I.ε v) * V ^ 2 /
      ((T * T') ^ D.R.k * W * a v * b v * (κ v * κ' v)) with hCvd
  have hCv : ∀ v, 0 < Cv v := by
    intro v
    have hg := (hGv v).2
    obtain ⟨h1, h2, h3, h4⟩ := hpos v
    simp only [hCvd]
    positivity
  have hDis := hP X u u' μN μN' μH μH' Cv hsN hsN' hsH hsH' hCv hN hN' hH hH' hloc
  have hCoo := cooOf_eq X u u' 1 (∏ v, Cv v) (Finset.prod_pos fun v _ => hCv v) hDis
  haveI := hsH
  haveI := hsH'
  have hAu : (X.muH u Set.univ).toReal = ∏ v, a v := by
    rw [hH, Measure.pi_univ, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun v _ => by rw [haH v, ENNReal.toReal_ofReal (hpos v).1.le]
  have hBu : (X.muH u' Set.univ).toReal = ∏ v, b v := by
    rw [hH', Measure.pi_univ, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun v _ => by rw [hbH v, ENNReal.toReal_ofReal (hpos v).2.1.le]
  have hB0 : 0 < ∏ v, b v := Finset.prod_pos fun v _ => (hpos v).2.1
  have hprod : (∏ v, Cv v) * (∏ v, a v) * (∏ v, b v) * ((∏ v, κ v) * ∏ v, κ' v) =
      Formalism.MainNotions.S.AutInst.gaugeU X.B.I * (V ^ 2 / ((T * T') ^ D.R.k * W)) ^
        Fintype.card (NumberField.InfinitePlace X.B.I.F) := by
    simp only [← Finset.prod_mul_distrib]
    unfold Formalism.MainNotions.S.AutInst.gaugeU
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hpos v
    simp only [hCvd]
    first | (field_simp; ring) | field_simp
  have hF : (0 : ℝ) < ((D.R.k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hY : V ^ 2 / ((T * T') ^ D.R.k * W) = V * 2 ^ D.R.k * (Real.pi ^ D.R.k / ((D.R.k - 1).factorial : ℝ)) *
      (T ^ D.R.k)⁻¹ * (T' ^ D.R.k)⁻¹ := by
    rw [hVW]
    field_simp
    ring
  rw [hBu] at hA'
  rw [hCoo, hAu, hvN, hvN', hA']
  have e1 : (∏ v, Cv v) * (∏ v, a v) * ((∏ v, κ v) * cN) * ((∏ v, κ' v) * cN') =
      ((∏ v, Cv v) * (∏ v, a v) * (∏ v, b v) * ((∏ v, κ v) * ∏ v, κ' v)) * (cN * cN') / ∏ v, b v := by
    first | (field_simp; ring) | field_simp
  rw [e1, hprod, hcN, hY]
  simp only [_root_.zpow_neg, zpow_natCast, pow_mul, mul_pow, inv_pow]
  first | (field_simp; ring) | field_simp | ring

end Reduction

end Formalism.L2.SG.Pf.NcReal
