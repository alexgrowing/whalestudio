import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.Choice

variable {k r : ℕ}

theorem measurable_mulF :
    Measurable fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => by fun_prop

theorem haarLie_eq_smul (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ℝ≥0∞) :
    Formalism.MainNotions.S.haarLie S κ = κ • Formalism.MainNotions.S.haarLie S 1 := by
  simp only [Formalism.MainNotions.S.haarLie, one_smul]

def aff (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (m : Mt k r) : Mt k r := A * Matrix.of m * B

theorem measurable_aff (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (aff (k := k) (r := r) A B) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [aff, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => (continuous_finset_sum _ fun m _ =>
    continuous_const.mul ((continuous_apply l).comp (continuous_apply m))).mul continuous_const

theorem uw_inv_eq {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h⁻¹ = Hpk k r * hᴴ * Hpk k r := by
  have hH : hᴴ * Hpk k r * h = Hpk k r := by
    obtain ⟨hU, -, -⟩ := hh
    exact hU
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * hᴴ * Hpk k r * h = Hpk k r * (hᴴ * Hpk k r * h) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hH, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

theorem uw_inv_mem {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hH : hᴴ * Hpk k r * h = Hpk k r := by
    obtain ⟨hU, -, -⟩ := hh
    exact hU
  have hi : h⁻¹ * h = 1 := by
    rw [uw_inv_eq hh]
    calc Hpk k r * hᴴ * Hpk k r * h = Hpk k r * (hᴴ * Hpk k r * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hH, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hi' : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (Matrix.isUnit_det_of_left_inverse hi)
  obtain ⟨hU, hfix, hz⟩ := hh
  have fix : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  unfold Formalism.QuantumDeterminants.UWset
  refine ⟨?_, fun a => ⟨fix _ (hfix a).1, fix _ (hfix a).2⟩, fix _ hz⟩
  show (h⁻¹)ᴴ * Hpk k r * h⁻¹ = Hpk k r
  calc (h⁻¹)ᴴ * Hpk k r * h⁻¹ = (h⁻¹)ᴴ * (hᴴ * Hpk k r * h) * h⁻¹ := by rw [hH]
    _ = (h * h⁻¹)ᴴ * Hpk k r * (h * h⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hi']; simp

theorem uw_inv_mul {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h⁻¹ * h = 1 := by
  have hH : hᴴ * Hpk k r * h = Hpk k r := by
    obtain ⟨hU, -, -⟩ := hh
    exact hU
  rw [uw_inv_eq hh]
  calc Hpk k r * hᴴ * Hpk k r * h = Hpk k r * (hᴴ * Hpk k r * h) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hH, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

theorem uw_mul_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h * h⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv h (Matrix.isUnit_det_of_left_inverse (uw_inv_mul hh))

theorem uw_inv_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : (h⁻¹)⁻¹ = h := by
  exact Matrix.inv_eq_left_inv (uw_mul_inv hh)

theorem conj_haarLie {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (κ : ℝ≥0∞)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    (Formalism.MainNotions.S.haarLie (Nset k r) κ).map (conjM h) = Formalism.MainNotions.S.haarLie (Nset k r) κ := by
  rw [haarLie_eq_smul, Measure.map_smul,
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z (Formalism.MainNotions.S.haarLie (Nset k r) 1) hz hT
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)) h hh]

theorem isHaarOn_muS_gen {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    {μN : Measure (Mt k r)} (hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    Formalism.MainNotions.S.IsHaarOn (Sset k r z) (Formalism.MainNotions.S.muS μW μN) := by
  have hNfc : ∀ K : Set (Mt k r), IsCompact K → μN K < ⊤ := hNB.finite_compact
  have : IsFiniteMeasureOnCompacts μN := ⟨hNB.finite_compact⟩
  have hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN := ⟨inferInstance, hNB.ne_zero, hNB.conc, hNB.left⟩
  have conj_haarLie : ∀ {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}, h ∈ UWset k r z →
      μN.map (conjM h) = μN := fun {h} hh => Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hNB h hh
  obtain ⟨hWsf, hWne, hWcon, hWinv⟩ := hW
  obtain ⟨hNsf, hNne, hNcon, hNinv⟩ := hN
  have : IsFiniteMeasure μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hmul := measurable_mulF (k := k) (r := r)
  have hSG := quotient_measure_unitary_group k r z hz hT
  have hUWc : IsCompact {x : Mt k r | Matrix.of x ∈ UWset k r z} := PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact k r z hz hT
  have hUWm : MeasurableSet {x : Mt k r | Matrix.of x ∈ UWset k r z} := hUWc.isClosed.measurableSet
  have hUWn : μW {x : Mt k r | Matrix.of x ∈ UWset k r z}ᶜ = 0 := by rw [Set.compl_ofPred]; exact hWcon

  have hfc : IsFiniteMeasureOnCompacts (Formalism.MainNotions.S.muS μW μN) := by
    refine ⟨fun K hK => ?_⟩
    let iv : Mt k r × Mt k r → Mt k r := fun p => (Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r * Matrix.of p.2 : Mt k r)
    have hivc : Continuous iv := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [iv, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
      fun_prop
    have hK'c : IsCompact (iv '' ({x : Mt k r | Matrix.of x ∈ UWset k r z} ×ˢ K)) :=
      (hUWc.prod hK).image hivc
    have hsub : (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r)) ⁻¹' K ⊆
        (Set.univ ×ˢ (iv '' ({x : Mt k r | Matrix.of x ∈ UWset k r z} ×ˢ K))) ∪
          ({x : Mt k r | Matrix.of x ∈ UWset k r z}ᶜ ×ˢ Set.univ) := by
      intro p hp
      by_cases h1 : Matrix.of p.1 ∈ UWset k r z
      · refine Or.inl ⟨trivial, ⟨(p.1, fun i j => (Matrix.of p.1 * Matrix.of p.2) i j), ⟨h1, hp⟩, ?_⟩⟩
        show (Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r * (Matrix.of p.1 * Matrix.of p.2) : Mt k r) = p.2
        rw [← Matrix.mul_assoc, (Formalism.MainNotions.S.Inh.unitary_stabilizer_inv_mem z _ h1).2, Matrix.one_mul]
        rfl
      · exact Or.inr ⟨h1, trivial⟩
    rw [Formalism.MainNotions.S.muS, Measure.map_apply hmul hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
    rw [Measure.prod_prod, Measure.prod_prod, hUWn, zero_mul, add_zero]
    exact ENNReal.mul_lt_top (measure_lt_top μW _) (hNfc _ hK'c)
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro h0
    have h2 := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simp only [Formalism.MainNotions.S.muS, Measure.map_apply hmul MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at h2
    rw [← Set.univ_prod_univ, Measure.prod_prod, hW1, one_mul] at h2
    exact hNne (Measure.measure_univ_eq_zero.mp h2)
  · have hScl : IsClosed {x : Mt k r | Matrix.of x ∈ Sset k r z} := hSG.2.1.1
    have hSc : MeasurableSet {x : Mt k r | Matrix.of x ∉ Sset k r z} := by
      rw [← Set.compl_ofPred]; exact hScl.isOpen_compl.measurableSet
    rw [Formalism.MainNotions.S.muS, Measure.map_apply hmul hSc]
    refine measure_mono_null (t := ({x : Mt k r | Matrix.of x ∈ UWset k r z}ᶜ ×ˢ Set.univ) ∪
      (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Nset k r})) ?_ ?_
    · intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true,
        true_and, not_or, not_not] at hc
      exact hp ⟨_, hc.1, _, hc.2, rfl⟩
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hUWn, zero_mul]
      · rw [Measure.prod_prod, hNcon, mul_zero]
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := hs
    have hlm : ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Measurable (lmulM (k := k) (r := r) a) :=
      fun a => Formalism.L2.SG.Pf.WFL.measurable_lmulM a
    have hcm : ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Measurable (conjM (k := k) (r := r) a) :=
      fun a => measurable_aff a a⁻¹
    ext A hA
    have hA1 : MeasurableSet (lmulM (h0 * n0) ⁻¹' A) := hlm _ hA
    rw [Measure.map_apply (hlm _) hA, Formalism.MainNotions.S.muS, Measure.map_apply hmul hA1, Measure.map_apply hmul hA,
      Measure.prod_apply (hmul hA1), Measure.prod_apply (hmul hA)]
    set F : Mt k r × Mt k r → Mt k r := fun p => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) with hF
    set Ψ : Mt k r → ℝ≥0∞ := fun h => μN (Prod.mk h ⁻¹' (F ⁻¹' A)) with hΨ
    have hΨm : Measurable Ψ := measurable_measure_prodMk_left (hmul hA)
    have hstep : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z →
        μN (Prod.mk h ⁻¹' (F ⁻¹' (lmulM (h0 * n0) ⁻¹' A))) = Ψ (lmulM h0 h) := by
      intro h hh
      set H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of h with hH
      have hB1 : MeasurableSet (aff (h0 * n0) H ⁻¹' A) := measurable_aff _ _ hA
      have hB2 : MeasurableSet (aff h0 H ⁻¹' A) := measurable_aff _ _ hA
      have hB3 : MeasurableSet (Prod.mk (lmulM h0 h) ⁻¹' (F ⁻¹' A)) := measurable_prodMk_left (hmul hA)
      have e1 : Prod.mk h ⁻¹' (F ⁻¹' (lmulM (h0 * n0) ⁻¹' A)) = conjM H ⁻¹' (aff (h0 * n0) H ⁻¹' A) := by
        ext n
        simp only [Set.mem_preimage]
        have : lmulM (h0 * n0) (F (h, n)) = aff (h0 * n0) H (conjM H n) := by
          show (h0 * n0) * (H * Matrix.of n) = (h0 * n0) * (H * Matrix.of n * H⁻¹) * H
          rw [Matrix.mul_assoc (h0 * n0) (H * Matrix.of n * H⁻¹) H, Matrix.mul_assoc (H * Matrix.of n) H⁻¹ H,
            uw_inv_mul hh, Matrix.mul_one]
        rw [this]
      have e2 : aff (h0 * n0) H ⁻¹' A = lmulM n0 ⁻¹' (aff h0 H ⁻¹' A) := by
        ext m
        simp only [Set.mem_preimage]
        have : aff (h0 * n0) H m = aff h0 H (lmulM n0 m) := by
          show h0 * n0 * Matrix.of m * H = h0 * (n0 * Matrix.of m) * H
          rw [Matrix.mul_assoc h0 n0]
        rw [this]
      have e3 : aff h0 H ⁻¹' A = conjM H⁻¹ ⁻¹' (Prod.mk (lmulM h0 h) ⁻¹' (F ⁻¹' A)) := by
        ext m
        simp only [Set.mem_preimage]
        have : aff h0 H m = F (lmulM h0 h, conjM H⁻¹ m) := by
          show h0 * Matrix.of m * H = h0 * H * (H⁻¹ * Matrix.of m * H⁻¹⁻¹)
          rw [uw_inv_inv hh, ← Matrix.mul_assoc (h0 * H) (H⁻¹ * Matrix.of m) H, ← Matrix.mul_assoc (h0 * H) H⁻¹,
            Matrix.mul_assoc h0 H H⁻¹, uw_mul_inv hh, Matrix.mul_one]
        rw [this]
      rw [e1, ← Measure.map_apply (hcm H) hB1, conj_haarLie hh, e2, ← Measure.map_apply (hlm n0) hB2,
        hNinv n0 hn0, e3, ← Measure.map_apply (hcm H⁻¹) hB3, conj_haarLie (uw_inv_mem hh)]
    have hae : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by
      rw [ae_iff]; simpa using hWcon
    calc ∫⁻ h, μN (Prod.mk h ⁻¹' (F ⁻¹' (lmulM (h0 * n0) ⁻¹' A))) ∂μW = ∫⁻ h, Ψ (lmulM h0 h) ∂μW :=
          lintegral_congr_ae (by filter_upwards [hae] with h hh; exact hstep h hh)
      _ = ∫⁻ h, Ψ h ∂(μW.map (lmulM h0)) := (lintegral_map hΨm (hlm h0)).symm
      _ = ∫⁻ h, Ψ h ∂μW := by rw [hWinv h0 hh0]

theorem isHaarOn_muS {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ⊤) :
    Formalism.MainNotions.S.IsHaarOn (Sset k r z) (Formalism.MainNotions.S.muS μW (Formalism.MainNotions.S.haarLie (Nset k r) κ)) :=
  isHaarOn_muS_gen hz hT hW hW1
    (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ (Formalism.MainNotions.BridgeCSB.haarLieN k r κ hκ0 hκt))

section Frame

open Formalism.L2.SG.HidaSetting

theorem hJ_smul_left' {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_smul_right' {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem transp_exists {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (lam : ℂ) (hlam : lam ≠ 0)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z0 : Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hez : ∀ a, hJ ε (e a) z0 = 0)
    (hfz : ∀ a, hJ ε (f a) z0 = 0) (hzz : hJ ε z0 z0 = -1)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (hew : ∀ c a, hJ ε (e c) (wf a) = 0)
    (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z0 (wf a) = 0) :
    ∃ (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ),
      Qi * Q = 1 ∧ Q * Qi = 1 ∧ Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r ∧
      ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a ∧
        Q *ᵥ Pi.single (esI k r a) 1 = (star (lam ^ (r - (a : ℕ))))⁻¹ • f a := by
  subst hn
  have hc : ∀ a : Fin r, lam ^ (r - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ hlam
  have hF : Formalism.L2.SG.Pf.WFL.IsFrameJ ε (fun a => lam ^ (r - (a : ℕ)) • e a)
      (fun a => (star (lam ^ (r - (a : ℕ))))⁻¹ • f a) wf z0 :=
    { ee := fun a b => by simp only [hJ_smul_left', hJ_smul_right', hee, mul_zero]
      ff := fun a b => by simp only [hJ_smul_left', hJ_smul_right', hff, mul_zero]
      ef := fun a b => by
        simp only [hJ_smul_left', hJ_smul_right', hef]
        split_ifs with h
        · subst h
          have hs : star (lam ^ (r - (a : ℕ))) ≠ 0 := by rw [Ne, star_eq_zero]; exact hc a
          simp only [mul_one]
          exact inv_mul_cancel₀ hs
        · simp
      ez := fun a => by simp only [hJ_smul_left', hez, mul_zero]
      fz := fun a => by simp only [hJ_smul_left', hfz, mul_zero]
      zz := hzz
      ww := hww
      ew := fun c a => by simp only [hJ_smul_left', hew, mul_zero]
      fw := fun c a => by simp only [hJ_smul_left', hfw, mul_zero]
      zw := hzw }
  refine ⟨Formalism.L2.SG.Pf.WFL.Qm _ _ wf z0, Formalism.L2.SG.Pf.WFL.Qi ε _ _ wf z0, Formalism.L2.SG.Pf.WFL.Qi_mul_Qm hF,
    Formalism.L2.SG.Pf.WFL.Qm_mul_Qi hF, Formalism.L2.SG.Pf.WFL.gramQ hF, fun a => ⟨?_, ?_⟩⟩
  · rw [show (Pi.single (eI k r a) 1 : Fin (2 * r + k + 1) → ℂ) = bvec (eI k r a) from rfl,
      Formalism.L2.SG.Pf.WFL.Qm_mulVec_bvec, Formalism.L2.SG.Pf.WFL.colQ_eI]
  · rw [show (Pi.single (esI k r a) 1 : Fin (2 * r + k + 1) → ℂ) = bvec (esI k r a) from rfl,
      Formalism.L2.SG.Pf.WFL.Qm_mulVec_bvec, Formalism.L2.SG.Pf.WFL.colQ_esI]

theorem qi_eq {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    Qi = Hpk k r * Qᴴ * Formalism.REAL.Jm ε := by
  calc Qi = Hpk k r * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by
        rw [hg, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.one_mul]
    _ = Hpk k r * Qᴴ * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem haar_tr {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r))
      ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) := by
  subst hn
  have hP : Formalism.L2.SG.Pf.WFL.CayPair ε Q Qi := ⟨hg, qi_eq rfl ε h2 hg⟩
  exact Formalism.L2.SG.Pf.WFL.isHaarOn_G hP

theorem z_tr {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r)
    (z : Fin n → ℂ) (hzc : ∀ a : Fin r, hJ ε (Q *ᵥ Pi.single (eI k r a) 1) z = 0 ∧
      hJ ε (Q *ᵥ Pi.single (esI k r a) 1) z = 0) :
    inWb k r (Qi *ᵥ z) ∧ Tz k r (Qi *ᵥ z) = -(hJ ε z z).re := by
  subst hn
  have hQi := qi_eq rfl ε h2 hg
  have hcoord : ∀ i, (Qi *ᵥ z) i = Formalism.QuantumDeterminants.GBasic.sgn k r i *
      hJ ε (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.GBasic.sig k r i) 1) z := by
    intro i
    rw [hQi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.WFL.Hpk_mulVec]
    congr 1
    simp only [hJ, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hcoord]
    rcases hi with hi | hi
    · have e1 : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [e1, Formalism.L2.SG.Pf.WFL.sig_eI_eq, (hzc _).2, mul_zero]
    · have e1 : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
      rw [e1, Formalism.L2.SG.Pf.WFL.sig_esI_eq, (hzc _).1, mul_zero]
  · have hQiHQi : Qiᴴ * Hpk k r * Qi = Formalism.REAL.Jm ε := by
      rw [← hg]
      calc Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    have : herm (Hpk k r) (Qi *ᵥ z) (Qi *ᵥ z) = hJ ε z z := by
      unfold herm hJ
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQiHQi]
    rw [Tz, this]

end Frame

section Low

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem ktype_map {ε : Fin n → Bool} {σ ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (U V : H →L[ℂ] H)
    (hVU : ∀ x, V (U x) = x) (hUV : ∀ x, U (V x) = x)
    (hρ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, ρ g x = U (σ g (V x))) {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : IsKTypeOf ε ρ Λ (S.map (U : H →ₗ[ℂ] H)) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  have hσ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, σ g x = V (ρ g (U x)) := fun g hg x => by rw [hρ g hg, hVU, hVU]
  have hsurj : Function.Surjective (U : H →ₗ[ℂ] H) := fun y => ⟨V y, hUV y⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hfd
    infer_instance
  · rintro g hg _ ⟨x, hx, rfl⟩
    refine ⟨σ g x, hst g hg x hx, ?_⟩
    show U (σ g x) = ρ g (U x)
    rw [hρ g hg, hVU]
  · intro S' hS' hst'
    have h1 : S'.comap (U : H →ₗ[ℂ] H) ≤ S := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hS' hx
      have hyx' : U y = U x := hyx
      have : y = x := by rw [← hVU y, hyx', hVU]
      exact this ▸ hy
    have h2 : IsKStableOn ε σ (S'.comap (U : H →ₗ[ℂ] H)) := fun g hg x hx => by
      show U (σ g x) ∈ S'
      rw [hσ g hg, hUV]
      exact hst' g hg _ hx
    have hS'eq : S' = (S'.comap (U : H →ₗ[ℂ] H)).map (U : H →ₗ[ℂ] H) :=
      (Submodule.map_comap_eq_of_surjective hsurj S').symm
    rcases hirr _ h1 h2 with h | h
    · left
      rw [hS'eq, h, Submodule.map_bot]
    · right
      rw [hS'eq, h]
  · refine ⟨U v, ⟨v, hvS, rfl⟩, fun h0 => hv0 ?_, fun θ hθ => ?_⟩
    · rw [← hVU v, h0, map_zero]
    · rw [hρ _ hθ, hVU, hvw θ hθ, map_smul]
  · rintro μ _ ⟨y, hy, rfl⟩ hx0 hxw
    refine hdom μ y hy (fun h0 => hx0 ?_) (fun θ hθ => ?_)
    · show U y = 0
      rw [h0, map_zero]
    · have h' := hxw θ hθ
      simp only [ContinuousLinearMap.coe_coe] at h'
      rw [hσ _ hθ, h', map_smul, hVU]

theorem lowKSub_map {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (U V : H →L[ℂ] H) (hVU : ∀ x, V (U x) = x) (hUV : ∀ x, U (V x) = x)
    (hρ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, ρ g x = U (σ g (V x))) {w : H} (hw : w ∈ lowKSub ε lam σ) :
    U w ∈ lowKSub ε lam ρ := by
  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam ρ).comap (U : H →ₗ[ℂ] H) := by
    unfold lowKSub
    refine sSup_le fun S hS => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup (ktype_map U V hVU hUV hρ hS)
  exact hle hw

theorem inUJ_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : Formalism.REAL.inUJ ε a) (hb : Formalism.REAL.inUJ ε b) :
    Formalism.REAL.inUJ ε (a * b) := by
  unfold Formalism.REAL.inUJ at ha hb ⊢
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]

theorem kset_sub {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : Formalism.REAL.inUJ ε g := by
  obtain ⟨hu, hc⟩ := hg
  have h1 : gᴴ * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hu
  unfold Formalism.REAL.inUJ
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end Low

section Y

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem qiHqi {n : ℕ} (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    Qiᴴ * Hpk k r * Qi = Formalism.REAL.Jm ε := by
  rw [← hg]
  calc Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2]; simp

theorem y_exists {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (ε' : Fin (2 * r + k + 1) → Bool)
    (hε : ∀ i, ε' i = ε (Fin.cast hn.symm i)) (lam : Fin n → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ)
    (hlam : ∀ i, lam' i = lam (Fin.cast hn.symm i)) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hrep : IsURepOn (UJset ε) σ) {w : H}
    (hw : w ∈ lowKSub ε lam σ)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε' P) :
    ∃ y ∈ UH (Hpk k r), σ (Q * y * Qi) w ∈ lowKSub ε' lam' (fun g => σ (Q * (P⁻¹ * g * P) * Qi)) := by
  subst hn
  have hε' : ε' = ε := funext fun i => by rw [hε]; rfl
  have hlam' : lam' = lam := funext fun i => by rw [hlam]; rfl
  rw [hε'] at hP ⊢
  rw [hlam']
  obtain ⟨⟨hPu, hPg⟩, -⟩ := hP
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hJ' : (P⁻¹)ᴴ * Hpk k r * P⁻¹ = Formalism.REAL.Jm ε := by
    rw [← hPg]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hQiH := qiHqi ε h2 hg
  have hh : Formalism.REAL.inUJ ε (Q * P⁻¹) := by
    unfold Formalism.REAL.inUJ
    calc (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hg, hJ']
  have hh' : Formalism.REAL.inUJ ε (P * Qi) := by
    unfold Formalism.REAL.inUJ
    calc (P * Qi)ᴴ * Formalism.REAL.Jm ε * (P * Qi) = Qiᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPg, hQiH]
  have hhh' : Q * P⁻¹ * (P * Qi) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, h2]
  have hh'h : P * Qi * (Q * P⁻¹) = 1 := by
    have h1 : Qi * Q = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ (by simp)).mp h2
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qi, h1, Matrix.one_mul, hPP]
  obtain ⟨⟨hone, hmul⟩, -, -⟩ := hrep
  refine ⟨P⁻¹ * Q, ?_, ?_⟩
  · show (P⁻¹ * Q)ᴴ * Hpk k r * (P⁻¹ * Q) = Hpk k r
    calc (P⁻¹ * Q)ᴴ * Hpk k r * (P⁻¹ * Q) = Qᴴ * ((P⁻¹)ᴴ * Hpk k r * P⁻¹) * Q := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hJ', hg]
  · have hy : Q * (P⁻¹ * Q) * Qi = Q * P⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [hy]
    refine lowKSub_map (σ (Q * P⁻¹)) (σ (P * Qi)) (fun x => ?_) (fun x => ?_) (fun g hg x => ?_) hw
    · rw [← ContinuousLinearMap.comp_apply, ← hmul _ hh' _ hh, hh'h, hone]; rfl
    · rw [← ContinuousLinearMap.comp_apply, ← hmul _ hh _ hh', hhh', hone]; rfl
    · have hgU : Formalism.REAL.inUJ ε g := kset_sub hg
      have e1 : Q * (P⁻¹ * g * P) * Qi = Q * P⁻¹ * g * (P * Qi) := by simp only [Matrix.mul_assoc]
      show σ (Q * (P⁻¹ * g * P) * Qi) x = σ (Q * P⁻¹) (σ g (σ (P * Qi) x))
      rw [e1, hmul _ (inUJ_mul hh hgU) _ hh', hmul _ hh _ hgU]
      rfl

end Y

section Exist

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

variable {D : D7} (X : HidaSetting D)

theorem n_eq' : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  rw [X.n_eq]
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem host_v_pos (D : D7) : 0 < D.host.v := by
  have hd : (0 : ℝ) < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
  have h : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos hd _
  unfold Formalism.BasicNotions.Host.v
  exact half_pos h

theorem frS_ne (D : D7) : frS D ≠ 0 := by
  have hv := host_v_pos D
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka
    exact div_pos Real.pi_pos hv
  unfold Formalism.L2.SG.LocWSOf.frS
  exact Complex.ofReal_ne_zero.mpr (div_pos hka (by positivity)).ne'

theorem kapN_ne_zero (D : D7) {θ : ℝ} (hθ : 0 < θ) : kapN D θ ≠ 0 := by
  have hv := host_v_pos D
  unfold Formalism.MainNotions.S.kapN
  exact (ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ)).ne'

theorem kapN_ne_top (D : D7) (θ : ℝ) : kapN D θ ≠ ⊤ := by
  unfold Formalism.MainNotions.S.kapN
  exact ENNReal.ofReal_ne_top

theorem Tr_pos (D : D7) (u : D.what₂.Word) : 0 < Tr D u := by
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem hJ_frame (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) = embS D (X.pl v) ((VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

theorem transpC_exists (u0 : D.what₂.Word) (τ : D.what₂.Tau) :
    ∃ (Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
      (Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ),
      IsTranspC X (vOf X τ) (frS D) D.R.k D.R.rS Q Qi := by
  set v := vOf X τ
  set T := Tr D u0 with hTdef
  have hT := Tr_pos D u0
  set c : ℂ := (((Real.sqrt T)⁻¹ : ℝ) : ℂ) with hc
  have hzz0 : hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.zu u0))) (rv X.B.I v (X.crd (X.zu u0))) = -(T : ℂ) := by
    rw [hJ_frame, X.zu_norm, map_neg, map_natCast]
    simp [hTdef, Tr]
  have hcc : star c * (c * -(T : ℂ)) = -1 := by
    have h1 : ((Real.sqrt T)⁻¹) ^ 2 * T = 1 := by
      rw [inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have h2 : star c = c := Complex.conj_ofReal _
    rw [h2, hc]
    have h3 : ((((Real.sqrt T)⁻¹) ^ 2 * T : ℝ) : ℂ) = 1 := by rw [h1]; simp
    push_cast at h3 ⊢
    linear_combination (-1 : ℂ) * h3
  obtain ⟨Q, Qi, h1, h2, hg, hcol⟩ := transp_exists (n_eq' X) (X.B.I.ε v) (frS D) (frS_ne D)
    (fun a => rv X.B.I v (X.crd (X.eX a))) (fun a => rv X.B.I v (X.crd (X.fY a))) (X.wfr u0 v)
    (c • rv X.B.I v (X.crd (X.zu u0)))
    (fun a b => by rw [hJ_frame, X.ee, map_zero])
    (fun a b => by rw [hJ_frame, X.ff, map_zero])
    (fun a b => by
      rw [hJ_frame, X.ef]
      split_ifs <;> simp)
    (fun a => by rw [hJ_smul_right', hJ_frame, (X.zu_orth u0 a).1, map_zero, mul_zero])
    (fun a => by rw [hJ_smul_right', hJ_frame, (X.zu_orth u0 a).2, map_zero, mul_zero])
    (by rw [hJ_smul_left', hJ_smul_right', hzz0, hcc])
    (X.wfr_on u0 v)
    (fun c' a => ((X.wfr_perp u0 v a).1 c').1)
    (fun c' a => ((X.wfr_perp u0 v a).1 c').2)
    (fun a => by
      have h0 : hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.zu u0))) (X.wfr u0 v a) = 0 := (X.wfr_perp u0 v a).2
      rw [hJ_smul_left', h0, mul_zero])
  refine ⟨Q, Qi, h1, h2, hg, fun a b hab => ?_⟩
  obtain rfl : a = b := Fin.ext hab
  exact hcol a

theorem zTr_of {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (u : D.what₂.Word) :
    inWb D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) ∧ Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) = Tr D u := by
  obtain ⟨h1, h2, hg, hcol⟩ := hQ
  obtain ⟨hz, hT⟩ := z_tr (n_eq' X) (X.B.I.ε v) h2 hg (rv X.B.I v (X.zR u)) (fun a => by
    obtain ⟨he, hf⟩ := hcol a a rfl
    rw [he, hf, hJ_smul_left', hJ_smul_left', show X.eR a = X.crd (X.eX a) from rfl,
      show X.fR a = X.crd (X.fY a) from rfl, show X.zR u = X.crd (X.zu u) from rfl, hJ_frame, hJ_frame,
      (X.zu_orth u a).1, (X.zu_orth u a).2, map_zero]
    simp)
  refine ⟨hz, ?_⟩
  rw [hT, show X.zR u = X.crd (X.zu u) from rfl, hJ_frame, X.zu_norm, map_neg, map_natCast]
  simp [Tr]

end Exist

end Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

theorem choiceExists {D : D7} (X : HidaSetting D) [Nonempty D.what₂.Word] (θ : ℝ) : ChoiceExists X θ := by
  intro hθ
  classical
  choose Q Qi hQ using transpC_exists X (Classical.arbitrary D.what₂.Word)
  have hy : ∀ τ, ∃ y, y ∈ UH (Hpk D.R.k D.R.rS) ∧ ∃ P, IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧
      sigB X (Q τ) (Qi τ) τ y (X.B.w (vOf X τ)) ∈ lowKSub (epsSH D.R) (lamD D τ)
        (fun g => sigB X (Q τ) (Qi τ) τ (P⁻¹ * g * P)) := by
    intro τ
    obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    obtain ⟨h1, h2, hg, -⟩ := hQ τ
    obtain ⟨y, hyU, hyl⟩ := y_exists (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
      (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
      (X.B.lam (vOf X τ)) (lamD D τ)
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ (vOf X τ)) (X.ds (vOf X τ)).2.2.1 (X.low (vOf X τ)).2 (Q τ) (Qi τ) h2 hg P hP
    exact ⟨y, hyU, P, hP, hyl⟩
  choose y hyU hyl using hy
  have hZ : ∀ u τ, inWb D.R.k D.R.rS (zB X (Qi τ) u τ) ∧ 0 < Tz D.R.k D.R.rS (zB X (Qi τ) u τ) := fun u τ => by
    obtain ⟨hz, hT⟩ := zTr_of X (hQ τ) u
    exact ⟨hz, hT ▸ Tr_pos D u⟩
  have hW : ∀ u τ, ∃ μ : MeasureTheory.Measure (Mt D.R.k D.R.rS),
      Formalism.MainNotions.S.IsHaarOn (UWset D.R.k D.R.rS (zB X (Qi τ) u τ)) μ ∧ μ Set.univ = 1 := fun u τ =>
    Formalism.MainNotions.S.Inh.haar_probability_compact_subgroup _ (Formalism.MainNotions.S.Inh.one_mem_unitary_stabilizer_set _) (Formalism.MainNotions.S.Inh.unitary_stabilizer_mul_mem _)
      (fun a => Hpk D.R.k D.R.rS * aᴴ * Hpk D.R.k D.R.rS)
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
      (fun a ha => Formalism.MainNotions.S.Inh.unitary_stabilizer_inv_mem _ a ha)
      (PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact _ _ _ (hZ u τ).1 (hZ u τ).2)
  choose muW hWh hW1 using hW
  have hN : ∀ u τ, ∃ ν, Formalism.MainNotions.S.IsQuotMeas (muGB X (Q τ) (Qi τ) τ) (Formalism.MainNotions.S.muS (muW u τ) (muNB D θ)) ν := by
    intro u τ
    obtain ⟨h1, h2, hg, -⟩ := hQ τ
    exact Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists _ _ _ (hZ u τ).1 (hZ u τ).2 _ _
      (haar_tr (n_eq' X) _ _ _ h2 hg)
      (isHaarOn_muS (hZ u τ).1 (hZ u τ).2 (hWh u τ) (hW1 u τ) (kapN_ne_zero D hθ) (kapN_ne_top D θ))
  choose nuS hnuS using hN
  exact ⟨Choice.mk Q Qi hQ y hyU hyl muW hWh hW1 nuS hnuS⟩

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Choice

section Tor

open Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants.GBasic

variable {k r : ℕ}

def tE (μ : ℂ) (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then μ ^ (r - i.val) else if r + k < i.val then (star (μ ^ (r - (2 * r + k - i.val))))⁻¹ else 1

theorem torS_eq (μ : ℂ) : torS μ k r = Matrix.diagonal (tE μ k r) := rfl

theorem tE_eI (μ : ℂ) (a : Fin r) : tE μ k r (eI k r a) = μ ^ (r - (a : ℕ)) := by
  simp only [tE]
  rw [if_pos (show (eI k r a).val < r from a.isLt)]
  rfl

theorem tE_esI (μ : ℂ) (a : Fin r) : tE μ k r (esI k r a) = (star (μ ^ (r - (a : ℕ))))⁻¹ := by
  have ha := a.isLt
  have h1 : ¬ (esI k r a).val < r := by show ¬ (2 * r + k - a.val) < r; omega
  have h2 : r + k < (esI k r a).val := by show r + k < 2 * r + k - a.val; omega
  have h3 : 2 * r + k - (esI k r a).val = a.val := by show 2 * r + k - (2 * r + k - a.val) = a.val; omega
  simp only [tE]
  rw [if_neg h1, if_pos h2, h3]

theorem tE_inv_mul (μ : ℂ) (hμ : μ ≠ 0) (i : Fin (2 * r + k + 1)) : tE μ⁻¹ k r i * tE μ k r i = 1 := by
  unfold tE
  split_ifs
  · rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hμ)]
  · rw [inv_pow, star_inv₀, inv_inv, mul_inv_cancel₀ (star_ne_zero.mpr (pow_ne_zero _ hμ))]
  · rw [one_mul]

theorem tE_mul_inv (μ : ℂ) (hμ : μ ≠ 0) (i : Fin (2 * r + k + 1)) : tE μ k r i * tE μ⁻¹ k r i = 1 := by
  rw [mul_comm]
  exact tE_inv_mul μ hμ i

theorem tE_sig (μ : ℂ) (hμ : μ ≠ 0) (i : Fin (2 * r + k + 1)) : star (tE μ k r i) * tE μ k r (sig k r i) = 1 := by
  have hs := Formalism.QuantumDeterminants.GBasic.sig_val k r i
  have hi := i.isLt
  unfold tE
  by_cases h1 : i.val < r
  · have h2 : ¬ (sig k r i).val < r := by rw [hs, if_pos (Or.inl h1)]; omega
    have h3 : r + k < (sig k r i).val := by rw [hs, if_pos (Or.inl h1)]; omega
    have h4 : 2 * r + k - (sig k r i).val = i.val := by rw [hs, if_pos (Or.inl h1)]; omega
    rw [if_pos h1, if_neg h2, if_pos h3, h4]
    exact mul_inv_cancel₀ (star_ne_zero.mpr (pow_ne_zero _ hμ))
  · by_cases h5 : r + k < i.val
    · have h2 : (sig k r i).val < r := by rw [hs, if_pos (Or.inr h5)]; omega
      have h4 : (sig k r i).val = 2 * r + k - i.val := by rw [hs, if_pos (Or.inr h5)]
      rw [if_neg h1, if_pos h5, if_pos h2, h4, star_inv₀, star_star]
      exact inv_mul_cancel₀ (pow_ne_zero _ hμ)
    · have h6 : sig k r i = i := Formalism.QuantumDeterminants.GBasic.sig_mid k r i (by omega) (by omega)
      rw [h6, if_neg h1, if_neg h5]
      simp

theorem torS_inv_mul (μ : ℂ) (hμ : μ ≠ 0) : torS μ⁻¹ k r * torS μ k r = 1 := by
  rw [torS_eq, torS_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact tE_inv_mul μ hμ i

theorem torS_mul_inv (μ : ℂ) (hμ : μ ≠ 0) : torS μ k r * torS μ⁻¹ k r = 1 := by
  rw [torS_eq, torS_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact tE_mul_inv μ hμ i

theorem torS_gram (μ : ℂ) (hμ : μ ≠ 0) : (torS μ k r)ᴴ * Hpk k r * torS μ k r = Hpk k r := by
  ext i j
  rw [torS_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Formalism.QuantumDeterminants.GBasic.Hpk_eq]
  split_ifs with h
  · subst h
    calc (star (tE μ k r)) i * Formalism.QuantumDeterminants.GBasic.sgn k r i * tE μ k r (sig k r i)
        = (star (tE μ k r i) * tE μ k r (sig k r i)) * Formalism.QuantumDeterminants.GBasic.sgn k r i := by
          simp only [Pi.star_apply]; ring
      _ = Formalism.QuantumDeterminants.GBasic.sgn k r i := by rw [tE_sig μ hμ i, one_mul]
  · simp

theorem torS_single (μ : ℂ) (i : Fin (2 * r + k + 1)) :
    torS μ k r *ᵥ Pi.single i 1 = tE μ k r i • (Pi.single i 1 : Fin (2 * r + k + 1) → ℂ) := by
  rw [torS_eq]
  ext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

end Tor

end Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

theorem cfS_ne (D : D7) : cfS D ≠ 0 := by
  unfold Formalism.L2.SG.LocWSOf.cfS
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hg))) hpi

theorem muT_ne (D : D7) : muT D ≠ 0 := by
  unfold Formalism.L2.SG.LocWSOf.muT
  exact div_ne_zero (cfS_ne D) (frS_ne D)

theorem torTie {D : D7} (X : HidaSetting D) : TorTie X := by
  intro v Q Qi hQ
  obtain ⟨h1, h2, hg, hcol⟩ := hQ
  have hμ : muT D ≠ 0 := muT_ne D
  have hμf : muT D * frS D = cfS D := div_mul_cancel₀ _ (frS_ne D)
  refine ⟨?_, ?_, ?_, fun a b hab => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qi, h1, Matrix.one_mul, torS_inv_mul _ hμ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (torS (muT D) D.R.k D.R.rS), torS_mul_inv _ hμ, Matrix.one_mul, h2]
  · rw [Matrix.conjTranspose_mul]
    calc (torS (muT D) D.R.k D.R.rS)ᴴ * Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * torS (muT D) D.R.k D.R.rS)
        = (torS (muT D) D.R.k D.R.rS)ᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * torS (muT D) D.R.k D.R.rS := by
          simp only [Matrix.mul_assoc]
      _ = Hpk D.R.k D.R.rS := by rw [hg, torS_gram _ hμ]
  · obtain ⟨he, hf⟩ := hcol a b hab
    constructor
    · rw [← Matrix.mulVec_mulVec, torS_single, Matrix.mulVec_smul, he, tE_eI, smul_smul, ← mul_pow, hμf]
    · rw [← Matrix.mulVec_mulVec, torS_single, Matrix.mulVec_smul, hf, tE_esI, smul_smul, ← mul_inv, ← star_mul',
        ← mul_pow, hμf]

theorem zTr {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : ZTr C u τ :=
  zTr_of X (C.isT τ) u

theorem haarTr {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) : HaarTr C τ :=
  haar_tr (n_eq' X) _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Choice

section Cols

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

theorem isFrameJ_scaled {ε : Fin (2 * r + k + 1) → Bool} (lam : ℂ) (hlam : lam ≠ 0)
    {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hez : ∀ a, hJ ε (e a) z0 = 0)
    (hfz : ∀ a, hJ ε (f a) z0 = 0) (hzz : hJ ε z0 z0 = -1)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (hew : ∀ c a, hJ ε (e c) (wf a) = 0)
    (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z0 (wf a) = 0) :
    IsFrameJ ε (fun a => lam ^ (r - (a : ℕ)) • e a) (fun a => (star (lam ^ (r - (a : ℕ))))⁻¹ • f a) wf z0 := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, hzz, hww,
    fun c a => ?_, fun c a => ?_, hzw⟩
  · simp only [hJ_smul_left', hJ_smul_right', hee, mul_zero]
  · simp only [hJ_smul_left', hJ_smul_right', hff, mul_zero]
  · simp only [hJ_smul_left', hJ_smul_right', hef]
    split_ifs with h
    · subst h
      have hs : star (lam ^ (r - (a : ℕ))) ≠ 0 := star_ne_zero.mpr (pow_ne_zero _ hlam)
      first
        | (rw [mul_one]; exact mul_inv_cancel₀ hs)
        | (rw [mul_one]; exact inv_mul_cancel₀ hs)
        | field_simp
    · rw [mul_zero, mul_zero]
  · simp only [hJ_smul_left', hez, mul_zero]
  · simp only [hJ_smul_left', hfz, mul_zero]
  · simp only [hJ_smul_left', hew, mul_zero]
  · simp only [hJ_smul_left', hfw, mul_zero]

theorem hcTypeW_tr {ε : Fin (2 * r + k + 1) → Bool} {Q Qi : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r)
    {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {T : ℝ} (hT : 0 < T)
    {z : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf (z0v T z))
    (hcolE : ∀ a, Q *ᵥ bvec (eI k r a) = e a) (hcolF : ∀ a, Q *ᵥ bvec (esI k r a) = f a)
    (hTz : Tz k r (Qi *ᵥ z) = T) {u : Fin k → ℝ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hπ : Formalism.MainNotions.S.IsHCTypeU k u πl) :
    Formalism.MainNotions.S.IsHCTypeW k r (Qi *ᵥ z) u (fun m => πl (Formalism.L2.SG.RealObj.matQ ε wf (Q * m * Qi))) := by
  set F := Qm e f wf (z0v T z) with hFdef
  set G := Formalism.L2.SG.Pf.WFL.Qi ε e f wf (z0v T z) with hGdef
  have hFG : F * G = 1 := Qm_mul_Qi hF
  have hgi : Qi * F * (G * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc F G Q, hFG, Matrix.one_mul, h1]
  have hginv : (Qi * F)⁻¹ = G * Q := Matrix.inv_eq_right_inv hgi
  refine ⟨Qi * F, ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · show (Qi * F)ᴴ * Hpk k r * (Qi * F) = Hpk k r
    calc (Qi * F)ᴴ * Hpk k r * (Qi * F) = Fᴴ * (Qiᴴ * Hpk k r * Qi) * F := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [qiHqi ε h2 hg, gramQ hF]
  · rw [← Matrix.mulVec_mulVec, Qm_mulVec_bvec, colQ_eI, ← hcolE, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rw [← Matrix.mulVec_mulVec, Qm_mulVec_bvec, colQ_esI, ← hcolF, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rw [hTz, show (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = zBv k r T from rfl,
      ← Matrix.mulVec_mulVec, Qm_zB hT z]
  · have hfun : (fun h => πl (Formalism.L2.SG.RealObj.matQ ε wf (Q * (Qi * F * Formalism.MainNotions.S.blockW k r h * (Qi * F)⁻¹) * Qi))) =
        fun h => piB ε e f wf (z0v T z) πl (Formalism.MainNotions.S.blockW k r h) := by
      funext h
      have hM : Q * (Qi * F * Formalism.MainNotions.S.blockW k r h * (Qi * F)⁻¹) * Qi = F * Formalism.MainNotions.S.blockW k r h * G := by
        rw [hginv]
        calc Q * (Qi * F * Formalism.MainNotions.S.blockW k r h * (G * Q)) * Qi
            = (Q * Qi) * F * Formalism.MainNotions.S.blockW k r h * G * (Q * Qi) := by simp only [Matrix.mul_assoc]
          _ = F * Formalism.MainNotions.S.blockW k r h * G := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [hM]
      rfl
    rw [hfun]
    simp_rw [piB_blockW hF]
    exact hπ

end Cols

section Cols2

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

theorem colsType_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) (lam : ℂ) (hlam : lam ≠ 0)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hez : ∀ a, hJ ε (e a) (z0v T z) = 0)
    (hfz : ∀ a, hJ ε (f a) (z0v T z) = 0) (hzz : hJ ε (z0v T z) (z0v T z) = -1)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (hew : ∀ c a, hJ ε (e c) (wf a) = 0)
    (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε (z0v T z) (wf a) = 0)
    (hcolE : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (hcolF : ∀ a : Fin r, Q *ᵥ Pi.single (esI k r a) 1 = (star (lam ^ (r - (a : ℕ))))⁻¹ • f a)
    (hTz : Tz k r (Qi *ᵥ z) = T) {u : Fin k → ℝ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} (hπ : Formalism.MainNotions.S.IsHCTypeU k u πl) :
    Formalism.MainNotions.S.IsHCTypeW k r (Qi *ᵥ z) u (fun m => πl (Formalism.L2.SG.RealObj.matQ ε wf (Q * m * Qi))) := by
  subst hn
  exact hcTypeW_tr h1 h2 hg hT (isFrameJ_scaled lam hlam hee hff hef hez hfz hzz hww hew hfw hzw) hcolE hcolF hTz hπ

end Cols2

section Cols3

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

variable {D : D7} (X : HidaSetting D)

theorem colsTypeTr_of {v : InfinitePlace X.B.I.F} {lam : ℂ} (hlam : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (u : D.what₂.Word) :
    IsHCTypeW D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (fun i => ((D.hcW u (X.pl v)).u i : ℝ))
      (fun m => X.piLoc u v (Formalism.L2.SG.RealObj.matQ (X.B.I.ε v) (X.wfr u v) (Q * m * Qi))) := by
  set T := Tr D u with hTdef
  have hT := Tr_pos D u
  set c : ℂ := (((Real.sqrt T)⁻¹ : ℝ) : ℂ) with hc
  have hzz0 : hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.zu u))) (rv X.B.I v (X.crd (X.zu u))) = -(T : ℂ) := by
    rw [hJ_frame, X.zu_norm, map_neg, map_natCast]
    simp [hTdef, Tr]
  have hcc : star c * (c * -(T : ℂ)) = -1 := by
    have h1 : ((Real.sqrt T)⁻¹) ^ 2 * T = 1 := by
      rw [inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have h2 : star c = c := Complex.conj_ofReal _
    rw [h2, hc]
    have h3 : ((((Real.sqrt T)⁻¹) ^ 2 * T : ℝ) : ℂ) = 1 := by rw [h1]; simp
    push_cast at h3 ⊢
    linear_combination (-1 : ℂ) * h3
  obtain ⟨h1, h2, hg, hcol⟩ := hQ
  exact colsType_loc (n_eq' X) (X.B.I.ε v) Q Qi h1 h2 hg lam hlam
    (fun a => rv X.B.I v (X.crd (X.eX a))) (fun a => rv X.B.I v (X.crd (X.fY a))) (X.wfr u v)
    (rv X.B.I v (X.crd (X.zu u))) hT
    (fun a b => by rw [hJ_frame, X.ee, map_zero])
    (fun a b => by rw [hJ_frame, X.ff, map_zero])
    (fun a b => by
      rw [hJ_frame, X.ef]
      split_ifs <;> simp)
    (fun a => by rw [Formalism.L2.SG.Pf.WFL.z0v, hJ_smul_right', hJ_frame, (X.zu_orth u a).1, map_zero, mul_zero])
    (fun a => by rw [Formalism.L2.SG.Pf.WFL.z0v, hJ_smul_right', hJ_frame, (X.zu_orth u a).2, map_zero, mul_zero])
    (by rw [Formalism.L2.SG.Pf.WFL.z0v, hJ_smul_left', hJ_smul_right', hzz0, ← hc, hcc])
    (X.wfr_on u v)
    (fun c' a => ((X.wfr_perp u v a).1 c').1)
    (fun c' a => ((X.wfr_perp u v a).1 c').2)
    (fun a => by
      have h0 : hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.zu u))) (X.wfr u v a) = 0 := (X.wfr_perp u v a).2
      rw [Formalism.L2.SG.Pf.WFL.z0v, hJ_smul_left', h0, mul_zero])
    (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2)
    (zTr_of X ⟨h1, h2, hg, hcol⟩ u).2 (X.piLoc_type u v)

end Cols3

end Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

theorem colsTypeTr {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ColsTypeTr C u τ := by
  have h := colsTypeTr_of X (frS_ne D) (C.isT τ) u
  rw [show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h
  exact h

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Choice

section Psi

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

theorem hJ_QQ {n N : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin N) ℂ) (H : Matrix (Fin N) (Fin N) ℂ)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = H) (y x : Fin N → ℂ) : hJ ε (Q *ᵥ y) (Q *ᵥ x) = star y ⬝ᵥ (H *ᵥ x) := by
  subst hg
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem star_single_dot {N : ℕ} (i : Fin N) (w : Fin N → ℂ) : star (Pi.single i (1 : ℂ)) ⬝ᵥ w = w i := by
  have h : star (Pi.single i (1 : ℂ)) = (Pi.single i 1 : Fin N → ℂ) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [h]
  simp

variable {D : D7} (X : HidaSetting D)

theorem rootCoord_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} (hlam : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (u : D.what₂.Word) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (a : Fin D.R.rS) :
    rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
        (Q * m * Qi) a =
      lam * (if h : a.val + 1 < D.R.rS then m (eI D.R.k D.R.rS a) (eI D.R.k D.R.rS ⟨a.val + 1, h⟩)
        else (m *ᵥ (Qi *ᵥ rv X.B.I v (X.zR u))) (eI D.R.k D.R.rS a)) := by
  obtain ⟨h1, h2, hg, hcol⟩ := hQ
  have hp : ∀ b : Fin D.R.rS, lam ^ (D.R.rS - (b : ℕ)) ≠ 0 := fun b => pow_ne_zero _ hlam
  have hsp : ∀ b : Fin D.R.rS, star (lam ^ (D.R.rS - (b : ℕ))) ≠ 0 := fun b => by
    rw [Ne, star_eq_zero]; exact hp b
  have hf : rv X.B.I v (X.fR a) = star (lam ^ (D.R.rS - (a : ℕ))) •
      (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
    rw [(hcol a a rfl).2, smul_smul, mul_inv_cancel₀ (hsp a), one_smul]
  have hHe : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      star (Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) (1 : ℂ)) ⬝ᵥ (Hpk D.R.k D.R.rS *ᵥ x) = x (eI D.R.k D.R.rS a) := by
    intro x
    rw [star_single_dot, Formalism.L2.SG.Pf.WFL.Hpk_mulVec, Formalism.L2.SG.Pf.WFL.sgn_esI, Formalism.L2.SG.Pf.WFL.sig_esI_eq, one_mul]
  unfold rootCoord nxt
  dsimp only
  rw [hf, hJ_smul_left', star_star]
  by_cases h : a.val + 1 < D.R.rS
  · rw [dif_pos h, dif_pos h]
    set b : Fin D.R.rS := ⟨a.val + 1, h⟩
    have he : rv X.B.I v (X.eR b) = (lam ^ (D.R.rS - (b : ℕ)))⁻¹ • (Q *ᵥ Pi.single (eI D.R.k D.R.rS b) 1) := by
      rw [(hcol b b rfl).1, smul_smul, inv_mul_cancel₀ (hp b), one_smul]
    have hQiQ : ∀ y, Qi *ᵥ (Q *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [he, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQiQ, hJ_smul_right', hJ_QQ _ Q _ hg,
      hHe]
    have hm : (m *ᵥ Pi.single (eI D.R.k D.R.rS b) 1) (eI D.R.k D.R.rS a) = m (eI D.R.k D.R.rS a) (eI D.R.k D.R.rS b) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hm]
    have hexp : D.R.rS - (a : ℕ) = (D.R.rS - (b : ℕ)) + 1 := by simp only [b]; omega
    rw [hexp, pow_succ]
    field_simp [hp b]
  · rw [dif_neg h, dif_neg h]
    have hz : rv X.B.I v (X.zR u) = Q *ᵥ (Qi *ᵥ rv X.B.I v (X.zR u)) := by
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have hQiQ : ∀ y, Qi *ᵥ (Q *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    conv_lhs => rw [hz]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQiQ, hJ_QQ _ Q _ hg, hHe]
    have hexp : D.R.rS - (a : ℕ) = 1 := by have := a.isLt; omega
    rw [hexp, pow_one]

theorem rootSum_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} (hlam : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (u : D.what₂.Word) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    ∑ a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
        (Q * m * Qi) a = lam * Formalism.QuantumDeterminants.ell D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) m := by
  rw [Formalism.QuantumDeterminants.ell, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => rootCoord_tr X hlam hQ u m a

end Psi

end Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

theorem psiTr {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : PsiTr C u τ := by
  intro m _
  unfold psiR psiS Formalism.QuantumDeterminants.psi
  set L := Formalism.QuantumDeterminants.ell D.R.k D.R.rS (zB X (C.Qi τ) u τ) m with hL
  have hsum : (frS D * L + star (frS D * L)) = ((2 * (D.host.ka / (2 * Real.pi)) * L.re : ℝ) : ℂ) := by
    unfold frS
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← mul_add, Complex.add_conj]
    push_cast
    ring
  have hsplit : ∑ a, (rootCoord (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a))
      (fun a => rv X.B.I (vOf X τ) (X.fR a)) (rv X.B.I (vOf X τ) (X.zR u)) (C.Q τ * m * C.Qi τ) a +
      star (rootCoord (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a))
      (fun a => rv X.B.I (vOf X τ) (X.fR a)) (rv X.B.I (vOf X τ) (X.zR u)) (C.Q τ * m * C.Qi τ) a)) =
      frS D * L + star (frS D * L) := by
    rw [Finset.sum_add_distrib, ← star_sum, rootSum_tr X (frS_ne D) (C.isT τ) u m]
    rfl
  rw [hsplit, hsum, X.g_eq]
  congr 1
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).pos.ne'
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).pos.ne'
  have hre : (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) * L).re =
      2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * L.re := Complex.re_ofReal_mul _ _
  rw [hre]
  push_cast
  field_simp

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Choice

section DSConj

open Formalism.MainNotions.S
open scoped InnerProductSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def isoOf {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : IsURepOn (UJset ε) σ)
    {h : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) : H →ₗᵢ[ℂ] H :=
  ⟨(σ h : H →ₗ[ℂ] H), fun v => hrep.2.1 h hh v⟩

theorem inner_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : IsURepOn (UJset ε) σ)
    {h h' : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) (hh' : Formalism.REAL.inUJ ε h') (hhh' : h * h' = 1)
    (w x : H) : ⟪w, σ h x⟫_ℂ = ⟪σ h' w, x⟫_ℂ := by
  have hmul : σ (h * h') = (σ h).comp (σ h') := hrep.1.2 h hh h' hh'
  have h1 : σ 1 = 1 := hrep.1.1
  have key : σ h (σ h' w) = w := by
    have := congrArg (fun T : H →L[ℂ] H => T w) hmul
    simp only [hhh', h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  calc ⟪w, σ h x⟫_ℂ = ⟪σ h (σ h' w), σ h x⟫_ℂ := by rw [key]
    _ = ⟪σ h' w, x⟫_ℂ := (isoOf hrep hh).inner_map_map (σ h' w) x

theorem isDS_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hds : IsDS ε lam σ) {h h' : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) (hh' : Formalism.REAL.inUJ ε h')
    (hhh' : h * h' = 1) (hh'h : h' * h = 1) : IsDS ε lam (fun g => σ (h * g * h')) := by
  obtain ⟨hc, hnt, hrep, hirr, hsq, ⟨S0, hS0⟩, hmin⟩ := hds
  have hcon : ∀ {g}, Formalism.REAL.inUJ ε g → Formalism.REAL.inUJ ε (h * g * h') := fun hg => inUJ_mul (inUJ_mul hh hg) hh'
  have hsplit : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, σ (h * g * h') x = σ h (σ g (σ h' x)) := fun g hg x => by
    rw [hrep.1.2 _ (inUJ_mul hh hg) _ hh', hrep.1.2 _ hh _ hg]; rfl
  have hVU : ∀ x, σ h' (σ h x) = x := fun x => by
    rw [← ContinuousLinearMap.comp_apply, ← hrep.1.2 _ hh' _ hh, hh'h, hrep.1.1]; rfl
  have hUV : ∀ x, σ h (σ h' x) = x := fun x => by
    rw [← ContinuousLinearMap.comp_apply, ← hrep.1.2 _ hh _ hh', hhh', hrep.1.1]; rfl
  have hback : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, σ g x = σ h' (σ (h * g * h') (σ h x)) := fun g hg x => by
    rw [hsplit g hg, hVU, hVU]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · show σ (h * 1 * h') = 1
    rw [Matrix.mul_one, hhh', hrep.1.1]
  · intro a ha b hb
    show σ (h * (a * b) * h') = (σ (h * a * h')).comp (σ (h * b * h'))
    rw [← hrep.1.2 _ (hcon ha) _ (hcon hb)]
    congr 1
    calc h * (a * b) * h' = h * a * (h' * h) * b * h' := by rw [hh'h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = h * a * h' * (h * b * h') := by simp only [Matrix.mul_assoc]
  · intro g hg v
    exact hrep.2.1 _ (hcon hg) v
  · intro v
    have hmaps : Set.MapsTo (fun g : Matrix (Fin n) (Fin n) ℂ => h * g * h') (UJset ε) (UJset ε) :=
      fun g hg => hcon hg
    exact (hrep.2.2 v).comp ((continuous_const.mul continuous_id).mul continuous_const).continuousOn hmaps
  · intro S hS hst
    refine hirr S hS fun g hg v hv => ?_
    have hg' : Formalism.REAL.inUJ ε (h' * g * h) := inUJ_mul (inUJ_mul hh' hg) hh
    have : σ g v = σ (h * (h' * g * h) * h') v := by
      congr 2
      calc g = (h * h') * g * (h * h') := by rw [hhh', Matrix.one_mul, Matrix.mul_one]
        _ = h * (h' * g * h) * h' := by simp only [Matrix.mul_assoc]
    rw [this]
    exact hst _ hg' v hv
  · intro v w
    have heq : coefOn (ε := ε) (fun g => σ (h * g * h')) v w = coefOn (ε := ε) σ (σ h' v) (σ h' w) := by
      funext γ
      show ⟪w, σ (h * umat γ * h') v⟫_ℂ = ⟪σ h' w, σ (umat γ) (σ h' v)⟫_ℂ
      rw [hsplit _ γ.2, inner_conj ⟨hrep.1, hrep.2.1, hrep.2.2⟩ hh hh' hhh']
    rw [heq]
    exact hsq _ _
  · exact ⟨_, ktype_map (σ h) (σ h') hVU hUV (fun g hg x => hsplit g (kset_sub hg) x) hS0⟩
  · intro μ S hS
    exact hmin μ _ (ktype_map (σ h') (σ h) hUV hVU (fun g hg x => hback g (kset_sub hg) x) hS)

theorem isFdeg_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : IsURepOn (UJset ε) σ)
    {h h' : Matrix (Fin n) (Fin n) ℂ} (hh : Formalism.REAL.inUJ ε h) (hh' : Formalism.REAL.inUJ ε h')
    (hhh' : h * h' = 1) {μ : MeasureTheory.Measure (Formalism.REAL.UJ ε)} {d : ℝ} (hd : IsFdeg μ σ d) :
    IsFdeg μ (fun g => σ (h * g * h')) d := by
  obtain ⟨hd0, hdi⟩ := hd
  have hsplit : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, σ (h * g * h') x = σ h (σ g (σ h' x)) := fun g hg x => by
    rw [hrep.1.2 _ (inUJ_mul hh hg) _ hh', hrep.1.2 _ hh _ hg]; rfl
  have heq : ∀ v w, coefOn (ε := ε) (fun g => σ (h * g * h')) v w = coefOn (ε := ε) σ (σ h' v) (σ h' w) := by
    intro v w
    funext γ
    show ⟪w, σ (h * umat γ * h') v⟫_ℂ = ⟪σ h' w, σ (umat γ) (σ h' v)⟫_ℂ
    rw [hsplit _ γ.2, inner_conj hrep hh hh' hhh']
  refine ⟨hd0, fun v w v' w' => ?_⟩
  rw [heq, heq]
  obtain ⟨hi, hint⟩ := hdi (σ h' v) (σ h' w) (σ h' v') (σ h' w')
  refine ⟨hi, ?_⟩
  rw [hint]
  have h1 := (isoOf hrep hh').inner_map_map v' v
  have h2 := (isoOf hrep hh').inner_map_map w w'
  simp only [isoOf, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe] at h1 h2
  rw [h1, h2]

end DSConj

section DSTr

open Formalism.MainNotions.S

variable {k r : ℕ}

theorem cay_facts {ε : Fin (2 * r + k + 1) → Bool} {Q Qi P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) (hP : IsCayleyU k r ε P) :
    Formalism.REAL.inUJ ε (Q * P⁻¹) ∧ Formalism.REAL.inUJ ε (P * Qi) ∧ Q * P⁻¹ * (P * Qi) = 1 ∧ P * Qi * (Q * P⁻¹) = 1 := by
  obtain ⟨⟨hPu, hPg⟩, -⟩ := hP
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQd : IsUnit Q.det := Matrix.isUnit_det_of_right_inverse h2
  have h1 : Qi * Q = 1 := by
    rw [← Matrix.inv_eq_right_inv h2]
    exact Matrix.nonsing_inv_mul Q hQd
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Formalism.REAL.inUJ
    calc (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [hg, ← hPg]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPi]; simp
  · unfold Formalism.REAL.inUJ
    calc (P * Qi)ᴴ * Formalism.REAL.Jm ε * (P * Qi) = Qiᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPg]; exact qiHqi ε h2 hg
  · calc Q * P⁻¹ * (P * Qi) = Q * (P⁻¹ * P) * Qi := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hiP, Matrix.mul_one, h2]
  · calc P * Qi * (Q * P⁻¹) = P * (Qi * Q) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hPi]

theorem dsHpk_tr {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (ε' : Fin (2 * r + k + 1) → Bool)
    (hε : ∀ i, ε' i = ε (Fin.cast hn.symm i)) (lam : Fin n → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ)
    (hlam : ∀ i, lam' i = lam (Fin.cast hn.symm i)) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hds : IsDS ε lam σ)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε' P) :
    IsDS ε' lam' (fun g => σ (Q * (P⁻¹ * g * P) * Qi)) := by
  subst hn
  have hεe : ε' = ε := funext fun i => by rw [hε]; rfl
  have hle : lam' = lam := funext fun i => by rw [hlam]; rfl
  subst hεe
  subst hle
  obtain ⟨c1, c2, c3, c4⟩ := cay_facts h2 hg hP
  have := isDS_conj hds c1 c2 c3 c4
  simpa only [Matrix.mul_assoc] using this

theorem fdegHpk_tr {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (ε' : Fin (2 * r + k + 1) → Bool)
    (hε : ∀ i, ε' i = ε (Fin.cast hn.symm i)) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hrep : IsURepOn (UJset ε) σ) {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε' P) :
    IsFdeg (Formalism.REAL.muG ε') (fun g => σ (Q * (P⁻¹ * g * P) * Qi)) d := by
  subst hn
  have hεe : ε' = ε := funext fun i => by rw [hε]; rfl
  subst hεe
  obtain ⟨c1, c2, c3, -⟩ := cay_facts h2 hg hP
  have := isFdeg_conj hrep c1 c2 c3 hd
  simpa only [Matrix.mul_assoc] using this

end DSTr

end Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

theorem dsTr {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) := by
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  refine ⟨P, hP, ?_⟩
  exact dsHpk_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
    (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
    (X.B.lam (vOf X τ)) (lamD D τ)
    (fun i => by
      rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
      exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
    (X.B.σ (vOf X τ)) (X.ds (vOf X τ)) (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Choice

end Formalism.L2.SG.Pf.Choice
