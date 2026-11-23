import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LtCharCont

open GlobalTheory.ExpImage Filter Topology Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (w : Om l) :
    oB P w ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om w
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem norm_th_le_of_mem_Lat {P : LocPrime l} {AI : LocAinf l P} (Θ : ThetaL P AI) {n : ℕ}
    {y : P.R.BdR} (hy : y ∈ Lat AI 1 n) : ‖Θ.θ y‖ ≤ ‖(l : ℚ_[l])‖ ^ n := by
  obtain ⟨a, ha⟩ := hy
  have hy0 : y ∈ FilB P 0 := Lat_mem_zero AI ⟨a, ha⟩
  have hi0 : io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := io_mem AI _
  have hd0 : y - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := sub_mem hy0 hi0
  have h1 : Θ.θ (y - io AI (((l : ℕ) : Ainf l) ^ n * a)) = 0 :=
    (Θ.θ_ker _ hd0).2 (by simpa using ha)
  have h2 : Θ.θ y = Θ.θ (io AI (((l : ℕ) : Ainf l) ^ n * a)) := by
    have := Θ.θ_add _ hd0 _ hi0
    rw [sub_add_cancel, h1, zero_add] at this
    exact this
  have e : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    rw [map_mul, map_pow, map_natCast, map_pow, map_natCast]
  rw [h2, e, Θ.θ_mul _ (qB_mem _) _ (io_mem AI a), norm_mul]
  have e2 : qB P ((l : ℚ_[l]) ^ n) = oB P (algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)) :=
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR _
  rw [e2, Θ.θ_Om, PadicComplex.norm_extends]
  have e3 : ‖algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
    rw [← norm_pow]; exact PadicAlgCl.norm_extends (p := l) _
  rw [e3]
  have := Θ.θ_int a
  rw [← io_apply AI a] at this
  calc _ ≤ ‖(l : ℚ_[l])‖ ^ n * 1 := by gcongr
    _ = _ := mul_one _

theorem continuous_char_of_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → P.ιB x ∈ (P.PD K).Fil 1 →
    P.ιB x ∉ (P.PD K).Fil 2 → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ,
    (∀ g : ↥(GK K), P.actQ (g : GQ l) x =
      algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) →
    Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) := by
  intro l _ P AI T K x _hxu hx1 hx2 c hc
  let Θ := GlobalTheory.ThetaTie.thetaL T
  have hF : ∀ (a : ℤ) (y : P.R.BdR), y ∈ (P.PD K).Fil a ↔ y ∈ FilB P a := fun a y =>
    Set.ext_iff.1 (P.PD_Fil K (botExt l) a) y
  have hX1 : P.ιB x ∈ FilB P 1 := (hF 1 _).1 hx1
  have hX2 : P.ιB x ∉ FilB P 2 := fun h => hx2 ((hF 2 _).2 h)
  obtain ⟨s, hs, hts⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  have hb0 : s * P.ιB x ∈ FilB P 0 := by
    have := FilB_mul hs hX1
    simpa using this
  have hθb : Θ.θ (s * P.ιB x) ≠ 0 := by
    intro h0
    have h1 : s * P.ιB x ∈ FilB P 1 := (Θ.θ_ker _ hb0).1 h0
    apply hX2
    have := FilB_mul (tD_mem (P := P)) h1
    have e : tD P * (s * P.ιB x) = P.ιB x := by
      rw [← mul_assoc]
      change P.ιB P.tB * s * P.ιB x = P.ιB x
      rw [hts, one_mul]
    rw [e] at this
    simpa using this
  let cv : ↥(GK K) → Om l := fun g => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)
  let χv : ↥(GK K) → Om l := fun g => algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])
  let uv : ↥(GK K) → Om l := fun g => cv g * (χv g)⁻¹
  have hK0 : ∀ z : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B z) = oB P (z : Om l) := fun z =>
    GlobalTheory.LocIota.ιB_algebraMap_Kur P (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) z)
  have hqo : ∀ z : ℚ_[l], qB P z = oB P (algebraMap ℚ_[l] (Om l) z) := fun z =>
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z
  have hact : ∀ g : ↥(GK K), P.actQdR (g : GQ l) (s * P.ιB x) = oB P (uv g) * (s * P.ιB x) := by
    intro g
    have hX : P.actQdR (g : GQ l) (P.ιB x) = oB P (cv g) * P.ιB x := by
      rw [← ιB_act, hc g, map_mul, hK0]
    have ht := act_tD (P := P) (g : GQ l)
    have h1 : P.actQdR (g : GQ l) (tD P) * P.actQdR (g : GQ l) s = 1 := by
      rw [← map_mul]
      change P.actQdR (g : GQ l) (P.ιB P.tB * s) = 1
      rw [hts, map_one]
    have h2 : qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * qB P (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one]
    have hts' : tD P * s = 1 := hts
    rw [ht] at h1
    have hs' : P.actQdR (g : GQ l) s = qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s := by
      linear_combination (qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s) * h1
        - P.actQdR (g : GQ l) s * h2
        - (P.actQdR (g : GQ l) s * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹
            * qB P (P.χQ (g : GQ l) : ℚ_[l])) * hts'
    have hu : oB P (uv g) = oB P (cv g) * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ := by
      rw [hqo, map_inv₀]
      change oB P (cv g * (χv g)⁻¹) = _
      rw [map_mul]
    rw [map_mul, hs', hX, hu]
    ring
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hθpos : 0 < ‖Θ.θ (s * P.ιB x)‖ := norm_pos_iff.2 hθb
  have htv : Tendsto (fun g : ↥(GK K) => (g : GQ l)) (𝓝 1) (𝓝 1) := by
    simpa using continuous_subtype_val.tendsto (1 : ↥(GK K))
  have huv : Tendsto uv (𝓝 1) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hθpos) hl
    have hev := (bounded_and_eventually_sub_mem_Lat l P AI T _ hb0 1 n).2
    filter_upwards [htv.eventually hev] with g hg
    rw [hact g] at hg
    have e : oB P (uv g) * (s * P.ιB x) - s * P.ιB x = oB P (uv g - 1) * (s * P.ιB x) := by
      rw [map_sub, map_one]; ring
    rw [e] at hg
    have h3 := norm_th_le_of_mem_Lat Θ hg
    rw [Θ.θ_mul _ (oB_mem T _) _ hb0, Θ.θ_Om, norm_mul, PadicComplex.norm_extends] at h3
    rw [dist_eq_norm]
    have h4 : ‖uv g - 1‖ * ‖Θ.θ (s * P.ιB x)‖ < ε * ‖Θ.θ (s * P.ιB x)‖ := h3.trans_lt hn
    exact lt_of_mul_lt_mul_right h4 hθpos.le
  have hqc : Continuous (algebraMap ℚ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (Om l))
      (fun z => PadicAlgCl.norm_extends (p := l) z)).continuous
  have hχ : Tendsto χv (𝓝 1) (𝓝 1) := by
    have hcont : Continuous χv :=
      hqc.comp ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
    simpa [χv] using hcont.tendsto 1
  have hcv1 : Tendsto cv (𝓝 1) (𝓝 1) := by
    have := huv.mul hχ
    rw [mul_one] at this
    refine this.congr fun g => ?_
    have hne : χv g ≠ 0 := by
      simp only [χv, ne_eq, map_eq_zero]
      exact Units.ne_zero _
    exact inv_mul_cancel_right₀ hne (cv g)
  have hmul : ∀ g h : ↥(GK K), cv (g * h) = cv g * cv h := by
    intro g h
    simp [cv, map_mul]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have t1 : Tendsto (fun g : ↥(GK K) => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_mul_left g₀⁻¹).tendsto g₀
  have t2 := (hcv1.comp t1).const_mul (cv g₀)
  rw [mul_one] at t2
  refine t2.congr fun g => ?_
  change cv g₀ * cv (g₀⁻¹ * g) = cv g
  rw [← hmul, mul_inv_cancel_left]

end GlobalTheory.LtCharCont
