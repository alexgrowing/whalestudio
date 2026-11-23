import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDescendPeriodicTrig
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffMulCharConvAndHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanPeriodicIndepOfCovolumeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPosOfPeriodicNonneg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped TensorProduct ContDiff Topology NNReal ENNReal

namespace GlobalTheory.ThetaAllChar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilVacMove GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem chi_ker (hψ : IsCharAF D.host.F ψ) (x : WO S T) :
    (∀ γ : ratL T S, chi ψ S T γ x = 1) ↔ x ∈ ratL T S := by
  constructor
  · intro h
    obtain ⟨ψ₀, hstd, a, ha, hψa⟩ := exists_std hψ
    have hlaws := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
    set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) a with hc
    have hmap : (c • x : WO S T) = x.map fun z => algebraMap (AF D.host.F) (AE D) c * z := by
      ext i j
      simp [Matrix.smul_apply, Algebra.smul_def]

    have key : ∀ y : WO S T, symplO S T (c • x) y = c * symplO S T x y := by
      intro y
      rw [hmap]
      unfold symplO
      rw [GlobalTheory.OrientedFormLaws.hO_mul_left, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hx' : (c • x : WO S T) ∈ ratL T S := by
      refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ₀ hstd S T _).1 ?_
      intro γ hγ
      rw [key, hc, ← hψa, ← hlaws.2.2.2.1]
      exact h ⟨γ, hγ⟩
    have hback := smul_mem_ratL a⁻¹ hx'
    rw [hc, smul_smul, ← map_mul, inv_mul_cancel₀ ha, map_one, one_smul] at hback
    exact hback
  · intro hx γ
    exact chi_rat hψ γ.2 hx

theorem norm_chi (hn : ∀ x, ‖ψ x‖ = 1) (γ x : WO S T) : ‖chi ψ S T γ x‖ = 1 := by
  unfold chi
  exact hn _

def chiR (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (γ : ratL T S) : WO S T → ℂ := chi ψ S T γ.1

theorem chiR_laws (hψ : IsCharAF D.host.F ψ) : (∀ a, Continuous (chiR ψ S T a)) ∧
    (∀ a x y, chiR ψ S T a (x + y) = chiR ψ S T a x * chiR ψ S T a y) ∧
    (∀ a b x, chiR ψ S T (a + b) x = chiR ψ S T a x * chiR ψ S T b x) ∧ (∀ x, chiR ψ S T 0 x = 1) ∧
    (∀ a x, ‖chiR ψ S T a x‖ = 1) ∧ ∀ x, (∀ a, chiR ψ S T a x = 1) ↔ x ∈ ratL T S := by
  refine ⟨fun a => continuous_chi hψ.1 _, fun a x y => chi_add _ _ _, fun a b x => ?_, fun x => ?_,
    fun a x => norm_chi hψ.2.1 _ _, fun x => chi_ker hψ x⟩
  · show chi ψ S T ((a + b : ratL T S) : WO S T) x = chi ψ S T a x * chi ψ S T b x
    rw [AddSubgroup.coe_add]
    exact chi_add_left _ _ _
  · show chi ψ S T ((0 : ratL T S) : WO S T) x = 1
    rw [ZeroMemClass.coe_zero]
    exact chi_zero_left x

theorem isTheta_sum {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ) (h : ∀ i ∈ s, IsThetaFunO ψ S T (F i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isTheta_zero : IsThetaFunO ψ S T 0)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isTheta_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def trig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (s : Finset (ratL T S)) (c : ratL T S → ℂ) : WO S T → ℂ :=
  ∑ γ ∈ s, c γ • chi ψ S T γ

theorem lintegral_sq_le {G : Type} [MeasurableSpace G] (ν : Measure G) {u : G → ℂ} {ε B : ℝ}
    (h : ∀ w, ‖u w‖ ≤ ε * B) : ∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (B ^ 2) * ν Set.univ) := by
  have hpt : ∀ w, ‖u w‖ₑ ^ 2 ≤ ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (B ^ 2) := by
    intro w
    have h0 : 0 ≤ ‖u w‖ := norm_nonneg _
    rw [← ENNReal.ofReal_mul (sq_nonneg ε), ← mul_pow, ← ofReal_norm, ← ENNReal.ofReal_pow h0]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 (h w) 2)
  calc ∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν ≤ ∫⁻ _w, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (B ^ 2) ∂ν := lintegral_mono hpt
    _ = _ := by rw [lintegral_const, mul_assoc]

theorem ae_zero_of_small {G : Type} [MeasurableSpace G] (ν : Measure G) {h : G → ℂ} (hm : Measurable h) {M N : ℝ≥0∞}
    (hM : M ≠ ⊤) (hN : N ≠ ⊤) (hs : ∀ ε : ℝ, 0 < ε → ∃ u v : G → ℂ, Measurable u ∧ h = u - v ∧
      ∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (ε ^ 2) * M ∧ ∫⁻ w, ‖v w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (ε ^ 2) * N) :
    ∀ᵐ w ∂ν, h w = 0 := by

  have hpt : ∀ a b : ℂ, ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
    intro a b
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    have hab : ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
      have t := norm_sub_le a b
      have t0 := norm_nonneg (a - b)
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hab
  set I := ∫⁻ w, ‖h w‖ₑ ^ 2 ∂ν with hI
  have hK : 2 * (M + N) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hM, hN⟩)
  have hle : ∀ ε : ℝ, 0 < ε → I ≤ ENNReal.ofReal (ε ^ 2) * (2 * (M + N)) := by
    intro ε hε
    obtain ⟨u, v, hu, huv, hu2, hv2⟩ := hs ε hε
    calc I ≤ ∫⁻ w, 2 * (‖u w‖ₑ ^ 2 + ‖v w‖ₑ ^ 2) ∂ν := by
          refine lintegral_mono fun w => ?_
          rw [huv]
          exact hpt (u w) (v w)
      _ = 2 * (∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν + ∫⁻ w, ‖v w‖ₑ ^ 2 ∂ν) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (hu.enorm.pow_const 2)]
      _ ≤ 2 * (ENNReal.ofReal (ε ^ 2) * M + ENNReal.ofReal (ε ^ 2) * N) := by gcongr
      _ = ENNReal.ofReal (ε ^ 2) * (2 * (M + N)) := by ring
  have hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2) * (2 * (M + N))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_pow 2).tendsto (0 : ℝ))
      simpa using (ENNReal.tendsto_ofReal (this.mono_left nhdsWithin_le_nhds))
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hK)
  have hI0 : I = 0 := by
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [self_mem_nhdsWithin] with ε hε using hle ε hε
  have hae := (lintegral_eq_zero_iff (hm.enorm.pow_const 2)).1 hI0
  filter_upwards [hae] with w hw
  simpa using hw

theorem schur (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : Schur ψ S T := by
  intro μ 𝓕 hμ h𝓕 A hAθ hAc hAb
  obtain ⟨C, hC⟩ := hAb
  have hE := isExpChar_of_isCharAF hψ
  have hn := hE.2.1
  have : μ.IsAddHaarMeasure := hμ
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hχc, hχadd, hχadd', hχ0, hχn, hχker⟩ := chiR_laws (S := S) (T := T) hψ
  have hfin : μ 𝓕 ≠ ⊤ := by
    obtain ⟨N, hN⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov).2
      (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    exact (hN μ 𝓕 hμ h𝓕).2.1

  have hmulχ : ∀ γ ∈ ratL T S, ∀ g, IsThetaFunO ψ S T g → A (chi ψ S T γ * g) = chi ψ S T γ * A g := by
    intro γ hγ g hg
    rw [← heisO_rat hγ hg, ← heisO_rat hγ (hAθ g hg)]
    exact hAc _ g hg
  have htp : ∀ (s : Finset (ratL T S)) (c : ratL T S → ℂ) g, IsThetaFunO ψ S T g →
      A ((∑ a ∈ s, c a • chiR ψ S T a) * g) = (∑ a ∈ s, c a • chiR ψ S T a) * A g := by
    intro s c g hg
    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul]
    congr 1
    exact hmulχ a a.2 g hg

  have hcomm : ∀ Φ, IsThetaFunO 1 S T Φ → ∀ g, IsThetaFunO ψ S T g → A (Φ * g) = Φ * A g := by
    intro Φ hΦ g hg
    have hAg := hAθ g hg
    obtain ⟨Bg, hBg0, hBg⟩ := exists_bound hn hg
    obtain ⟨Ba, hBa0, hBa⟩ := exists_bound hn hAg
    have hh : IsThetaFunO ψ S T (A (Φ * g) - Φ * A g) :=
      isTheta_sub (hAθ _ (isTheta_one_mul hΦ hg)) (isTheta_one_mul hΦ hAg)
    have hae : ∀ᵐ w ∂μ.restrict 𝓕, (A (Φ * g) - Φ * A g) w = 0 := by
      refine ae_zero_of_small (μ.restrict 𝓕) (M := (C : ℝ≥0∞) * (ENNReal.ofReal (Bg ^ 2) * μ 𝓕))
        (N := ENNReal.ofReal (Ba ^ 2) * μ 𝓕) hh.cont.measurable ?_ ?_ ?_
      · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
      intro ε hε
      obtain ⟨s, c, happ⟩ := GlobalTheory.trigPoly_dense_periodic (WO S T) (ratL T S) K hK hcov (ratL T S) (chiR ψ S T)
        hχc hχadd hχadd' hχ0 hχn hχker Φ hΦ.cont (periodic_of_one hΦ) ε hε
      obtain ⟨P, hPdef⟩ : ∃ P : WO S T → ℂ, P = ∑ a ∈ s, c a • chiR ψ S T a := ⟨_, rfl⟩
      have hPθ : IsThetaFunO 1 S T P := by
        rw [hPdef]
        exact isTheta_sum s _ fun a _ => isTheta_smul _ (isTheta_chi hψ a.2)
      have hPA : A (P * g) = P * A g := by
        rw [hPdef]
        exact htp s c g hg
      have hPapp : ∀ x, ‖(Φ - P) x‖ ≤ ε := by
        intro x
        rw [hPdef]
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using happ x
      have hDθ : IsThetaFunO 1 S T (Φ - P) := isTheta_sub hΦ hPθ
      refine ⟨A ((Φ - P) * g), (Φ - P) * A g, (hAθ _ (isTheta_one_mul hDθ hg)).cont.measurable, ?_, ?_, ?_⟩
      · rw [sub_mul, sub_mul, map_sub, hPA]
        abel
      · calc ∫⁻ w, ‖A ((Φ - P) * g) w‖ₑ ^ 2 ∂μ.restrict 𝓕
            ≤ (C : ℝ≥0∞) * ∫⁻ w, ‖((Φ - P) * g) w‖ₑ ^ 2 ∂μ.restrict 𝓕 := hC _ (isTheta_one_mul hDθ hg)
          _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Bg ^ 2) * (μ.restrict 𝓕) Set.univ)) := by
              gcongr
              refine lintegral_sq_le _ fun w => ?_
              rw [Pi.mul_apply, norm_mul]
              exact mul_le_mul (hPapp w) (hBg w) (norm_nonneg _) hε.le
          _ = ENNReal.ofReal (ε ^ 2) * ((C : ℝ≥0∞) * (ENNReal.ofReal (Bg ^ 2) * μ 𝓕)) := by
              rw [Measure.restrict_apply_univ]
              ring
      · calc ∫⁻ w, ‖((Φ - P) * A g) w‖ₑ ^ 2 ∂μ.restrict 𝓕
            ≤ ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Ba ^ 2) * (μ.restrict 𝓕) Set.univ) := by
              refine lintegral_sq_le _ fun w => ?_
              rw [Pi.mul_apply, norm_mul]
              exact mul_le_mul (hPapp w) (hBa w) (norm_nonneg _) hε.le
          _ = ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Ba ^ 2) * μ 𝓕) := by
              rw [Measure.restrict_apply_univ]
    have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hh.cont
      (norm_periodic' hn hh) hae
    exact sub_eq_zero.1 hz

  obtain ⟨g, hg, hg0⟩ := exists_theta_zero_ne hψ S T
  have hpt : ∀ f, IsThetaFunO ψ S T f → A f 0 = A g 0 / g 0 * f 0 := by
    intro f hf
    have e1 := hcomm (f * star g) (isTheta_mul_star hn hf hg) g hg
    have e2 := hcomm (g * star g) (isTheta_mul_star hn hg hg) f hf
    have e3 : f * star g * g = g * star g * f := by ring
    rw [e3, e2] at e1
    have e0 := congrFun e1 0
    simp only [Pi.mul_apply, Pi.star_apply] at e0
    have hs : star (g 0) ≠ 0 := star_ne_zero.2 hg0
    rw [div_mul_eq_mul_div, eq_div_iff hg0]
    apply mul_right_cancel₀ hs
    linear_combination e0

  refine ⟨A g 0 / g 0, fun f hf => ?_⟩
  funext x
  have h1 := hpt (heisO ψ S T x f) (isTheta_heis hE hf x)
  rw [hAc x f hf, heisO_apply_zero, heisO_apply_zero] at h1
  rw [Pi.smul_apply, smul_eq_mul]
  exact h1

theorem word_bound (hψ : IsExpChar ψ) (Ls : List (ℝ →+ WO S T)) (hL : ∀ L ∈ Ls, IsRealDir L) :
    ∀ g, IsThetaFunO ψ S T g → ∃ (Ms : List (List (ℝ →+ WO S T))) (C : ℝ), 0 ≤ C ∧ (∀ M ∈ Ms, ∀ L ∈ M, IsRealDir L) ∧
      ∀ Φ, IsThetaFunO 1 S T Φ → ∀ B : ℝ, 0 ≤ B → (∀ M ∈ Ms, ∀ w, ‖dHeisWord 1 S T M Φ w‖ ≤ B) →
        ∀ w, ‖dHeisWord ψ S T Ls (Φ * g) w‖ ≤ C * B := by
  induction Ls using List.reverseRecOn with
  | nil =>
    intro g hg
    obtain ⟨Bg, hBg0, hBg⟩ := exists_bound hψ.2.1 hg
    refine ⟨[[]], Bg, hBg0, by simp, ?_⟩
    intro Φ _ B hB hΦB w
    have h1 : ‖Φ w‖ ≤ B := hΦB [] (by simp) w
    show ‖Φ w * g w‖ ≤ Bg * B
    rw [norm_mul]
    calc ‖Φ w‖ * ‖g w‖ ≤ B * Bg := mul_le_mul h1 (hBg w) (norm_nonneg _) hB
      _ = Bg * B := mul_comm _ _
  | append_singleton Ls L ih =>
    intro g hg
    have hL' : IsRealDir L := hL L (by simp)
    have hLs : ∀ L ∈ Ls, IsRealDir L := fun L' h' => hL L' (by simp [h'])
    obtain ⟨Ms1, C1, hC1, hM1, h1⟩ := ih hLs g hg
    have hg' := (hasDerivAt_and_isTheta hψ hL' hg).2
    obtain ⟨Ms2, C2, hC2, hM2, h2⟩ := ih hLs _ hg'
    refine ⟨Ms1.map (· ++ [L]) ++ Ms2, C1 + C2, add_nonneg hC1 hC2, ?_, ?_⟩
    · intro M hM L'' hL''
      rcases List.mem_append.1 hM with hM | hM
      · obtain ⟨M', hM', rfl⟩ := List.mem_map.1 hM
        rcases List.mem_append.1 hL'' with h | h
        · exact hM1 M' hM' L'' h
        · rw [List.mem_singleton.1 h]
          exact hL'
      · exact hM2 M hM L'' hL''
    · intro Φ hΦ B hB hΦB w
      have hΦ' := (hasDerivAt_and_isTheta isExpChar_one hL' hΦ).2
      have e : dHeisWord ψ S T (Ls ++ [L]) (Φ * g) =
          dHeisWord ψ S T Ls (dHeis 1 S T L Φ * g) + dHeisWord ψ S T Ls (Φ * dHeis ψ S T L g) := by
        rw [dHeisWord_concat, dHeis_one_mul hψ hL' hΦ hg,
          dHeisWord_add hψ hLs (isTheta_one_mul hΦ' hg) (isTheta_one_mul hΦ hg')]
      have b1 := h1 (dHeis 1 S T L Φ) hΦ' B hB (fun M hM w => by
        rw [← dHeisWord_concat]
        exact hΦB _ (List.mem_append_left _ (List.mem_map.2 ⟨M, hM, rfl⟩)) w) w
      have b2 := h2 Φ hΦ B hB (fun M hM w => hΦB M (List.mem_append_right _ hM) w) w
      rw [e, Pi.add_apply]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ C1 * B + C2 * B := add_le_add b1 b2
        _ = (C1 + C2) * B := by ring

theorem words_bound (hψ : IsExpChar ψ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (W : List (List (ℝ →+ WO S T)))
    (hW : ∀ Ls ∈ W, ∀ L ∈ Ls, IsRealDir L) :
    ∃ (Ms : List (List (ℝ →+ WO S T))) (C : ℝ), 0 ≤ C ∧ (∀ M ∈ Ms, ∀ L ∈ M, IsRealDir L) ∧
      ∀ Φ, IsThetaFunO 1 S T Φ → ∀ B : ℝ, 0 ≤ B → (∀ M ∈ Ms, ∀ w, ‖dHeisWord 1 S T M Φ w‖ ≤ B) →
        ∀ Ls ∈ W, ∀ w, ‖dHeisWord ψ S T Ls (Φ * g) w‖ ≤ C * B := by
  induction W with
  | nil => exact ⟨[], 0, le_rfl, by simp, fun _ _ _ _ _ _ hLs _ => by simp at hLs⟩
  | cons Ls W ih =>
    obtain ⟨Ms1, C1, hC1, hM1, h1⟩ := word_bound hψ Ls (hW Ls (by simp)) g hg
    obtain ⟨Ms2, C2, hC2, hM2, h2⟩ := ih (fun Ls' h' => hW Ls' (by simp [h']))
    refine ⟨Ms1 ++ Ms2, C1 + C2, add_nonneg hC1 hC2, ?_, ?_⟩
    · intro M hM
      rcases List.mem_append.1 hM with h | h
      exacts [hM1 M h, hM2 M h]
    · intro Φ hΦ B hB hΦB Ls' hLs' w
      rcases List.mem_cons.1 hLs' with rfl | h
      · calc _ ≤ C1 * B := h1 Φ hΦ B hB (fun M hM => hΦB M (List.mem_append_left _ hM)) w
          _ ≤ (C1 + C2) * B := by nlinarith
      · calc _ ≤ C2 * B := h2 Φ hΦ B hB (fun M hM => hΦB M (List.mem_append_right _ hM)) Ls' h w
          _ ≤ (C1 + C2) * B := by nlinarith

theorem isThetaCont_mul (hψ : IsExpChar ψ) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : IsThetaCont ψ S T ℓ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : IsThetaCont 1 S T (ℓ ∘ₗ LinearMap.mulRight ℂ g) := by
  intro U hU
  obtain ⟨V, hV, hVg⟩ := hg.level
  have hUV : IsOpen ((U ⊓ V : AddSubgroup (WO S T)) : Set (WO S T)) := by
    rw [AddSubgroup.coe_inf]
    exact hU.inter hV
  obtain ⟨words, C, hw, hC⟩ := hℓ (U ⊓ V) hUV
  obtain ⟨Ms, C', hC', hMs, hb⟩ := words_bound hψ hg words hw
  refine ⟨Ms, C * C', hMs, ?_⟩
  intro Φ hΦ hΦU B hB hΦB
  have hlev : HasLevel ψ S T (U ⊓ V) (Φ * g) := by
    intro u hu hu0
    rw [heisO_one_mul, hΦU u (AddSubgroup.mem_inf.1 hu).1 hu0, hVg u (AddSubgroup.mem_inf.1 hu).2 hu0]
  have := hC (Φ * g) (isTheta_one_mul hΦ hg) hlev (C' * B) (mul_nonneg hC' hB) (hb Φ hΦ B hB hΦB)
  simpa [LinearMap.comp_apply, LinearMap.mulRight_apply, mul_assoc] using this

def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (Φ : WO S T → ℂ)
    (γ : WO S T) : ℂ :=
  ∫ y in 𝓕, Φ y * starRingEnd ℂ (chi ψ S T γ y) ∂μ

theorem eq_mul_of_chi (hψ : IsCharAF D.host.F ψ) {m : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hm : IsThetaCont 1 S T m) {κ : ℂ}
    (hκ : ∀ γ ∈ ratL T S, m (chi ψ S T γ) = κ) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO 1 S T Φ) : m Φ = κ * Φ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov
  obtain ⟨hχc, hχadd, hχadd', hχ0, hχn, hχker⟩ := chiR_laws (S := S) (T := T) hψ
  have hE1 : IsExpChar (1 : AddChar (AF D.host.F) ℂ) := isExpChar_one

  let cf : (WO S T → ℂ) → ratL T S → ℂ := fun Ψ a => ∫ y in 𝓕, Ψ y * starRingEnd ℂ (chiR ψ S T a y) ∂μ
  let tr : Finset (ratL T S) → (ratL T S → ℂ) → (WO S T → ℂ) → WO S T → ℂ :=
    fun s c Ψ => ∑ a ∈ s, (c a * cf Ψ a) • chiR ψ S T a
  have tr_apply : ∀ s c Ψ x, tr s c Ψ x = ∑ a ∈ s, c a * (cf Ψ a * chiR ψ S T a x) := by
    intro s c Ψ x
    simp only [tr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have tr_theta : ∀ s c Ψ, IsThetaFunO 1 S T (tr s c Ψ) := fun s c Ψ =>
    isTheta_sum s _ fun a _ => isTheta_smul _ (isTheta_chi hψ a.2)
  have hper : ∀ Ψ, IsThetaFunO 1 S T Ψ → Continuous Ψ ∧ ∀ γ ∈ ratL T S, ∀ x, Ψ (γ + x) = Ψ x :=
    fun Ψ hΨ => ⟨hΨ.cont, periodic_of_one hΨ⟩

  have claws := fun (a : ratL T S) (Ψ : WO S T → ℂ) (hΨ : IsThetaFunO 1 S T Ψ) =>
    GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt (WO S T) (ratL T S) K hK hcov μ 𝓕 hμ h𝓕
      (chiR ψ S T a) (hχc a) (hχadd a) (hχn a) (fun γ hγ => chi_rat hψ a.2 hγ) Ψ (hper Ψ hΨ).1 (hper Ψ hΨ).2

  have tr_dHeis : ∀ s c (L : ℝ →+ WO S T), IsRealDir L → ∀ Ψ, IsThetaFunO 1 S T Ψ →
      dHeis 1 S T L (tr s c Ψ) = tr s c (dHeis 1 S T L Ψ) := by
    intro s c L hL Ψ hΨ
    have hd := hasDerivAt_and_isTheta hE1 hL hΨ
    funext x
    have hline : ∀ w, HasDerivAt (fun t : ℝ => Ψ (w + L t)) (dHeis 1 S T L Ψ w) 0 := by
      intro w
      have hw := hd.1 w
      simp only [heisO_one_apply] at hw
      exact hw
    have hsum : HasDerivAt (fun t : ℝ => tr s c Ψ (x + L t)) (tr s c (dHeis 1 S T L Ψ) x) 0 := by
      have hterm : ∀ a ∈ s, HasDerivAt (fun t : ℝ => c a * (cf Ψ a * chiR ψ S T a (x + L t)))
          (c a * (cf (dHeis 1 S T L Ψ) a * chiR ψ S T a x)) 0 := fun a _ =>
        ((claws a Ψ hΨ).2 L _ (hper _ hd.2).1 (hper _ hd.2).2 hline x).const_mul (c a)
      simp only [tr_apply]
      have hs' := HasDerivAt.sum hterm
      rw [Finset.sum_fn] at hs'
      exact hs'
    have e : (fun t : ℝ => heisO 1 S T (L t) (tr s c Ψ) x) = fun t => tr s c Ψ (x + L t) := by
      funext t
      rw [heisO_one_apply]
    show deriv (fun t : ℝ => heisO 1 S T (L t) (tr s c Ψ) x) 0 = _
    rw [e]
    exact hsum.deriv
  obtain ⟨V, hV, hVΦ⟩ := hΦ.level
  have hfix : ∀ u ∈ V, u.map (infPart D) = 0 → ∀ y, Φ (u + y) = Φ y := by
    intro u hu hu0 y
    have hy := congrFun (hVΦ u hu hu0) y
    rw [heisO_one_apply, add_comm] at hy
    exact hy

  have tr_level : ∀ s c, HasLevel 1 S T V (tr s c Φ) := by
    intro s c u hu hu0
    funext w
    rw [heisO_one_apply, tr_apply, tr_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hconv := (claws a Φ hΦ).1 u
    simp only [hfix u hu hu0] at hconv
    have hconv' : cf Φ a * chiR ψ S T a u = cf Φ a := hconv
    rw [hχadd a w u]
    congr 1
    calc cf Φ a * (chiR ψ S T a w * chiR ψ S T a u) = chiR ψ S T a w * (cf Φ a * chiR ψ S T a u) := by ring
      _ = cf Φ a * chiR ψ S T a w := by rw [hconv']; ring
  obtain ⟨words, C, hw, hC⟩ := hm V hV
  have hbound : ∀ ε : ℝ, 0 < ε → ‖m Φ - κ * Φ 0‖ ≤ (C + ‖κ‖) * ε := by
    intro ε hε
    have hl : ∀ Ψ ∈ (Φ :: words.map fun M => dHeisWord 1 S T M Φ),
        Continuous Ψ ∧ ∀ γ ∈ ratL T S, ∀ x, Ψ (γ + x) = Ψ x := by
      intro Ψ hΨ
      rcases List.mem_cons.1 hΨ with rfl | hΨ
      · exact hper _ hΦ
      · obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hΨ
        exact hper _ (isTheta_dHeisWord hE1 (hw M hM) hΦ)
    obtain ⟨s, c, happ⟩ := GlobalTheory.exists_summation_kernel_periodic (WO S T) (ratL T S) K hK hcov (ratL T S)
      (chiR ψ S T) hχc hχadd hχadd' hχ0 hχn hχker μ 𝓕 hμ h𝓕 _ hl ε hε
    have tr_word : ∀ M : List (ℝ →+ WO S T), (∀ L ∈ M, IsRealDir L) → ∀ Ψ, IsThetaFunO 1 S T Ψ →
        dHeisWord 1 S T M (tr s c Ψ) = tr s c (dHeisWord 1 S T M Ψ) := by
      intro M
      induction M using List.reverseRecOn with
      | nil => intro _ Ψ _; rfl
      | append_singleton M L ih =>
        intro hML Ψ hΨ
        have hL : IsRealDir L := hML L (by simp)
        rw [dHeisWord_concat, dHeisWord_concat, tr_dHeis s c L hL Ψ hΨ,
          ih (fun L' h' => hML L' (by simp [h'])) _ (hasDerivAt_and_isTheta hE1 hL hΨ).2]
    have hRθ : IsThetaFunO 1 S T (Φ - tr s c Φ) := isTheta_sub hΦ (tr_theta s c Φ)
    have hRlev : HasLevel 1 S T V (Φ - tr s c Φ) := by
      intro u hu hu0
      funext w
      have a2 := congrFun (tr_level s c u hu hu0) w
      rw [heisO_one_apply] at a2
      rw [heisO_one_apply, Pi.sub_apply, Pi.sub_apply, a2, add_comm, hfix u hu hu0]
    have eR : Φ - tr s c Φ = Φ + (-1 : ℂ) • tr s c Φ := by
      rw [neg_one_smul, sub_eq_add_neg]
    have hRder : ∀ M ∈ words, ∀ w, ‖dHeisWord 1 S T M (Φ - tr s c Φ) w‖ ≤ ε := by
      intro M hM w
      have e : dHeisWord 1 S T M (Φ - tr s c Φ) = dHeisWord 1 S T M Φ - tr s c (dHeisWord 1 S T M Φ) := by
        rw [eR, dHeisWord_add hE1 (hw M hM) hΦ (isTheta_smul _ (tr_theta s c Φ)), dHeisWord_smul,
          tr_word M (hw M hM) Φ hΦ, neg_one_smul, ← sub_eq_add_neg]
      rw [e, Pi.sub_apply, tr_apply]
      exact happ _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨M, hM, rfl⟩)) w
    have hmR := hC _ hRθ hRlev ε hε.le hRder
    have h0 : ‖Φ 0 - tr s c Φ 0‖ ≤ ε := by
      rw [tr_apply]
      exact happ Φ List.mem_cons_self 0
    have hmT : m (tr s c Φ) = κ * tr s c Φ 0 := by
      rw [tr_apply]
      simp only [tr, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show chiR ψ S T a = chi ψ S T a from rfl, hκ _ a.2, chi_zero]
      ring
    have e2 : m Φ - κ * Φ 0 = m (Φ - tr s c Φ) - κ * (Φ 0 - tr s c Φ 0) := by
      rw [map_sub, hmT]
      ring
    rw [e2]
    calc ‖m (Φ - tr s c Φ) - κ * (Φ 0 - tr s c Φ 0)‖ ≤ ‖m (Φ - tr s c Φ)‖ + ‖κ‖ * ‖Φ 0 - tr s c Φ 0‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * ε + ‖κ‖ * ε := by gcongr
      _ = (C + ‖κ‖) * ε := by ring

  have hz : ‖m Φ - κ * Φ 0‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖m Φ - κ * Φ 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hKpos : 0 < |C| + ‖κ‖ + 1 := by positivity
    have hb := hbound (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) (by positivity)
    have hCle : C + ‖κ‖ ≤ |C| + ‖κ‖ + 1 := by linarith [le_abs_self C]
    have hmono : (C + ‖κ‖) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) ≤
        (|C| + ‖κ‖ + 1) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) := by
      gcongr
    have e : (|C| + ‖κ‖ + 1) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) = ‖m Φ - κ * Φ 0‖ / 2 := by
      field_simp
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

theorem thetaUnique (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : ThetaUnique ψ S T := by
  intro ℓ hinv hℓ
  have hE := isExpChar_of_isCharAF hψ
  obtain ⟨g, hg, hg0⟩ := exists_theta_zero_ne hψ S T

  have hmul : ∀ h, IsThetaFunO ψ S T h → ∀ Φ, IsThetaFunO 1 S T Φ → ℓ (Φ * h) = ℓ h * Φ 0 := by
    intro h hh Φ hΦ
    have key := eq_mul_of_chi (m := ℓ ∘ₗ LinearMap.mulRight ℂ h) (κ := ℓ h) hψ (isThetaCont_mul hE hℓ hh) ?_ hΦ
    · simpa using key
    intro γ hγ
    obtain ⟨γ', rfl⟩ := hγ
    change ℓ (chi ψ S T _ * h) = ℓ h
    rw [← heisO_rat ⟨γ', rfl⟩ hh]
    exact hinv γ' h hh
  refine ⟨ℓ g / g 0, fun f hf => ?_⟩

  have e1 := hmul g hg (f * star g) (isTheta_mul_star hE.2.1 hf hg)
  have e2 := hmul f hf (g * star g) (isTheta_mul_star hE.2.1 hg hg)
  have e3 : f * star g * g = g * star g * f := by ring
  rw [e3, e2] at e1
  simp only [Pi.mul_apply, Pi.star_apply] at e1
  have hs : star (g 0) ≠ 0 := star_ne_zero.2 hg0
  have e4 : ℓ f * g 0 = ℓ g * f 0 := by
    apply mul_right_cancel₀ hs
    linear_combination e1
  rw [div_mul_eq_mul_div, eq_div_iff hg0]
  exact e4

theorem covolOneExists (S T : HSp D) : CovolOneExists S T := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, hvol⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov
  exact ⟨μ, 𝓕, hμ, h𝓕, hvol⟩

theorem heisenbergLemma (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : HeisenbergLemma ψ S T := by
  intro μ μ' 𝓕 𝓕' hc hc' f f' hf hf'
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have hn := (isExpChar_of_isCharAF hψ).2.1
  have hΦ := isTheta_mul_star hn hf hf'
  obtain ⟨hμ, h𝓕, hv⟩ := hc
  obtain ⟨hμ', h𝓕', hv'⟩ := hc'

  have key := GlobalTheory.mean_periodic_indep_of_covolume_one (WO S T) (ratL T S) K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 hv hμ' h𝓕'
    hv' (f * star f') hΦ.cont (periodic_of_one hΦ)
  have key' := GlobalTheory.mean_periodic_indep_of_covolume_one (WO S T) (ratL T S) K hK hcov μ' μ 𝓕' 𝓕 hμ' h𝓕' hv' hμ h𝓕
    hv (f * star f') hΦ.cont (periodic_of_one hΦ)
  simp only [heisO_apply_zero]
  exact ⟨key.1, key'.1, key.2⟩

theorem thetaFacts (D : D7) : ThetaFacts D := by
  intro ψ hψ S T
  refine ⟨schur hψ S T, thetaUnique hψ S T, ⟨covolOneExists S T, heisenbergLemma hψ S T⟩, ?_⟩
  obtain ⟨g, hg, h0⟩ := exists_theta_zero_ne hψ S T
  exact ⟨g, hg, fun h => h0 (by simp [h])⟩

end GlobalTheory.ThetaAllChar

end
