import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotientsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.EulerAtTwist

open GlobalTheory.LFun in

theorem eulerProd_eq_mul_prod {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {S₀ S : Set (HeightOneSpectrum (𝓞 F))} {A : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v, v ∈ S ↔ v ∈ S₀ ∨ v ∈ A) (hA : ∀ v ∈ A, v ∉ S₀) {c : Fam E} {r : ℕ} {κ : ℝ}
    (hb : ∀ T, Bounded T c r κ) {s : ℂ} (hs : κ + 1 < s.re) :
    eulerProd (above E S₀) c s = eulerProd (above E S) c s * ∏ v ∈ A, Lv c v s := by
  have h1 := hasProd_Lv ((hb (above E S₀)).converges hs)
  have h2 : HasProd ((fun v => Lv c v s) ∘ ((↑) : ↥(Sᶜ) → HeightOneSpectrum (𝓞 F))) (LS S c s) :=
    hasProd_Lv ((hb (above E S)).converges hs)
  have h3 := A.hasProd (fun v => Lv c v s)
  have hdisj : Disjoint (Sᶜ) (↑A : Set (HeightOneSpectrum (𝓞 F))) :=
    Set.disjoint_left.2 fun v hv hvA => hv ((hS v).2 (Or.inr hvA))
  have h4 := h2.mul_disjoint hdisj h3
  have e : Sᶜ ∪ (↑A : Set (HeightOneSpectrum (𝓞 F))) = S₀ᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_compl_iff, Finset.mem_coe]
    constructor
    · rintro (h | h)
      · exact fun h0 => h ((hS v).2 (Or.inl h0))
      · exact hA v h
    · intro h
      by_cases hv : v ∈ S
      · exact Or.inr (((hS v).1 hv).resolve_left h)
      · exact Or.inl hv
  rw [e] at h4
  exact h1.unique h4

open GlobalTheory.LFun in

theorem Lv_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : Fam E)
    {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)} (hne : P' ≠ P)
    (hv : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = P ∨ u = P') (s : ℂ) :
    Lv c v s = locL c P s * locL c P' s := by
  classical
  have e : Formalism.L2.Host.aboveF (L := E) F v = {P, P'} := by ext u; simp [GlobalTheory.LFun.mem_aboveF, hv]
  rw [Lv, e, Finset.prod_pair hne.symm]

open GlobalTheory.LFun in
theorem norm_npow_lt_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : 0 < z.re) :
    ‖npow P (-z)‖ < 1 := by
  rw [norm_npow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm P) (by simpa using hz)

open GlobalTheory.LFun in
theorem one_sub_ne_zero {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {b : ℂ} (hb : ‖b‖ = 1)
    {z : ℂ} (hz : 0 < z.re) : 1 - b * npow P (-z) ≠ 0 := fun h => by
  have h1 : b * npow P (-z) = 1 := (sub_eq_zero.1 h).symm
  have h2 := norm_npow_lt_one P hz
  have h3 := congrArg norm h1
  rw [norm_mul, hb, one_mul, norm_one] at h3
  linarith

open GlobalTheory.LFun in
theorem npow_neg_natCast {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    npow P (-(n : ℂ)) = ((Ideal.absNorm P.asIdeal : ℂ) ^ n)⁻¹ := by
  rw [npow, Complex.cpow_neg, Complex.cpow_natCast]

open GlobalTheory.LFun in
theorem differentiable_factor {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (b : ℂ) :
    Differentiable ℂ fun z : ℂ => 1 - b * npow P (-z) :=
  (differentiable_const _).sub ((differentiable_const _).mul
    (differentiable_neg.const_cpow (Or.inl (by exact_mod_cast (one_lt_absNorm P).ne_bot))))

end GlobalTheory.ChainTw.EulerAtTwist

namespace GlobalTheory.ChainTw.EulerAtTwist

variable {D : D7}

theorem quotL_entire_ne_zero_off (c : Com D) (hc : c.Is) (S' : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ D.R.m)
    (hunr : GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧
      HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e' :=
    ⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ,
      (QuotL.e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))).ne⟩
  obtain ⟨Λ, ⟨hd, hp⟩, hpos⟩ := (GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1))
    (QuotL.isHecke hc (by omega) (by omega)) (QuotL.isHecke hc (by omega) hj) (QuotL.trivialOnF hc (by omega) (by omega))
    (QuotL.trivialOnF hc (by omega) hj) hexp D.R.t).2 S'
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩
  · have hoff : ∀ P, OffS D S' P ↔ P ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff S' P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · have := (hpos n h1 h2).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

open GlobalTheory.LFun in

theorem eval_relation (c : Com D) (w : Twist D) (hw : w.Is c) {i j : ℕ} (hi : i ∈ Finset.Icc 1 D.R.m)
    (hj : j ∈ Finset.Icc 1 D.R.m) {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hΛ₀ : Differentiable ℂ Λ₀)
    (e : ∀ z : ℂ, 1 < z.re → Λ z = eulerProd (above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
      (fun w => {val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z)
    (e₀ : ∀ z : ℂ, 1 < z.re → Λ₀ z = eulerProd (above D.host.E w.S₀)
      (fun w => {val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z)
    (n : ℕ) (hn : 1 ≤ n) :
    Λ₀ n = Λ n * ∏ PP ∈ w.Q,
      ((1 - (val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP : ℂ) * ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹) *
        (1 - (val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP : ℂ)⁻¹ * ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  classical
  obtain ⟨hS, hQS, hinj, hpair, -⟩ := GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients D c w hw
  have hpair' : ∀ PP ∈ w.Q, ∃ PP' : Pl D.host.E, PP' ≠ PP ∧
      (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) ↔ P = PP ∨ P = PP') ∧
      Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧
      val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹ :=
    fun PP hPP => by
      obtain ⟨-, -, PP', h1, h2, h3, h4⟩ := hpair PP hPP
      exact ⟨PP', h1, h2, h3, h4 i hi j hj⟩
  clear hpair
  generalize c.μ i * (c.μ j)⁻¹ = χ at e e₀ hpair' ⊢
  set f : Fam D.host.E := fun w => {val (F := D.host.F) χ w} with hf
  have hb : ∀ T, Bounded T f 1 0 := fun T w _ =>
    ⟨by simp [hf], fun b hb => by
      rw [hf] at hb
      rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, norm_val]⟩
  have hu : ∀ PP, ‖(val (F := D.host.F) χ PP : ℂ)‖ = 1 := fun PP => norm_val _ _
  have hu' : ∀ PP, ‖(val (F := D.host.F) χ PP : ℂ)⁻¹‖ = 1 := fun PP => by rw [norm_inv, hu, inv_one]

  let P : ℂ → ℂ := fun z => ∏ PP ∈ w.Q, ((1 - (val (F := D.host.F) χ PP : ℂ) * npow PP (-z)) *
    (1 - (val (F := D.host.F) χ PP : ℂ)⁻¹ * npow PP (-z)))
  have hPd : Differentiable ℂ P := by
    intro z
    refine DifferentiableAt.fun_finsetProd fun PP _ => ?_
    exact ((differentiable_factor PP _).mul (differentiable_factor PP _)) z
  have hPne : ∀ z : ℂ, 0 < z.re → ∀ PP, (1 - (val (F := D.host.F) χ PP : ℂ) * npow PP (-z)) *
      (1 - (val (F := D.host.F) χ PP : ℂ)⁻¹ * npow PP (-z)) ≠ 0 := fun z hz PP =>
    mul_ne_zero (one_sub_ne_zero PP (hu PP) hz) (one_sub_ne_zero PP (hu' PP) hz)

  let A : Finset (HeightOneSpectrum (𝓞 D.host.F)) := w.Q.image fun PP => PP.under (𝓞 D.host.F)
  have hS' : ∀ v, v ∈ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ↔ v ∈ w.S₀ ∨ v ∈ A := fun v =>
    (hS v).trans (or_congr_right Finset.mem_image.symm)
  have hA : ∀ v ∈ A, v ∉ w.S₀ := fun v hv => by
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    exact hQS PP hPP
  have hrel : ∀ z : ℂ, 1 < z.re → Λ₀ z * P z = Λ z := fun z hz => by
    have hz0 : (0 : ℝ) < z.re := by linarith
    rw [e₀ z hz, e z hz, eulerProd_eq_mul_prod hS' hA hb (by simpa using hz), Finset.prod_image hinj, mul_assoc,
      ← Finset.prod_mul_distrib]
    conv_rhs => rw [← mul_one (eulerProd _ _ _)]
    congr 1
    refine Finset.prod_eq_one fun PP hPP => ?_
    obtain ⟨PP', hne, hv, hN, hval⟩ := hpair' PP hPP
    rw [Lv_pair f hne hv]
    have hnp : npow PP' (-z) = npow PP (-z) := by simp only [npow, hN]
    have l1 : locL f PP z = (1 - (val (F := D.host.F) χ PP : ℂ) * npow PP (-z))⁻¹ := by
      simp only [hf, locL, eulerFac_singleton]
    have l2 : locL f PP' z = (1 - (val (F := D.host.F) χ PP : ℂ)⁻¹ * npow PP (-z))⁻¹ := by
      simp only [hf, locL, eulerFac_singleton, hnp, hval, Units.val_inv_eq_inv_val]
    rw [l1, l2]
    have h1 := one_sub_ne_zero PP (hu PP) hz0
    have h2 := one_sub_ne_zero PP (hu' PP) hz0
    rw [mul_mul_mul_comm, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, one_mul]

  have hall : (fun z => Λ₀ z * P z) = Λ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq ((hΛ₀.mul hPd).differentiableOn.analyticOnNhd isOpen_univ)
      (hΛ.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := 2) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hrel z hz
  have hn0 : (0 : ℝ) < (n : ℂ).re := by simp; omega
  have k := congrFun hall n
  have hPn : P n ≠ 0 := Finset.prod_ne_zero_iff.2 fun PP _ => hPne n hn0 PP
  rw [← k, mul_assoc]
  have : ∏ PP ∈ w.Q, ((1 - (val (F := D.host.F) χ PP : ℂ) * ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹) *
      (1 - (val (F := D.host.F) χ PP : ℂ)⁻¹ * ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹))⁻¹ = (P n)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [npow_neg_natCast]
  rw [this, mul_inv_cancel₀ hPn, mul_one]

end GlobalTheory.ChainTw.EulerAtTwist

namespace GlobalTheory.ChainTw.EulerAtTwist

open GlobalTheory.LFun in

theorem restore_hval : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m,
    (∀ H H₀, IsHval c (c.S : Set _) k H → IsHval c w.S₀ k H₀ → H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) ∧
    ∃ H₀, H₀ ≠ 0 ∧ IsHval c w.S₀ k H₀ := by
  intro D c w hw k hk
  have hmem : ∀ i ∈ Finset.Icc 1 k, i ∈ Finset.Icc 1 D.R.m ∧ k + 1 ∈ Finset.Icc 1 D.R.m := fun i hi => by
    have := Finset.mem_Icc.1 hi
    exact ⟨Finset.mem_Icc.2 ⟨this.1, by omega⟩, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  refine ⟨fun H H₀ ⟨Λ, hΛ, hH⟩ ⟨Λ₀, hΛ₀, hH₀⟩ => ?_, ?_⟩
  · subst hH hH₀
    have key : ∀ i ∈ Finset.Icc 1 k, ∀ n ∈ Finset.Icc 1 D.R.t, Λ₀ i n = Λ i n *
        ∏ PP ∈ w.Q, ((1 - (val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP : ℂ) *
          ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹) * (1 - (val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP : ℂ)⁻¹ *
            ((Ideal.absNorm PP.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := fun i hi n hn =>
      eval_relation c w hw (hmem i hi).1 (hmem i hi).2 (hΛ i hi).1 (hΛ₀ i hi).1 (hΛ i hi).2 (hΛ₀ i hi).2 n
        (Finset.mem_Icc.1 hn).1
    rw [Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun n hn => key i hi n hn]
    simp only [Finset.prod_mul_distrib]
    congr 1
    unfold blockL
    rw [Finset.prod_comm (s := w.Q)]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_comm
  · obtain ⟨-, -, -, -, hunr⟩ := GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients D c w hw
    obtain ⟨S', hS'⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 D.host.F)), (S' : Set _) = w.S₀ := ⟨_, rfl⟩
    have hex : ∀ i, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧
        (∀ z : ℂ, 1 < z.re → Λ z = eulerProd (above D.host.E w.S₀)
          (fun w => {val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := fun i => by
      by_cases hi : i ∈ Finset.Icc 1 k
      · have h := Finset.mem_Icc.1 hi
        have hu := hunr i (hmem i hi).1 (k + 1) (hmem i hi).2
        rw [← hS'] at hu ⊢
        obtain ⟨Λ, h1, h2, h3⟩ := quotL_entire_ne_zero_off c hw.com S' h.1 (by omega) (by omega) hu
        exact ⟨Λ, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose Λ hΛ using hex
    refine ⟨∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n, ?_,
      ⟨Λ, fun i hi => ⟨(hΛ i hi).1, (hΛ i hi).2.1⟩, rfl⟩⟩
    refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun n hn => ?_
    have := Finset.mem_Icc.1 hn
    exact (hΛ i hi).2.2 n this.1 this.2

end GlobalTheory.ChainTw.EulerAtTwist

example : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, (∀ H H₀, IsHval c (c.S : Set _) k H → IsHval c w.S₀ k H₀ → H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) ∧ ∃ H₀, H₀ ≠ 0 ∧ IsHval c w.S₀ k H₀ :=
  GlobalTheory.ChainTw.EulerAtTwist.restore_hval
