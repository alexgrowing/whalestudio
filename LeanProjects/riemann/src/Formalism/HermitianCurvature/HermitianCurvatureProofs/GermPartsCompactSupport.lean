import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocalOfFibres
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocBOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNegBetaL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositivityBoundOfActual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBJoint

namespace Formalism.FourierDecayAlt.P.GermFibreKernels

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def GramRealiseAll : Prop :=
  ∀ (α : Type) (K : α → α → ℂ), (∀ Y : Finset α, TB.PSDOn Y K) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ x y, K x y = ⟪V x, V y⟫_ℂ

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def vOf (dl : ℝ) (Vec : C.LPt → H) (P : C.LPt) (c : ℂ) : H := (((√dl)⁻¹ : ℝ) : ℂ) • Vec (P ++ [(1, c)])

def btOf (s : ℕ) (dl : ℝ) (Vec : C.LPt → H) (h : C.LPt) (z : ℂ) : H :=
  if z = 0 then 0 else ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√dl)⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])

theorem vec_continuousOn {X : Type} [TopologicalSpace X] (k : C.LPt → C.LPt → ℂ) (Vec : C.LPt → H)
    (hV : ∀ P Q, k P Q = ⟪Vec P, Vec Q⟫_ℂ) (f : X → C.LPt) (U : Set X)
    (hk : ContinuousOn (fun cc : X × X => k (f cc.1) (f cc.2)) (U ×ˢ U)) :
    ContinuousOn (fun c => Vec (f c)) U := by
  intro c0 hc0
  have hq : ∀ c, ‖Vec (f c) - Vec (f c0)‖ ^ 2 =
      (k (f c) (f c) - k (f c) (f c0) - k (f c0) (f c) + k (f c0) (f c0)).re := by
    intro c
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right, hV, hV, hV, hV]
    rw [RCLike.re_to_complex]
    simp only [Complex.sub_re, Complex.add_re]
    ring
  have hpair : ∀ g1 g2 : X → X, ContinuousWithinAt g1 U c0 → ContinuousWithinAt g2 U c0 → (∀ c ∈ U, g1 c ∈ U) →
      (∀ c ∈ U, g2 c ∈ U) → ContinuousWithinAt (fun c => k (f (g1 c)) (f (g2 c))) U c0 := by
    intro g1 g2 h1 h2 hu1 hu2
    have hkk : ContinuousWithinAt (fun cc : X × X => k (f cc.1) (f cc.2)) (U ×ˢ U) (g1 c0, g2 c0) :=
      hk _ ⟨hu1 c0 hc0, hu2 c0 hc0⟩
    exact ContinuousWithinAt.comp (f := fun c => (g1 c, g2 c)) hkk (h1.prodMk h2) (fun c hc => ⟨hu1 c hc, hu2 c hc⟩)
  have hc1 := hpair id id continuousWithinAt_id continuousWithinAt_id (fun c h => h) (fun c h => h)
  have hc2 := hpair id (fun _ => c0) continuousWithinAt_id continuousWithinAt_const (fun c h => h) (fun _ _ => hc0)
  have hc3 := hpair (fun _ => c0) id continuousWithinAt_const continuousWithinAt_id (fun _ _ => hc0) (fun c h => h)
  have hQ : ContinuousWithinAt (fun c => (k (f c) (f c) - k (f c) (f c0) - k (f c0) (f c) + k (f c0) (f c0)).re)
      U c0 :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt
      (((hc1.sub hc2).sub hc3).add continuousWithinAt_const)
  have hs := (Real.continuous_sqrt.tendsto _).comp hQ.tendsto
  have h0 : (k (f c0) (f c0) - k (f c0) (f c0) - k (f c0) (f c0) + k (f c0) (f c0)).re = 0 := by simp
  rw [Function.comp_def, h0, Real.sqrt_zero] at hs
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine hs.congr (fun c => ?_)
  rw [← hq c, Real.sqrt_sq (norm_nonneg _)]

end vec

section vec2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_real_smul_smul (r : ℝ) (u w : H) :
    ⟪(r : ℂ) • u, (r : ℂ) • w⟫_ℂ = ((r * r : ℝ) : ℂ) * ⟪u, w⟫_ℂ := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
  push_cast; ring

theorem inv_sqrt_mul (d : ℝ) (hd : 0 < d) : (d : ℂ) * (((√d)⁻¹ * (√d)⁻¹ : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hd.le, mul_inv_cancel₀ hd.ne', Complex.ofReal_one]

theorem bz_btOf (s : ℕ) (hs : s ≠ 0) (dl : ℝ) (Vec : C.LPt → H) (h : C.LPt) (z : ℂ) (hz : z ≠ 0) :
    bz s (btOf s dl Vec h) z = (((√dl)⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)]) := by
  unfold bz btOf
  rw [if_neg hz, smul_smul, ← Complex.ofReal_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
  have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
  have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  positivity

end vec2

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def KerCont (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ i, i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ m, 1 ≤ m → ∀ P Q : C.LPt,
    D.ptSize P + m = i → D.ptSize Q + m = i →
    ContinuousOn (fun cc : ℂ × ℂ => KB.gN S v ε i a (P ++ [(m, cc.1)]) (Q ++ [(m, cc.2)])) ({0}ᶜ ×ˢ {0}ᶜ)

def GermRate (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

theorem measurableSet_ne_zero : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl

theorem fibres_of (hKol : GramRealiseAll) (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (hg1 : 0 < S.G.g1)
    (hg2 : 0 < S.G.g2) (hpos : C.ThmPPos S) (hK : KerCont S v) (hR : GermRate S v) :
    GermFibres S v ∧ GermCont S v := by
  have hg : 0 < S.g := by unfold C.HidaSetting.g; exact Nat.mul_pos hg1 hg2
  refine ⟨?_, ?_⟩
  swap
  · intro ε hε b s hb hs hbs a ha h h' hh hh'
    have := hK ε hε (b + s - 1) (by omega) a ha s (by omega) h h' (by rw [hh]; omega) (by rw [hh']; omega)
    show ContinuousOn (fun z : ℂ => KB.gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)])) {0}ᶜ
    exact ContinuousOn.comp
      (g := fun cc : ℂ × ℂ => KB.gN S v ε (b + s - 1) a (h ++ [(s, cc.1)]) (h' ++ [(s, cc.2)]))
      (f := fun z : ℂ => (z, z)) this (continuousOn_id.prodMk continuousOn_id) (fun z hz => ⟨hz, hz⟩)
  intro ε hε b s hb hs hbs a ha Y hY
  obtain ⟨w, hw⟩ := ha
  have hpsd : ∀ Y' : Finset C.LPt, TB.PSDOn Y' (KB.gN S v ε (b + s - 1) a) := by
    intro Y'; rw [← hw]; exact PBB.gN_psd S hpos v ε hε (b + s - 1) (by omega) w Y'
  obtain ⟨H, i1, i2, i3, Vec, hVec⟩ := hKol C.LPt (KB.gN S v ε (b + s - 1) a) hpsd
  let _ := i1; let _ := i2; have _ := i3
  have ha : D.AdmAt S v a := ⟨w, hw⟩
  set dl1 := KB.dlB S (b + s - 1) 1 with hdl1
  set dl2 := KB.dlB S b s with hdl2
  have hd1 : 0 < dl1 := PBC.dlB_pos S hg _ _
  have hd2 : 0 < dl2 := PBC.dlB_pos S hg _ _
  have hs0 : s ≠ 0 := by omega

  have hcont : ∀ m, 1 ≤ m → ∀ P : C.LPt, D.ptSize P + m = b + s - 1 →
      ContinuousOn (fun c : ℂ => Vec (P ++ [(m, c)])) {0}ᶜ := fun m hm P hP =>
    vec_continuousOn _ Vec hVec (fun c => P ++ [(m, c)]) {0}ᶜ (hK ε hε (b + s - 1) (by omega) a ha m hm P P hP hP)
  have hsz : ∀ h ∈ Y, ∀ x : ℂ, D.ptSize (ptX s h x) + 1 = b + s - 1 := by
    intro h hh x; rw [ptSize_ptX, hY h hh]; omega
  have hszs : ∀ h ∈ Y, D.ptSize h + s = b + s - 1 := by intro h hh; rw [hY h hh]; omega

  let g : C.LPt → ℂ → H := fun h z => ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√dl2)⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])
  have hgc : ∀ h ∈ Y, ContinuousOn (g h) {0}ᶜ := by
    intro h hh
    refine ContinuousOn.smul ?_ (hcont s (by omega) h (hszs h hh))
    refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ continuousOn_const)
    refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
    have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
    have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    positivity
  have hbt : ∀ h, btOf s dl2 Vec h = ({0}ᶜ : Set ℂ).piecewise (g h) (fun _ => 0) := by
    intro h; funext z
    by_cases hz : z = 0
    · simp [btOf, hz]
    · simp [btOf, hz, Set.piecewise, g]
  obtain ⟨ε', φ, hε'1, hφ1, hφc, hRr⟩ := hR ε hε b s hb hs hbs a ha H Vec hVec
  have hbzφ : ∀ h z, z ≠ 0 → bz s (fun z => φ z • btOf s dl2 Vec h z) z =
      φ z • ((((√dl2)⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])) := by
    intro h z hz
    rw [← bz_btOf s hs0 dl2 Vec h z hz]
    unfold bz; rw [smul_comm]
  refine ⟨{
    H := H
    V := vOf dl1 Vec
    bt := fun h z => φ z • btOf s dl2 Vec h z
    β := betaL S
    ε' := ε'
    hβ := betaL_ne_zero S hg1 hg2
    hε' := hε'1
    hpsi := fun σ z => psi_betaL S σ z
    measV := ?_
    fibre := ?_
    meas := ?_
    loc := ?_
    germ := ?_
    dens := ?_ }⟩
  ·
    intro h hh x hx
    have h1 : ContinuousOn (vOf dl1 Vec (ptX s h x)) {0}ᶜ :=
      continuousOn_const.smul (hcont 1 le_rfl (ptX s h x) (hsz h hh x))
    have h2 := h1.aestronglyMeasurable (μ := volume) measurableSet_ne_zero
    rwa [Measure.restrict_eq_self_of_ae_mem (by filter_upwards [GermRealisation.ae_ne_zero] with z hz using hz)] at h2
  ·
    intro h hh h' hh' x x' hx hx' c hc
    unfold vOf
    rw [inner_real_smul_smul, ← hVec, ← mul_assoc, inv_sqrt_mul dl1 hd1, one_mul]
  ·
    intro h hh
    letI : MeasurableSpace H := borel H
    haveI : BorelSpace H := ⟨rfl⟩
    have hbt' : (fun z => φ z • btOf s dl2 Vec h z) = ({0}ᶜ : Set ℂ).piecewise (fun z => φ z • g h z) (fun _ => 0) := by
      funext z; rw [hbt h]
      by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
      · simp only [Set.piecewise_eq_of_mem _ _ _ hz]
      · simp only [Set.piecewise_eq_of_notMem _ _ _ hz, smul_zero]
    have hgc' : ContinuousOn (fun z => φ z • g h z) {0}ᶜ := hφc.smul (hgc h hh)
    rw [stronglyMeasurable_iff_measurable_separable, hbt']
    refine ⟨ContinuousOn.measurable_piecewise hgc' continuousOn_const measurableSet_ne_zero, ?_⟩
    refine TopologicalSpace.IsSeparable.mono (s := (fun z => φ z • g h z) '' {0}ᶜ ∪ {0}) ?_
      (Set.range_subset_iff.2 fun z => ?_)
    · exact (hgc'.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)).union
        (Set.finite_singleton (0 : H)).isSeparable
    · by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
      · left; rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact ⟨z, hz, rfl⟩
      · right; rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl
  ·
    intro h hh K hKc hK0
    have hsub : K ⊆ {0}ᶜ := fun z hz hz0 => hK0 (by rw [Set.mem_singleton_iff.1 hz0] at hz; exact hz)
    have hc : ContinuousOn (fun z => ‖(((√dl2)⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])‖ ^ 2) K :=
      ((continuousOn_const.smul (hcont s (by omega) h (hszs h hh))).norm.pow 2).mono hsub
    refine (hc.congr fun z hz => ?_).integrableOn_compact hKc
    rw [hbzφ h z (fun h0 => hK0 (h0 ▸ hz)), norm_smul, hφ1, one_mul]
  ·
    intro h hh K hKc hK0
    obtain ⟨C, hC⟩ := hRr h (hY h hh) K hKc hK0
    exact ⟨C, fun x hx => Eventually.of_forall fun D hD => hC x hx D hD⟩
  ·
    intro h hh h' hh' z hz
    unfold gDens
    have hφφ : (starRingEnd ℂ) (φ z) * φ z = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hφ1]; simp
    rw [hbzφ h z hz, hbzφ h' z hz, inner_smul_left, inner_smul_right, ← mul_assoc ((starRingEnd ℂ) (φ z)), hφφ, one_mul,
      inner_real_smul_smul, ← hVec, ← mul_assoc, inv_sqrt_mul dl2 hd2, one_mul]

end loc

section hermitianSpaces

theorem cutSeq_cpt (Cb : ℝ) : ∃ c1 : ℝ, ∀ (Cc : ℝ), c1 ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v ε, 0 < ε → KB.CptCoef (p v).T.base (PBASM.cutSeq S p f χ n v ε) := by
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  refine ⟨c1, fun Cc le1 E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v ε hε => ?_⟩
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, -, -, -, -, hA, hv⟩ := hB
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop PBASM.cutN (by rw [hl0]; exact hInD)
    hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right le1 (by positivity)) (by positivity)

def KerContB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, KerCont (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

def GermRateB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRate (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

end hermitianSpaces

theorem germPartsC_of (hK : KerContB) (hR : GermRateB) : P5.ThmPActualCpt → PBASM.GermPartsC := by
  intro hA Cb
  have hKol : GramRealiseAll := fun α K hK => kolmogorov K hK
  obtain ⟨c1, h1⟩ := cutSeq_cpt Cb
  obtain ⟨c5, h5⟩ := positivity_bound hA Cb
  obtain ⟨c2, h2⟩ := hK Cb
  obtain ⟨c3, h3⟩ := hR hA Cb
  refine ⟨max (max c1 c5) (max c2 c3), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have le1 : c1 ≤ max (max c1 c5) (max c2 c3) := le_max_of_le_left (le_max_left _ _)
  have le5 : c5 ≤ max (max c1 c5) (max c2 c3) := le_max_of_le_left (le_max_right _ _)
  have le2 : c2 ≤ max (max c1 c5) (max c2 c3) := le_max_of_le_right (le_max_left _ _)
  have le3 : c3 ≤ max (max c1 c5) (max c2 c3) := le_max_of_le_right (le_max_right _ _)
  have hcpt := h1 _ le1 E Wp Wq S p f χ A₀ hB n
  have hpos := h5 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le5 hB) _ (fun v ε hε => hcpt v ε hε)
  exact fibres_of hKol _ v hB.1 hB.2.1 hpos (h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le2 hB) n v)
    (h3 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le3 hB) n v)

end

end Formalism.FourierDecayAlt.P.GermFibreKernels

theorem Formalism.FourierDecayAlt.P.germ_parts_compact_support :
    Formalism.FourierDecayAlt.P.GermFibreKernels.KerContB → Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB → Formalism.FourierDecayAlt.P5.ThmPActualCpt → Formalism.FourierDecayAlt.P.PBASM.GermPartsC :=
  Formalism.FourierDecayAlt.P.GermFibreKernels.germPartsC_of
