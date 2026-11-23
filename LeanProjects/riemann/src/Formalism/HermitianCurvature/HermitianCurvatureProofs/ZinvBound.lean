import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordLengthLe

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section ube

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def UBL (f : Mat k r → E) (S : Set (Mat k r)) (n e γ : ℕ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ UB f S n C e γ) ∧ LSS f S

lemma ubl_mono {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n e γ e' γ' : ℕ}
    (h : UBL f S n e γ) (he : e ≤ e') (hγ : γ ≤ γ') : UBL f S n e' γ' := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_mono hSG hub hC he hγ⟩, hl⟩

lemma ubl_const (c : E) {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (n γ : ℕ) : UBL (fun _ : Mat k r => c) S n 0 γ := by
  exact ⟨⟨‖c‖, norm_nonneg _, ub_const c S hSG n γ⟩, lss_of_contDiff contDiff_const S⟩

lemma ubl_clm {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n e γ : ℕ} (h : UBL f S n e γ) : UBL (fun g => L (f g)) S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ub_clm L hSG hl hub⟩, lss_clm L hl⟩

lemma ubl_app {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} {n ea eb γ : ℕ} (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) :
    UBL (fun g => a g (b g)) S n (ea + eb) γ := by
  obtain ⟨⟨Ca, hCa, hua⟩, hla⟩ := ha
  obtain ⟨⟨Cb, hCb, hub⟩, hlb⟩ := hb
  exact ⟨⟨2 ^ n * (Ca * Cb), by positivity, ub_app hSG hla hlb hCa hCb hua hub⟩, lss_app hla hlb⟩

lemma ubl_congr {f f₂ : Mat k r → E} {S V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V) (hSG : S ⊆ GV k r)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n e γ : ℕ} (h : UBL f₂ S n e γ) : UBL f S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_congr hV hSV hSG he hub⟩, lss_congr hV hSV he hl⟩

lemma ubl_sub {f : Mat k r → E} {S S' : Set (Mat k r)} (hS : S' ⊆ S) {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL f S' n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, fun w hw g hg => hub w hw g (hS hg)⟩, lss_mono hl hS⟩

end ube

lemma ubl_mul {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a b : Mat k r → ℂ} {n ea eb γ : ℕ}
    (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) : UBL (fun g => a g * b g) S n (ea + eb) γ := by
  have ha' : UBL (fun g => ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ) (a g)) S n ea γ :=
    ubl_clm _ hSG ha
  have h := ubl_app hSG ha' hb
  convert h using 2
  simp

lemma ubl_prod {ι : Type*} [DecidableEq ι] {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n γ : ℕ} (s : Finset ι)
    (f : ι → Mat k r → ℂ) (h : ∀ i ∈ s, UBL (f i) S n 0 γ) : UBL (fun g => ∏ i ∈ s, f i g) S n 0 γ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ubl_const 1 hSG n γ
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have h1 := ubl_mul hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

lemma ubl_poly {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n γ : ℕ) :
    UBL P S n d γ := by
  obtain ⟨hcd, C, hC, hb⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff hcd S⟩
  refine le_trans (hb w hw g (hSG hg)) (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ (gN_ge_one (hSG hg)) (Nat.le_add_right _ _)

lemma poly_H {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) (n : ℕ) :
    ∃ M : ℝ, ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ M * gN g ^ (d * w.length) := by
  obtain ⟨-, C, hC, hb⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  refine ⟨C, fun w hw hne g hg => le_trans (hb w hw g hg) (mul_le_mul_of_nonneg_left ?_ hC)⟩
  have hl : 1 ≤ w.length := List.length_pos_iff.2 hne
  exact pow_le_pow_right₀ (gN_ge_one hg) (Nat.le_mul_of_pos_right d hl)

lemma ubl_fdb {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (K : Set F)
    (hK : ∀ g ∈ S, ψ g ∈ K) (α n : ℕ) (M : ℝ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w ψ g‖ ≤ M * gN g ^ (α * w.length))
    (Φ : F → E) (hΦ : ContDiff ℝ ∞ Φ) (hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) :
    UBL (fun g => Φ (ψ g)) S n 0 α := by
  obtain ⟨C, hC, hb⟩ := fdb ψ hψ S K hK gN (fun g hg => gN_ge_one (hSG hg)) α 0 M n
    (fun w hw hne g hg => by simpa using H w hw hne g (hSG hg)) n E Φ hΦ hB
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff (hΦ.comp hψ) S⟩
  have hlen : w.length ≤ n := by
    obtain ⟨u, v, -, -, hl, rfl⟩ := hw
    simpa [wL, wR] using hl
  simpa using hb w hw hlen g hg

lemma normSq_cd : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have h : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 :=
    funext fun z => Complex.normSq_eq_norm_sq z
  rw [h]
  exact contDiff_norm_sq ℝ

def zinv (c : ℝ) (m : ℕ) (z : ℂ) : ℂ := (sc c (Complex.normSq z) : ℂ) * z⁻¹ ^ m

lemma zinv_cd {c : ℝ} (hc : 0 < c) (m : ℕ) : ContDiff ℝ ∞ (zinv c m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · have hev : zinv c m =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {w : ℂ | Complex.normSq w < c / 4} :=
        isOpen_lt normSq_cd.continuous continuous_const
      have hmem : z ∈ {w : ℂ | Complex.normSq w < c / 4} := by
        show Complex.normSq z < c / 4
        rw [hz, map_zero]
        positivity
      filter_upwards [hopen.mem_nhds hmem] with w hw
      unfold zinv
      rw [sc_zero hc (le_of_lt hw)]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · unfold zinv
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ((sc c (Complex.normSq w) : ℝ) : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.comp ((sc_cd c).comp normSq_cd)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => w⁻¹ ^ m) z :=
      ((contDiffAt_inv ℂ hz).pow m).restrict_scalars ℝ
    exact h1.mul h2

lemma zinv_eq {c : ℝ} (hc : 0 < c) (m : ℕ) {z : ℂ} (hz : c / 2 ≤ Complex.normSq z) : zinv c m z = z⁻¹ ^ m := by
  unfold zinv
  rw [sc_one hc hz]
  simp

lemma zinv_bound {c : ℝ} (hc : 0 < c) (m j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | c ≤ Complex.normSq z}, ‖iteratedFDeriv ℝ j (zinv c m) z‖ ≤ B := by
  refine ⟨‖∏ i ∈ Finset.range j, ((((-(m : ℤ)) : ℤ) : ℂ) - (i : ℂ))‖ * (Real.sqrt c)⁻¹ ^ (m + j),
    fun z hz => ?_⟩
  have hz' : c ≤ Complex.normSq z := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz'
    linarith
  have hev : zinv c m =ᶠ[𝓝 z] fun w : ℂ => w⁻¹ ^ m := by
    have hopen : IsOpen {w : ℂ | c / 2 < Complex.normSq w} :=
      isOpen_lt continuous_const normSq_cd.continuous
    have hmem : z ∈ {w : ℂ | c / 2 < Complex.normSq w} := by
      show c / 2 < Complex.normSq z
      linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact zinv_eq hc m (le_of_lt hw)
  have hcd : ContDiffAt ℂ ∞ (zinv c m) z :=
    ((contDiffAt_inv ℂ hz0).pow m).congr_of_eventuallyEq hev
  have hR : ‖iteratedFDeriv ℝ j (zinv c m) z‖ = ‖iteratedFDeriv ℂ j (zinv c m) z‖ := by
    rw [← (contDiffAt_infty.1 hcd j).restrictScalars_iteratedFDeriv, Function.comp_apply,
      ContinuousMultilinearMap.norm_restrictScalars]
  have hfz : (fun w : ℂ => w⁻¹ ^ m) = fun w : ℂ => w ^ (-(m : ℤ)) := by
    funext w
    rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  rw [hR, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hev.iteratedDeriv_eq, hfz, iteratedDeriv_eq_iterate,
    iter_deriv_zpow, norm_mul, norm_zpow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hzn : Real.sqrt c ≤ ‖z‖ := by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt hz'
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [show (-(m : ℤ) - (j : ℤ)) = -((m + j : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) (inv_anti₀ hsc hzn) _

lemma ubl_invpow {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c : ℝ} (hc : 0 < c) (hS : ∀ g ∈ S, c ≤ Complex.normSq (P g)) (m n : ℕ) :
    UBL (fun g => (P g)⁻¹ ^ m) S n 0 d := by
  obtain ⟨hPc, -⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hV : IsOpen {g : Mat k r | c / 2 < Complex.normSq (P g)} :=
    isOpen_lt continuous_const (normSq_cd.continuous.comp hPc.continuous)
  have hSV : S ⊆ {g : Mat k r | c / 2 < Complex.normSq (P g)} := fun g hg => by
    show c / 2 < Complex.normSq (P g)
    linarith [hS g hg]
  refine ubl_congr hV hSV hSG (f₂ := fun g => zinv c m (P g)) (fun g _ hgV => (zinv_eq hc m (le_of_lt hgV)).symm) ?_
  exact ubl_fdb P hPc S hSG {z : ℂ | c ≤ Complex.normSq z} hS d n M hM (zinv c m) (zinv_cd hc m)
    (fun j => zinv_bound hc m j)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
