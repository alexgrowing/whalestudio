import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisPoleLEZeroOfLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups

noncomputable section

open scoped Matrix NNReal Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.PolesModel

open GlobalTheory.StdUnn GlobalTheory.StdUnn.HeightExists GlobalTheory.Eis

variable {D : D7} {n : ℕ}

def detP : P D n →* (AE D)ˣ := Matrix.GeneralLinearGroup.det.comp leviBlock

def modP : P D n →* ℝ≥0 := (absA D).comp detP

theorem continuous_modP : Continuous (modP (D := D) (n := n)) :=
  continuous_absE.comp (continuous_detGL.comp continuous_leviBlock)

theorem isIwasawa : IsIwasawa (modP (D := D) (n := n)) (K D n) :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  isIwasawa_of_isCompact isClosed_P continuous_modP isCompact_K fun g =>
    let ⟨p, hp, k, hk, e⟩ := Iwasawa.exists_mul D n g; ⟨⟨p, hp⟩, k, hk, e⟩

theorem height_eq {H : G D n → ℝ≥0} (h : IsHeight H) : H = iwAbs modP (K D n) := funext fun g => by
  obtain ⟨p, k, hk, rfl⟩ := isIwasawa.1 g
  rw [isIwasawa.iwAbs_mul p hk]
  exact h p p.2 (leviBlock (D := D) (n := n) p) rfl k hk

theorem isSection_iff {χ : (AE D)ˣ →* Circle} {s : ℂ} {φ : G D n → ℂ} :
    IsSection χ s φ ↔ φ ∈ indSpace modP (K D n) (χ.comp detP) (s + (n : ℂ) / 2) := by
  refine and_congr_left fun _ => ⟨fun h p g => h p p.2 (leviBlock (D := D) (n := n) p) rfl g, fun h p hp a ha g => ?_⟩
  rw [show a = leviBlock (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact h ⟨p, hp⟩ g

theorem isSection_stdSec {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (h : IsHeight H) {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s₁ φ) (s : ℂ) : IsSection χ s (stdSec H φ s₁ s) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  rw [height_eq h, isSection_iff]
  exact isIwasawa.flatSec_mem isClosed_P continuous_modP isCompact_K (isSection_iff.1 hφ) s

theorem stdSec_of_mem {H : G D n → ℝ≥0} (h : IsHeight H) (φ : G D n → ℂ) (s₁ s : ℂ) {k : G D n} (hk : k ∈ K D n) :
    stdSec H φ s₁ s k = φ k := by
  rw [height_eq h]; exact isIwasawa.flatSec_of_mem φ s₁ s hk

theorem leftInv_of_isSection {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {s : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s φ) : LeftInv (P D n ⊓ GF D n) φ := fun γ hγ g => by
  obtain ⟨u, hu⟩ := LeftInvSect.det_rat hγ.2 (leviBlock (D := D) (n := n) ⟨γ, hγ.1⟩) rfl
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hφ.1 γ hγ.1 (leviBlock (D := D) (n := n) ⟨γ, hγ.1⟩) rfl g, hu, hχ.2 u, h1]
  simp

theorem hypotheses_hold (D : D7) (n k : ℕ) (s₁ : ℂ) : ∃ (H : G D n → ℝ≥0) (φ : G D n → ℂ),
    IsHeckeChar D 1 ∧ ResEta D 1 (2 * k) ∧ IsHeight H ∧ IsSection 1 s₁ φ ∧ ∀ g, φ g ≠ 0 := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  obtain ⟨H, hH⟩ := exists_height D n
  refine ⟨H, fun g => npow (iwAbs modP (K D n) g) (s₁ + (n : ℂ) / 2), ⟨continuous_const, fun _ => rfl⟩,
    SimplePoleModel.resEta_one_two_mul D k, hH, isSection_iff.2 ?_, fun g => npow_ne_zero (iwAbs_pos _ _ g) _⟩
  exact isIwasawa.npow_iwAbs_mem isClosed_P continuous_modP isCompact_K _

theorem summable_of_rank (A : HSp D) (τ : ℝ) (hτ : (A.rank : ℝ) / 2 < τ) : Summable fun q =>
    ((term (P D A.rank) (GF D A.rank) (iwAbs modP (K D A.rank)) 1 q : ℝ≥0) : ℝ) ^ (τ + (A.rank : ℝ) / 2) := by
  obtain ⟨μ, hμ, hconj⟩ := ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨p, hp⟩ := hconj A a ha κ hκ
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hf := ((sphConv_iff hI).1 (sphConv D A a hI)).1 τ hτ
  have hH := height_eq (isHeight_hgtStd D A μ hμ κ hκ a p hp)
  have := (cosetSum_along_mulEquiv _ _ κ.symm (P D A.rank) (GF D A.rank) (siegel A) (GQ (dblSp A))
    (fun g => by rw [mem_siegel_iff_chart_mem_P D A μ hμ κ hκ, MulEquiv.apply_symm_apply])
    (fun g => by rw [chart_mem_GF_iff D A μ hμ κ hκ, MulEquiv.apply_symm_apply])
    (sph A a τ) (κ (p : GA D (dblSp A))⁻¹) (npow (absA D (aP A p)) (τ + (A.rank : ℂ) / 2))
    (fun g => npow (hgtStd A a κ p g) (τ + (A.rank : ℂ) / 2))
    (fun g => by rw [hgtStd, npow_mul, map_mul, MulEquiv.symm_apply_apply, sph, mul_comm]) hf.1).2 1
  refine (this.1 (hf.2 _)).congr fun q => ?_
  simp only [term, hH]
  rw [norm_npow (iwAbs_pos _ _ _)]
  simp

theorem summable_spherical (τ : ℝ) (hτ : (n : ℝ) / 2 < τ) : Summable fun q =>
    ((term (P D n) (GF D n) (iwAbs modP (K D n)) 1 q : ℝ≥0) : ℝ) ^ (τ + (n : ℝ) / 2) :=
  summable_of_rank (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n) τ hτ

theorem cosetConv_stdSec {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (h : IsHeight H) {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s₁ φ) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (g : G D n) :
    CosetConv (P D n) (GF D n) (stdSec H φ s₁ s) g := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (iwAbs modP (K D n)) := isIwasawa.continuous_iwAbs isClosed_P continuous_modP isCompact_K
  have h2 : Continuous fun g => Real.log (iwAbs modP (K D n) g) :=
    (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
  refine cosetConv_of_spherical (χ := χ.comp detP) (ρ := (n : ℝ) / 2) isIwasawa isCompact_K (Continuous.continuousOn ?_)
    (fun z _ => ?_) summable_spherical hs g
  · simp only [stdSec, height_eq h, npow_eq_exp (iwAbs_pos _ _ _)]
    exact (hφ.2.1.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
      (continuous_fst.sub continuous_const)).cexp)
  · have := (isSection_iff.1 (isSection_stdSec h hφ z)).1
    push_cast
    exact this

theorem poleLE_zero {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (h : IsHeight H) {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s₁ φ) {s₀ : ℂ} (hs : (n : ℝ) / 2 < s₀.re) (g : G D n) :
    PoleLE (fun s => cosetSum (P D n) (GF D n) (stdSec H φ s₁ s) g) s₀ 0 := by
  have ha : AnalyticOnNhd ℂ (fun s => cosetSum (P D n) (GF D n) (stdSec H φ s₁ s) g) (rightOf ((n : ℝ) / 2)) :=
    analyticOnNhd_tsum_npow (f := term _ _ φ g) (a := term _ _ H g) (fun _ => by rw [height_eq h]; exact iwAbs_pos _ _ _)
      fun s hs => cosetConv_stdSec h hφ hs g
  exact ⟨_, ⟨_, hs, isRightDomain_rightOf _, ha.meromorphicOn, 0, fun _ _ => rfl⟩,
    by simpa using (ha s₀ hs).meromorphicOrderAt_nonneg⟩

theorem polesStd_iff : Published.SiegelEisensteinPolesStd ↔
    ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D χ → ResEta D χ b →
    ∀ H : G D n → ℝ≥0, IsHeight H → ∀ (s₁ : ℂ) (φ : G D n → ℂ), IsSection χ s₁ φ →
    ∀ s₀ : ℂ, 0 < s₀.re → s₀.re ≤ (n : ℝ) / 2 → ∀ g,
      PoleLE (fun s => cosetSum (P D n) (GF D n) (stdSec H φ s₁ s) g) s₀ 1 := by
  refine ⟨fun h D n χ b h1 h2 H h3 s₁ φ h4 s₀ h5 h6 => h D n ?_ χ b h1 h2 H h3 s₁ φ h4 s₀ h5,
    fun h D n _ χ b h1 h2 H h3 s₁ φ h4 s₀ h5 g => ?_⟩
  · have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  · rcases le_or_gt s₀.re ((n : ℝ) / 2) with e | e
    · exact h D n χ b h1 h2 H h3 s₁ φ h4 s₀ h5 e g
    · exact SimplePoleModel.poleLE_succ (poleLE_zero h3 h4 e g)

end GlobalTheory.StdUnn.PolesModel

end
