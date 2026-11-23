import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IsCompactKSet
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ParamCD
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mul_M2 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.1 * p.2) := by
  refine contDiff_of_entries fun a b => ?_
  have : (fun p : M2 n × M2 n => (p.1 * p.2) a b) = fun p => ∑ c, p.1 a c * p.2 c b := by
    funext p; rfl
  rw [this]
  exact ContDiff.sum fun c _ => ((contDiff_entry a c).comp contDiff_fst).mul ((contDiff_entry c b).comp contDiff_snd)

theorem tw_contDiff (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (tw m e μK β) := by
  have hk : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) (univ ×ˢ univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.2 * p.1) := contDiff_mul_M2.comp (contDiff_snd.prodMk contDiff_fst)
    exact (Complex.ofRealCLM.contDiff.comp (hβ.comp h1)).contDiffOn
  have hv : Continuous (fun k : KR n => (mR (k : GR n))ᴴ) := continuous_kR.matrix_conjTranspose
  have hh : Continuous (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀ fun k => Vac.spherical_section_ne_zero detU1 m 0 e _
  have := PCD.contDiffOn_integral' (F := M2 n) (X := KR n) isOpen_univ μK
    (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) hk (fun k : KR n => (mR (k : GR n))ᴴ) hv
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) hh
    (fun x _ => ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ u hu => absurd (mem_univ u) hu⟩)
  rw [contDiffOn_univ] at this
  have e' : tw m e μK β = fun X => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ • ((β ((mR (k : GR n))ᴴ * X) : ℝ) : ℂ) ∂μK := by
    funext X; rfl
  rw [e']
  exact this

def kk (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (p : M2 n × M2 n) : ℂ := tw m e μK β (p.1⁻¹ * p.2)

theorem kk_contDiffOn (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiffOn ℝ ∞ (kk m e μK β) (Inv n ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => (p.1⁻¹, p.2)) (Inv n ×ˢ univ) :=
    (contDiffOn_inv.comp contDiffOn_fst fun p hp => hp.1).prodMk contDiffOn_snd
  exact (tw_contDiff m e μK hβ).comp_contDiffOn (contDiff_mul_M2.comp_contDiffOn h1)

theorem kk_supp (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβs : HasCompactSupport β) :
    ∀ x ∈ Inv n, ∃ W ∈ 𝓝 x, ∃ C : Set (GR n), IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, kk m e μK β (x', mR u) = 0 := by
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp isOpen_Inv x hx
  have hFD : FiniteDimensional ℝ (M2 n) := inferInstanceAs (FiniteDimensional ℝ (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  have hPS : ProperSpace (M2 n) := FiniteDimensional.proper ℝ (M2 n)
  set B := Metric.closedBall x (r / 2)
  have hB : IsCompact B := isCompact_closedBall x (r / 2)
  have hBI : B ⊆ Inv n := fun y hy => hrs (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (half_lt_self hr))
  set T := (fun p : M2 n × M2 n => p.1 * p.2) '' (B ×ˢ kSet (tsupport β))
  have hT : IsCompact T := (hB.prod (isCompact_kSet hβs)).image contDiff_mul_M2.continuous
  refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (half_pos hr), (mR : GR n → M2 n) ⁻¹' T,
    isCompact_preimage_mR hT, fun x' hx' u hu => ?_⟩
  unfold kk
  refine tw_eq_zero m e μK β fun hmem => hu ?_
  refine ⟨(x', x'⁻¹ * mR u), ⟨hx', hmem⟩, ?_⟩
  show x' * (x'⁻¹ * mR u) = mR u
  have hdet : IsUnit x'.det := isUnit_iff_ne_zero.mpr (hBI hx')
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
