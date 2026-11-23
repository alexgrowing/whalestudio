import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelA
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set GlobalTheory.Eis GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

variable {D : D7} {n : ℕ}

theorem law_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  simp only [fam]
  rw [hH.2.2 q hq a ha g, h q hq a ha g, npow_mul]
  have e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) := by
    rw [← npow_add (hom_pos _ _)]; congr 1; ring
  rw [e]; ring

theorem cont_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  simp only [fam, npow_eq_exp (hH.2.1 _)]
  have h1 : Continuous fun u : ℂ × G D n => Real.log (H u.2 : ℝ) :=
    (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)).log fun u => (NNReal.coe_pos.2 (hH.2.1 _)).ne'
  exact (((Complex.continuous_ofReal.comp h1).mul (continuous_fst.sub continuous_const)).cexp).mul
    (hφ.comp continuous_snd)

def cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : Set (G D n) :=
  ⋃ x ∈ C.s, (fun k => g * k * nb x) '' (K D n : Set (G D n))

theorem isCompact_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : IsCompact (cset nb C g) :=
  C.s.isCompact_biUnion fun _ _ => isCompact_K.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) (u : KAt D n v) {x : hermA D n}
    (hx : x ∈ C.s) : g * (u : G D n) * nb x ∈ cset nb C g :=
  mem_biUnion hx ⟨u, (Subgroup.mem_inf.1 u.2).1, rfl⟩

theorem farRight {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g)
    {z : ℂ} (hz : (n : ℝ) / 2 < z.re) (g : G D n) :
    ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv = c z * eisS (fam H φ s₀ z) g := by
  have := t2Space_adeleRing' (F := D.host.F)
  have hcont := cont_fam hH hφc s₀
  have hz' : Continuous (fam H φ s₀ z) := hcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨w, hw, hwb⟩ := exists_majorant (P := P D n) (Γ := GF D n) (χ := χ.comp detP) (ρ := (n : ℝ) / 2)
    (σ := (n : ℝ) / 2) (Φ := fam H φ s₀) isIwasawa isCompact_K hcont.continuousOn
    (fun s _ q g => by
      have := law_fam hH hφl s q q.2 (leviBlock (D := D) (n := n) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ hτ) isCompact_singleton (singleton_subset_iff.2 hz) (isCompact_cset nb C g)
  have hb : ∀ q (u : KAt D n v) x, x ∈ C.s →
      ‖fam H φ s₀ z (((q.out : GF D n) : G D n) * g * u * nb x)‖ ≤ w q := fun q u x hx => by
    have := hwb q z rfl _ (mem_cset nb C g u hx)
    simpa only [term, mul_assoc] using this
  have hterm : ∀ u : KAt D n v, cutR nb C (eisS (fam H φ s₀ z)) (g * u) =
      ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) := by
    intro u
    simp only [cutR, eisS, cosetSum]
    rw [Summable.tsum_finsetSum fun x hx => (Summable.of_norm_bounded hw fun q => by
      simpa only [term, mul_assoc] using hwb q z rfl _ (mem_cset nb C g u hx)).mul_left (C.co x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← tsum_mul_left]
    simp only [term, mul_assoc]
  calc ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv
      = ∫ u, ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        congr 1; funext u; exact hterm u
    _ = ∑' q : Cosets (P D n) (GF D n), ∫ u, cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        refine integral_tsum_dom νv _ (fun q => (∑ x ∈ C.s, ‖C.co x‖) * w q) (hw.mul_left _) (fun q u => ?_)
          fun q => ?_
        · simp only [cutR]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun x hx => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hb q u x hx) (norm_nonneg _)
        · refine Continuous.aestronglyMeasurable ?_
          simp only [cutR]
          exact continuous_finsetSum _ fun x _ => continuous_const.mul
            (hz'.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    _ = ∑' q : Cosets (P D n) (GF D n), c z * fam H φ s₀ z (((q.out : GF D n) : G D n) * g) := by
        congr 1; funext q; exact hrel z _
    _ = c z * eisS (fam H φ s₀ z) g := by
        rw [tsum_mul_left]; rfl

end PositivityTheory.Rg.Rsw.L.LCfRel

end
