import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay

variable {D : D7}

def quotHeight (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : NNReal :=
  ⨅ γ : GQ V, height θ V ((γ : GA D V) * g)

def IsRapidDecay (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g : GA D V, ‖φ g‖ * (quotHeight θ V g : ℝ) ^ N ≤ C

end GlobalTheory.CuspDecay

namespace GlobalTheory.Published

def CuspRapidDecay : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (e : LieInf V → GA D V), IsExpFam θ V e →
      ∀ φ : GA D V → ℂ, IsAutFun V φ → IsSmoothInf V e φ → IsUnifModerate θ V e φ → IsCuspFun V φ →
        GlobalTheory.CuspDecay.IsRapidDecay θ V φ

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_le (g : GA D V) {γ : GA D V} (hγ : γ ∈ GQ V) : quotHeight θ V g ≤ height θ V (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : GQ V)

theorem one_le_quotHeight (g : GA D V) : 1 ≤ quotHeight θ V g :=
  le_ciInf fun _ => one_le_height θ V _

theorem exists_height_le (g : GA D V) : ∃ γ ∈ GQ V, height θ V (γ * g) ≤ 2 * quotHeight θ V g := by
  have h : quotHeight θ V g < 2 * quotHeight θ V g :=
    lt_mul_of_one_lt_left (zero_lt_one.trans_le (one_le_quotHeight g)) one_lt_two
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h
  exact ⟨γ, γ.2, hγ.le⟩

theorem IsRapidDecay.bounded {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem IsRapidDecay.mul_bounded {φ ψ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hψ : ∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) {N : ℕ} {C : ℝ} (hC : ∀ g, ‖ψ g‖ ≤ C * (height θ V g : ℝ) ^ N) :
    ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨C', hC'⟩ := h N
  refine ⟨|C| * 2 ^ N * C', fun g => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖ψ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N := by
    rw [← hψ γ hγ g]
    exact (hC _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))
  calc ‖ψ g‖ * ‖φ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N * ‖φ g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖φ g‖ * (quotHeight θ V g : ℝ) ^ N) := by rw [mul_pow]; ring
    _ ≤ |C| * 2 ^ N * C' := mul_le_mul_of_nonneg_left (hC' g) (by positivity)

theorem exists_norm_le_height_pow (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ g‖ ≤ C * (height θ V g : ℝ) ^ N := by
  obtain ⟨-, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨-, -, N, hN⟩ := h2 e he
  obtain ⟨C, hC⟩ := hN []
  exact ⟨N, C, hC⟩

theorem isRapidDecay_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : IsRapidDecay θ V φ := by
  obtain ⟨ha, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨hs, -, hg⟩ := h2 e he
  exact hP D θ hθ V e he φ ha hs hg hc

theorem bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C :=
  (isRapidDecay_of_cuspForm hP hθ h hc).bounded

theorem mul_bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {ψ φ : GA D V → ℂ}
    (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨N, C, hC⟩ := exists_norm_le_height_pow hθ hψ
  exact (isRapidDecay_of_cuspForm hP hθ h hc).mul_bounded hψ.left hC

theorem measure_lt_top (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  exact hV D.host.F D.host.E D.sp.cm.sig h1 V.rank V.gram (h2 V) μ hμ 𝓕 h𝓕

theorem integrableOn_star_mul (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hθ : IsInfFam θ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {ψ φ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IntegrableOn (fun g => star (ψ g) * φ g) 𝓕 μ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := mul_bounded_of_cuspForm hP hθ hψ h hc
  refine Measure.integrableOn_of_bounded (M := B) (measure_lt_top hV V μ 𝓕 hμ h𝓕).ne
    ((hψ.cont.star.mul h.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hB g

end GlobalTheory.CuspDecay

end
