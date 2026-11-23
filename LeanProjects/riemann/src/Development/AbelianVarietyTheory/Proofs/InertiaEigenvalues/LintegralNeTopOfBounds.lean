import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.EisAbsPf

abbrev LA : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∃ (M : ℕ) (C : ℝ), ∀ g₁ g₂ : GA D W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ≤ ENNReal.ofReal (C * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₁ : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₂ : ℝ)) ^ M)

abbrev LB : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ

theorem lintegral_ne_top_of_bounds {X : Type*} [MeasurableSpace X] [Mul X] (ν : Measure X) (𝓖 : Set X)
    (hfin : ν 𝓖 < ⊤) (Γ : Set X) (h q : X → ℝ) (hq : ∀ g, 0 ≤ q g)
    (htr : ∀ g, ∃ γ ∈ Γ, h (γ * g) ≤ 2 * q g) (hh : ∀ g, 0 ≤ h g)
    (S : X → X → ENNReal) (hinv : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, ∀ g₁ g₂, S (γ₁ * g₁) (γ₂ * g₂) = S g₁ g₂)
    (M : ℕ) (C : ℝ) (hC : ∀ g₁ g₂, S g₁ g₂ ≤ ENNReal.ofReal (C * (h g₁ * h g₂) ^ M))
    (a b : X → ℂ) (C₁ C₂ : ℝ) (hC₁ : ∀ g, ‖a g‖ * q g ^ M ≤ C₁) (hC₂ : ∀ g, ‖b g‖ * q g ^ M ≤ C₂) :
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ := by
  have hpt : ∀ g₁ g₂, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
    intro g₁ g₂
    obtain ⟨γ₁, hγ₁, e1⟩ := htr g₁
    obtain ⟨γ₂, hγ₂, e2⟩ := htr g₂
    have hq₁ := hq g₁
    have hq₂ := hq g₂
    have hS1 : S g₁ g₂ ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) := by
      rw [← hinv γ₁ hγ₁ γ₂ hγ₂ g₁ g₂]
      refine (hC _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hh' : h (γ₁ * g₁) * h (γ₂ * g₂) ≤ (2 * q g₁) * (2 * q g₂) :=
        mul_le_mul e1 e2 (hh _) (by linarith)
      calc C * (h (γ₁ * g₁) * h (γ₂ * g₂)) ^ M
          ≤ |C| * ((2 * q g₁) * (2 * q g₂)) ^ M :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg (hh _) (hh _)) hh' M) (pow_nonneg (mul_nonneg (hh _) (hh _)) M)
              (abs_nonneg _)
        _ = |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := by
            rw [show (2 * q g₁) * (2 * q g₂) = 4 * (q g₁ * q g₂) by ring, mul_pow, mul_pow]; ring
    have hn1 : ‖a g₁‖ₑ = ENNReal.ofReal ‖a g₁‖ := (ofReal_norm_eq_enorm _).symm
    have hn2 : ‖b g₂‖ₑ = ENNReal.ofReal ‖b g₂‖ := (ofReal_norm_eq_enorm _).symm
    have a1 := hC₁ g₁
    have a2 := hC₂ g₂
    have p1 : 0 ≤ ‖a g₁‖ * q g₁ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₁ M)
    have p2 : 0 ≤ ‖b g₂‖ * q g₂ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₂ M)
    have c0 : 0 ≤ |C| * 4 ^ M := by positivity
    calc S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ
        ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) * ENNReal.ofReal ‖a g₁‖ * ENNReal.ofReal ‖b g₂‖ := by
          rw [hn1, hn2]; gcongr
      _ = ENNReal.ofReal (|C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)) := by
          have c1 : 0 ≤ |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := mul_nonneg c0 (mul_nonneg (pow_nonneg hq₁ M) (pow_nonneg hq₂ M))
          rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_mul (mul_nonneg c1 (norm_nonneg _))]
          congr 1; ring
      _ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc |C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)
              ≤ |C| * 4 ^ M * C₁ * (‖b g₂‖ * q g₂ ^ M) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 c0) p2
            _ ≤ |C| * 4 ^ M * C₁ * C₂ :=
                mul_le_mul_of_nonneg_left a2 (mul_nonneg c0 (p1.trans a1))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖) ?_ ?_
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hfin.ne
  · calc ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν
        ≤ ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) ∂ν ∂ν :=
          lintegral_mono fun g₁ => lintegral_mono fun g₂ => hpt g₁ g₂
      _ = ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖 := by
          rw [setLIntegral_const, setLIntegral_const]

theorem eisAbs_of_bounds (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hA : LA) (hB : LB) :
    ∀ D : D7, EisAbs D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2
  obtain ⟨M, C, hC⟩ := hA D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2
  have e : ∀ γ g : GA D W, om (1, γ * g) = om (1, γ) * om (1, g) := by
    intro γ g; rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hinv : ∀ γ₁ ∈ (GQ W : Set (GA D W)), ∀ γ₂ ∈ (GQ W : Set (GA D W)), ∀ g₁ g₂ : GA D W,
      (∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁ * g₁) f₁) (om (1, γ₂ * g₂) f₂)‖ₑ) =
        ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ := by
    intro γ₁ hγ₁ γ₂ hγ₂ g₁ g₂
    rw [e γ₁ g₁, e γ₂ g₂, Module.End.mul_apply, Module.End.mul_apply]
    exact hB D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ (hS.weil.om_pres _ _ h1) (hS.weil.om_pres _ _ h2)
      γ₁ hγ₁ γ₂ hγ₂
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA1 hC1 M
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA2 hC2 M
  have hfin : νW 𝓖 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV W νW 𝓖 hS.haarW hS.fdW
  have key := lintegral_ne_top_of_bounds νW 𝓖 hfin (GQ W : Set (GA D W))
    (fun g => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g : ℝ)) (fun g => (GlobalTheory.CuspDecay.quotHeight θ W g : ℝ))
    (fun g => NNReal.coe_nonneg _)
    (fun g => by
      obtain ⟨γ, hγ, hle⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
      exact ⟨γ, hγ, by exact_mod_cast hle⟩)
    (fun g => NNReal.coe_nonneg _)
    (fun g₁ g₂ => ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ) hinv M C hC φ₁ φ₂ C₁ C₂ hC₁ hC₂
  refine ne_top_of_le_ne_top key (le_of_eq ?_)
  refine lintegral_congr fun g₁ => lintegral_congr fun g₂ => ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

theorem eisAbs : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, EisAbs D :=
  fun hP => eisAbs_of_bounds hP GlobalTheory.Mem.VolFin.finVol GlobalTheory.T.siegelWeilLagrangianTerms_abs_tsum_le_heightPoly GlobalTheory.T.siegelWeil_tsum_enorm_rational_invariant

end GlobalTheory.EisAbsPf

end
