import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HandHom
variable {D : D7}

theorem mixS_smul {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (T : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (a : ℂ) (f : WO V T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (a • f) x = a • d.mixS T ψ μ 𝓕 f x := by
  funext w₀
  simp only [HypDec.mixS, Pi.smul_apply, smul_eq_mul, HypDec.integrandS_eq]
  rw [← integral_const_mul]
  congr 1; funext a'; ring

theorem mixT_smul {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (a : ℂ) (f : WO S W → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (a • f) y = a • d.mixT S ψ μ 𝓕 f y := by
  funext w₀
  simp only [HypDec.mixT, Pi.smul_apply, smul_eq_mul, HypDec.integrandT_eq]
  rw [← integral_const_mul]
  congr 1; funext a'; ring

theorem flatAt_smul (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ)) (μT : Measure (Mx D σ V₀.rank))
    (𝓕T : Set (Mx D σ V₀.rank)) (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ)
    (Ψ : WO V W → ℂ) :
    GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y (a • Ψ) = a • GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y Ψ := by
  funext w
  simp only [GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt, mixS_smul, mixT_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem flatBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (a : ℂ) (Ψ : WO B.V J.W → ℂ) :
    flatBF s (a • Ψ) = a • flatBF s Ψ := by
  simp only [GlobalTheory.Unf.flatBF, GlobalTheory.MixPer.flat, flatAt_smul]

theorem flatFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (a : ℂ) (Ψ : WO J.W B.V → ℂ) :
    flatFB s (a • Ψ) = a • flatFB s Ψ := by
  simp only [GlobalTheory.Unf.flatFB, GlobalTheory.MixPer.flatLast, flatAt_smul]

theorem handBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (φ : GA D B.A → ℂ) (a : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) :
    handBF s l φ (a • Ξ) = star a • handBF s l φ Ξ := by
  funext h w
  simp only [GlobalTheory.Unf.handBF, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (φ _) a]
  rw [integral_const_mul, star_mul']

theorem handBF_zero {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (φ : GA D B.A → ℂ) :
    handBF s l φ 0 = 0 := by
  funext h w
  simp [GlobalTheory.Unf.handBF]

theorem handFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (c b : ℂ) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) :
    handFB s vL (c • Y) (b • Ξ) = (star c * b) • handFB s vL Y Ξ := by
  funext h₁
  simp only [GlobalTheory.Unf.handFB, GlobalTheory.Unf.pairKer, GlobalTheory.MixPer.contractT, GlobalTheory.MixPer.thPair, LinearMap.map_smul,
    Pi.smul_apply, smul_eq_mul, star_mul']
  simp_rw [show ∀ x y : ℂ, b * x * (star c * y) = (star c * b) * (x * y) from fun x y => by ring, integral_const_mul]

theorem per_smul {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a b : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) (b • f) = a * b * B.per ψ φ f := by
  simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer, GlobalTheory.MixPer.besFun, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ x y z : ℂ, a * x * (b * y) * z = (a * b) * (x * y * z) from fun x y z => by ring, integral_const_mul]

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7}

theorem hand_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), (∀ (Ψ₁ : WO B.V J.W → ℂ) (Ψ₂ : WO J.W B'.V → ℂ) (a b : ℂ), handFB s₂ vL (handBF s₁ l φ (flatBF s₁ (a • Ψ₁))) (flatFB s₂ (b • Ψ₂)) = (a * b) • handFB s₂ vL (handBF s₁ l φ (flatBF s₁ Ψ₁)) (flatFB s₂ Ψ₂)) ∧ (∀ Ξ₂, handFB s₂ vL (handBF s₁ l φ 0) Ξ₂ = 0) ∧ ∀ (a b : ℂ) (φ' : GA D B'.A → ℂ) (f : GA D B'.V → ℂ), B'.per ψ (a • φ') (b • f) = a * b * B'.per ψ φ' f := by
  intro D ψ σ B J B' s₁ s₂ l vL φ
  refine ⟨fun Ψ₁ Ψ₂ a b => ?_, fun Ξ₂ => ?_, fun a b φ' f => per_smul B' ψ a b φ' f⟩
  · rw [flatBF_smul, flatFB_smul, handBF_smul, handFB_smul, star_star]
  · rw [handBF_zero]
    funext h₁
    simp [GlobalTheory.Unf.handFB, GlobalTheory.Unf.pairKer, GlobalTheory.MixPer.contractT, GlobalTheory.MixPer.thPair]

end GlobalTheory.HandHom
