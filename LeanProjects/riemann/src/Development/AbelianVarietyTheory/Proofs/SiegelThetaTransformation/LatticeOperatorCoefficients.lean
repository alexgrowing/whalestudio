import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ip_smul_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
    {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hc : IsSB fun x => conj (ψ x) :=
    (isSB_algebra_haar_linear K κ ι ψ ψ hψ hψ).2.2.2.1
  have hp : IsSB (φ * fun x => conj (ψ x)) :=
    (isSB_algebra_haar_linear K κ ι φ _ hφ hc).2.2.1
  have hs := (isSB_algebra_haar_linear K κ ι _ _ hp hp).2.2.2.2.2.1 (a * conj b)
  have key : (fun x => (a • φ) x * conj ((b • ψ) x)) =
      (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  unfold ip
  rw [key, hs]
  rfl

theorem classSum_eq_sum {M : ℕ} [Fintype (Cls E n M)] (f : Lt E n → ℂ) :
    classSum M f = ∑ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1 := by
  unfold classSum
  exact finsum_eq_sum_of_fintype _

theorem exists_mass {M : ℕ} (hM : 0 < M) : ∃ m : ℝ, 0 < m ∧
    (∀ (f : Lt E n → ℂ) (a : ℂ), (∀ Λ ∈ Vset E n M, f Λ = a) → classSum M f = m * a) ∧
    ∀ (f : Lt E n → ℂ) (b : ℝ), (∀ Λ ∈ Vset E n M, ‖f Λ‖ ≤ b) → ‖classSum M f‖ ≤ m * b := by
  classical
  obtain ⟨hfin, hstd, hwt, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  refine ⟨∑ c : Cls E n M, wt M (Quot.out c).1, ?_, ?_, ?_⟩
  · apply Finset.sum_pos
    · intro c _
      exact (hwt _ (Quot.out c).2).2
    · exact ⟨(Quot.mk _ ⟨stdL E n, hstd⟩ : Cls E n M), Finset.mem_univ _⟩
  · intro f a hf
    rw [classSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hf _ (Quot.out c).2]
  · intro f b hf
    rw [classSum_eq_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hw := (hwt _ (Quot.out c).2).2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact mul_le_mul_of_nonneg_left (hf _ (Quot.out c).2) hw.le

theorem classSum_mul {M : ℕ} (hM : 0 < M) (f : Lt E n → ℂ) (a : ℂ) :
    classSum M f * a = classSum M fun Λ => f Λ * a := by
  classical
  have := (finite_cls_and_stab E n M hM).1
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  rw [classSum_eq_sum, classSum_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => mul_assoc _ _ _

end GlobalTheory.SW.Coef

namespace GlobalTheory.SW

open Coef

private theorem classSum_congr_of_eqOn_Vset {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n M : ℕ} {f g : Lt E n → ℂ} (h : ∀ Λ ∈ Vset E n M, f Λ = g Λ) :
    classSum M f = classSum M g := by
  unfold classSum
  exact finsum_congr fun c => by rw [h _ (Quot.out c).2]

theorem lattice_operator_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ (a θ : ℝ), 0 < a ∧ θ < 1 ∧ (∀ L ∈ 𝓛, classSum M (fun Λ => ip (Φ L Λ) (Φ L Λ)) = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ θ * a) ∧ ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, classSum M (fun Λ => ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ)) * μ γ L * conj (μ γ L') = classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) := by
  intro E _ _ _ r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hsys
  obtain ⟨m, hm, hconst, hbd⟩ := Coef.exists_mass (E := E) (n := n) hM
  obtain ⟨a, ha, hdiag, b, θ, hθ, hoff, hbt⟩ := hsys.norm
  have hma : 0 < m * a := mul_pos hm ha
  refine ⟨m * a, θ, hma, hθ, fun L hL => ?_, ?_⟩
  · have hb : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
        ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ m * a * b L L'.1 := fun L' => by
      rw [mul_assoc]
      exact hbd _ (a * b L L'.1) fun Λ hΛ => hoff L hL L'.1 L'.2.1 Λ hΛ
    have hS : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => m * a * b L L'.1 :=
      (hbt L hL).1.mul_left (m * a)
    have hT := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hS
    refine ⟨?_, hT, ?_⟩
    · rw [hconst _ (a : ℂ) fun Λ hΛ => hdiag L hL Λ hΛ]
      exact (Complex.ofReal_mul m a).symm
    · calc _ ≤ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, m * a * b L L'.1 :=
            Summable.tsum_le_tsum hb hT hS
        _ = m * a * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, b L L'.1 := tsum_mul_left
        _ ≤ m * a * θ := mul_le_mul_of_nonneg_left (hbt L hL).2 hma.le
        _ = θ * (m * a) := mul_comm _ _
  · intro γ hγ L hL L' hL'
    have hun := hsys.un γ hγ
    have key : ∀ Λ ∈ Vset E n M, ip (Φ L Λ) (Φ L' Λ) =
        ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ) * (μ γ L * conj (μ γ L')) := by
      intro Λ hΛ
      have hw := wG_laws E r X g bas idx n hs hn γ hun (Φ L Λ) (hsys.sb L hL Λ hΛ)
      rw [← (hw.2.2.1 (Φ L' Λ) (hsys.sb L' hL' Λ hΛ)).1, (hsys.mu γ hγ L hL).2 Λ hΛ,
        (hsys.mu γ hγ L' hL').2 Λ hΛ,
        Coef.ip_smul_smul (hsys.sb _ (hsys.stab γ hγ L hL) Λ hΛ)
          (hsys.sb _ (hsys.stab γ hγ L' hL') Λ hΛ)]
      ring
    rw [mul_assoc, Coef.classSum_mul hM]
    exact classSum_congr_of_eqOn_Vset fun Λ hΛ => (key Λ hΛ).symm

end GlobalTheory.SW
