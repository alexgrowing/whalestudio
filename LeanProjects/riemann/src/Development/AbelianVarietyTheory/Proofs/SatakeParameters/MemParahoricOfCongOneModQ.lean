import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.ParahoricOfCong

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem mem_stdAt_iff_sclLat_zero (q N : ℕ) (x : Sp E N) :
    x ∈ stdAt E N P ↔ x ∈ LocE.sclLat P q N (fun _ => 0) := by
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
  simp

theorem map_mem_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (h : Sp E N ≃ₗ[E] Sp E N) (hh : ∀ x ∈ stdAt E N P, q⁻¹ • (h x - x) ∈ stdAt E N P) :
    ∀ x ∈ M, h x ∈ M := by
  intro x hx
  have e : h x = x + (h x - x) := by abel
  rw [e]
  exact M.add_mem hx (hqM _ (hh x (hM hx)))

theorem mem_stabL_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (g : Sp E N ≃ₗ[E] Sp E N) (h1 : ∀ x ∈ stdAt E N P, q⁻¹ • (g x - x) ∈ stdAt E N P)
    (h2 : ∀ x ∈ stdAt E N P, q⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) :
    g ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    have := map_mem_of_cong P q M hM hqM g⁻¹ h2 (g x) hx
    have e : g⁻¹ (g x) = x := LinearEquiv.symm_apply_apply g x
    rwa [e] at this
  · exact map_mem_of_cong P q M hM hqM g h1 x

end GlobalTheory.ParahoricOfCong

open GlobalTheory.ParahoricOfCong in

theorem GlobalTheory.ParahoricOfCong.mem_JQ_of_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (kj n c : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)), (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E (n + c) P) → (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E (n + c) P) → g ∈ LocE.JQ P (qOf P) kj n c := by
  intro E _ _ _ P kj n c g h1 h2
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  refine ⟨?_, ?_⟩
  · refine mem_stabL_of_cong P _ _ le_rfl (fun y hy => ?_) g h1 h2
    have e : y = (qOf P : E) • ((qOf P : E)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
    rw [e, Nat.cast_smul_eq_nsmul E]
    exact nsmul_mem hy _
  · refine mem_stabL_of_cong P _ _ ?_ ?_ g h1 h2
    · intro x hx
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)]
      have := GlobalTheory.CongLevel.sclLat_le P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n)
      exact this (by simpa [LocE.parL] using hx)
    · intro y hy
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)] at hy
      have := GlobalTheory.CongLevel.smul_mem_sclLat P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n) y hy
      simpa [LocE.parL] using this
