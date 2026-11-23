import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTriple

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem theta_cocycle_eq_exp_hermitian (T : Tor D) (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T (w0 D • x) y).im : ℂ)) := by
  have h : Hf D T (w0 D • x) y = w0 D * Hf D T x y := by
    rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  rw [bc, h, Complex.mul_im, h1, h2]
  congr 1
  push_cast
  ring

theorem nice_of_klat (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    Nice D (tor0 D cc δ) A := by
  obtain ⟨-, h0, h1, h2, -, -, -⟩ :=
    GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have hw := GlobalTheory.ThetaInter.klat_smul_mem hA a hx
    rw [ha] at hw
    obtain ⟨m, hm⟩ := h1 _ hw y hy
    rw [theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  · have h := hx y hy
    rw [bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination -hn
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h3

theorem index_ne_zero (hc : Crv D cc δ) {A₁ A₂ : AddSubgroup (VC D N N')} (h₁ : KLat D (tor0 D cc δ) A₁)
    (h₂ : KLat D (tor0 D cc δ) A₂) : (A₁.addSubgroupOf A₂).index ≠ 0 := by
  haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂
    (GlobalTheory.ThetaInter.klat_facts hc h₂).1
  exact AddSubgroup.index_ne_zero_of_finite

theorem iop_self {T : Tor D} {A : AddSubgroup (VC D N N')} (hA : Nice D T A) {e : VC D N N' → ℂ}
    (he : e ∈ ThSp D T A) : Iop D T A A e = e := by
  rw [hA.Iop_eq]
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1 := hi
  obtain ⟨hs, ⟨q₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hc
  rw [finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi,
    ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]
  simp

theorem klat_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  intro D cc δ hc N N'
  refine ⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂,
    fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he
  exact ⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂,
    index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩

end GlobalTheory.ThetaTriple
