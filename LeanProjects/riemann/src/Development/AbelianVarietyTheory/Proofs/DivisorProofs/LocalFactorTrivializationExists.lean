import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorOfAutomorphyLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaQuasiPeriodicNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePeriodExponentLinearStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.ThetaTranslateLocal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem mem_cov {U : Set E} {P : Pt E g} : P ∈ cov U g ↔ P.1 ∈ U := by
  simp [cov]

theorem transl_mem_cov {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {x : Fl g} {P : Pt E g}
    (hP : P ∈ cov U g) : transl τ x P ∈ cov U g := by
  rw [mem_cov] at hP ⊢; exact hP

theorem iso_comp {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j j' j'' : Fl g → Pt E g → ℂ} {φ φ' : Pt E g → ℂ}
    (h : IsBundleIso U τ M j j' φ) (h' : IsBundleIso U τ M j' j'' φ') :
    IsBundleIso U τ M j j'' (fun P => φ P * φ' P) := by
  refine ⟨h.1.mul h'.1, fun P hP => mul_ne_zero (h.2.1 P hP) (h'.2.1 P hP), fun l hl P hP => ?_⟩
  have e1 := h.2.2 l hl P hP
  have e2 := h'.2.2 l hl P hP
  calc φ (transl τ l P) * φ' (transl τ l P) * j l P
      = φ' (transl τ l P) * (φ (transl τ l P) * j l P) := by ring
    _ = φ' (transl τ l P) * j' l P * φ P := by rw [e1]; ring
    _ = j'' l P * (φ P * φ' P) := by rw [e2]; ring

theorem iso_inv {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j j' : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ}
    (h : IsBundleIso U τ M j j' φ) : IsBundleIso U τ M j' j (fun P => (φ P)⁻¹) := by
  refine ⟨h.1.inv h.2.1, fun P hP => inv_ne_zero (h.2.1 P hP), fun l hl P hP => ?_⟩
  have e := h.2.2 l hl P hP
  have h1 := h.2.1 _ (transl_mem_cov (x := l) (τ := τ) hP)
  have h2 := h.2.1 P hP
  field_simp
  linear_combination -e

theorem iso_mono {U B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j j' : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ} (hUB : U ⊆ B)
    (h : IsBundleIso B τ M j j' φ) : IsBundleIso U τ M j j' φ := by
  have hc : cov U g ⊆ cov B g := fun P hP => mem_cov.2 (hUB (mem_cov.1 hP))
  exact ⟨h.1.mono hc, fun P hP => h.2.1 P (hc hP), fun l hl P hP => h.2.2 l hl P (hc hP)⟩

theorem iso_congr {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j₁ j₂ j₁' j₂' : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ}
    (e : ∀ l ∈ M, ∀ P ∈ cov U g, j₁ l P = j₂ l P) (e' : ∀ l ∈ M, ∀ P ∈ cov U g, j₁' l P = j₂' l P)
    (h : IsBundleIso U τ M j₁ j₁' φ) : IsBundleIso U τ M j₂ j₂' φ := by
  refine ⟨h.1, h.2.1, fun l hl P hP => ?_⟩
  rw [← e l hl P hP, ← e' l hl P hP]
  exact h.2.2 l hl P hP

theorem iso_mul {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j j' : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ} (k : Fl g → Pt E g → ℂ)
    (h : IsBundleIso U τ M j j' φ) :
    IsBundleIso U τ M (fun l P => k l P * j l P) (fun l P => k l P * j' l P) φ := by
  refine ⟨h.1, h.2.1, fun l hl P hP => ?_⟩
  have e := h.2.2 l hl P hP
  calc φ (transl τ l P) * (k l P * j l P) = k l P * (φ (transl τ l P) * j l P) := by ring
    _ = _ := by rw [e]; ring

theorem per_neg (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fl g) : per τ (-l) = -per τ l := by
  ext i
  simp only [per, Pi.neg_apply, Pi.add_apply, Matrix.vecMul, dotProduct, Complex.ofReal_neg,
    neg_mul, Finset.sum_neg_distrib]
  ring

theorem mulN_neg_one_transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (l : Fl g) (P : Pt E g) :
    mulN (-1) (transl τ l P) = transl τ ((-1 : ℤ) • l) (mulN (-1) P) := by
  simp [mulN, transl, per_neg, neg_add]

theorem iso_negPull {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    {j j' : Fl g → Pt E g → ℂ} {φ : Pt E g → ℂ}
    (h : IsBundleIso U τ (stdLat g) j j' φ) :
    IsBundleIso U τ (stdLat g) (mulPullFactor (-1) j) (mulPullFactor (-1) j')
      (fun P => φ (mulN (-1) P)) := by
  have hm : ∀ P ∈ cov U g, mulN (-1) P ∈ cov U g := fun P hP => mem_cov.2 (mem_cov.1 hP)
  refine ⟨?_, fun P hP => h.2.1 _ (hm P hP), fun l hl P hP => ?_⟩
  · have hd : Differentiable ℂ (mulN (E := E) (g := g) (-1)) := by
      unfold mulN; fun_prop
    exact h.1.comp hd.differentiableOn hm
  · simp only [mulPullFactor]
    rw [mulN_neg_one_transl]
    exact h.2.2 _ (Submodule.smul_mem _ _ hl) _ (hm P hP)

end GlobalTheory.ThetaTranslateLocal

namespace GlobalTheory.ThetaTranslateLocal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem thetaExp_neg (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fl g) (z : Fin g → ℂ) :
    thetaExp τ ((-1 : ℤ) • l) ((-1 : ℤ) • z) = thetaExp τ l z := by
  have h1 : (fun i => (((-l) (Sum.inl i) : ℝ) : ℂ)) = -fun i => ((l (Sum.inl i) : ℝ) : ℂ) := by
    ext i; simp
  rw [neg_one_smul, neg_one_smul]
  simp only [thetaExp, h1, Matrix.neg_vecMul, neg_dotProduct, dotProduct_neg, neg_neg]

theorem theta_translate_iso_char : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ x : Fl g, IsBundleIso U τ (stdLat g) (translPullFactor τ x (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))) (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2) * Complex.exp (2 * π * Complex.I * (-(riem x l : ℂ)))) (fun P => Complex.exp (2 * π * Complex.I * ((fun i => (x (Sum.inl i) : ℂ)) ⬝ᵥ P.2))) := by
  intro g E _ _ U τ hτ x
  refine ⟨?_, fun _ _ => Complex.exp_ne_zero _, fun l hl P hP => ?_⟩
  · apply Differentiable.differentiableOn
    unfold dotProduct
    fun_prop
  · have hsym := (hτ.2.2 P.1 (mem_cov.1 hP)).1
    simp only [translPullFactor, transl]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [thetaExp, per, dotProduct_add]
    set px : Fin g → ℂ := fun i => (x (Sum.inl i) : ℂ)
    set qx : Fin g → ℂ := fun i => (x (Sum.inr i) : ℂ)
    set pl : Fin g → ℂ := fun i => (l (Sum.inl i) : ℂ)
    set ql : Fin g → ℂ := fun i => (l (Sum.inr i) : ℂ)
    have key : (pl ᵥ* τ P.1) ⬝ᵥ px = (px ᵥ* τ P.1) ⬝ᵥ pl := by
      rw [← Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsym.eq, dotProduct_comm]
    have hr : (riem x l : ℂ) = qx ⬝ᵥ pl - px ⬝ᵥ ql := by
      simp [riem, dotProduct, Finset.sum_sub_distrib, qx, pl, px, ql]
    have hpx : px ⬝ᵥ (pl ᵥ* τ P.1) = (pl ᵥ* τ P.1) ⬝ᵥ px := dotProduct_comm _ _
    have hpl : pl ⬝ᵥ (px ᵥ* τ P.1) = (px ᵥ* τ P.1) ⬝ᵥ pl := dotProduct_comm _ _
    have hqx : pl ⬝ᵥ qx = qx ⬝ᵥ pl := dotProduct_comm _ _
    rw [hr]
    linear_combination (2 * π * Complex.I) * (hpx - hpl + key - hqx)

theorem quotient_by_theta : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ), IsFactor B τ (stdLat g) j → InducesPolarisation B τ (stdLat g) j → ∀ ι : Pt E g → ℂ, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι → IsFactor B τ (stdLat g) (fun l P => j l P / Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) ∧ (∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ, (∀ l ∈ stdLat g, Differentiable ℂ (f l) ∧ ∀ z, j l (b, z) / Complex.exp (2 * π * Complex.I * thetaExp (τ b) l z) = Complex.exp (2 * π * Complex.I * f l z)) ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ z, f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = 0) ∧ IsBundleIso B τ (stdLat g) (mulPullFactor (-1) (fun l P => j l P / Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))) (fun l P => j l P / Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) ι := by
  intro g E _ _ B τ hτ j hj hpol ι hι
  obtain ⟨hθf, hθp⟩ := theta_factor hτ
  refine ⟨⟨fun l hl => ⟨by simp only [div_eq_mul_inv]; exact (hj.1 l hl).1.mul ((hθf.1 l hl).1.inv (hθf.1 l hl).2),
    fun P hP => div_ne_zero ((hj.1 l hl).2 P hP) ((hθf.1 l hl).2 P hP)⟩,
    fun l hl l' hl' P hP => ?_⟩, fun b hb => ?_, ?_⟩
  · have e1 := hj.2 l hl l' hl' P hP
    have e2 := hθf.2 l hl l' hl' P hP
    simp only at e2 ⊢
    rw [e1, e2, mul_div_mul_comm]
  · obtain ⟨f, hf, hrel⟩ := hpol b hb
    obtain ⟨fθ, hfθ, hrelθ⟩ := hθp b hb
    refine ⟨fun l z => f l z - fθ l z, fun l hl => ⟨(hf l hl).1.sub (hfθ l hl).1, fun z => ?_⟩,
      fun l hl l' hl' z => ?_⟩
    · have e := (hfθ l hl).2 z
      simp only at e
      rw [(hf l hl).2 z, e, ← Complex.exp_sub]
      ring_nf
    · linear_combination hrel l hl l' hl' z - hrelθ l hl l' hl' z
  · have h := iso_mul (fun l P => (Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))⁻¹) hι
    refine iso_congr (fun l _ P _ => ?_) (fun l _ P _ => ?_) h
    · simp only [mulPullFactor]
      rw [show (mulN (-1) P).1 = P.1 from rfl, show (mulN (-1) P).2 = (-1 : ℤ) • P.2 from rfl,
        thetaExp_neg, div_eq_mul_inv, mul_comm]
    · simp only [div_eq_mul_inv, mul_comm]

end GlobalTheory.ThetaTranslateLocal

namespace GlobalTheory.ThetaTranslateLocal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem add_zero_of_add {M : Submodule ℤ (Fl g)} {U : Set E} {s : Fl g → E → ℂ}
    (hs : ∀ l ∈ M, ∀ l' ∈ M, ∀ b ∈ U, s (l + l') b = s l b + s l' b) :
    ∀ l ∈ M, ∀ b ∈ U, s ((-1 : ℤ) • l) b = -s l b := by
  intro l hl b hb
  have h0 : s 0 b = 0 := by
    have := hs 0 M.zero_mem 0 M.zero_mem b hb
    simp only [add_zero] at this
    linear_combination -this
  have := hs l hl ((-1 : ℤ) • l) (M.smul_mem _ hl) b hb
  rw [neg_one_smul, add_neg_cancel, h0] at this
  rw [neg_one_smul]
  linear_combination -this

theorem exists_local_theta_translate_iso : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → InducesPolarisation B τ (stdLat g) j → ∀ b₀ ∈ B, ∃ U : Set E, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ B ∧ ∃ (x : Fl g) (φ : Pt E g → ℂ), IsBundleIso U τ (stdLat g) (translPullFactor τ x (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))) j φ := by
  intro g E _ _ _ B τ hτ j hj ⟨ι, hι⟩ hpol b₀ hb₀
  obtain ⟨hu, hdeg, hιu⟩ := quotient_by_theta hτ j hj hpol ι hι
  obtain ⟨U, hUo, hb₀U, hUB, hUc, s, hsc, hsadd, φ₁, hφ₁⟩ := GlobalTheory.T.factor_of_automorphy_logarithm hτ _ hu hdeg b₀ hb₀
  have hτU : IsPeriodMap U τ :=
    ⟨hUo, fun i k => (hτ.2.1 i k).mono hUB, fun b hb => hτ.2.2 b (hUB hb)⟩
  have hneg := add_zero_of_add hsadd

  have h1 := iso_congr (j₂ := fun l P => Complex.exp (2 * π * Complex.I * (-s l P.1)))
    (fun l hl P hP => by
      simp only [mulPullFactor, mulN]
      rw [hneg l hl P.1 (mem_cov.1 hP)]) (fun _ _ _ _ => rfl) (iso_negPull hφ₁)
  have hψ := iso_comp h1 (iso_comp (iso_mono hUB hιu) (iso_inv hφ₁))
  set ψ := fun P => φ₁ (mulN (-1) P) * (ι P * (φ₁ P)⁻¹) with hψdef
  have hq : ∀ l ∈ stdLat g, ∀ P ∈ cov U g, ψ (transl τ l P) =
      Complex.exp (4 * π * Complex.I * s l P.1) * ψ P := by
    intro l hl P hP
    have e := hψ.2.2 l hl P hP
    have e2 : Complex.exp (4 * π * Complex.I * s l P.1) =
        Complex.exp (2 * π * Complex.I * s l P.1) * Complex.exp (2 * π * Complex.I * s l P.1) := by
      rw [← Complex.exp_add]; ring_nf
    have e3 : Complex.exp (2 * π * Complex.I * -s l P.1) * Complex.exp (2 * π * Complex.I * s l P.1) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    calc ψ (transl τ l P) = ψ (transl τ l P) * (Complex.exp (2 * π * Complex.I * -s l P.1) * Complex.exp (2 * π * Complex.I * s l P.1)) := by rw [e3, mul_one]
      _ = _ := by rw [e2, ← mul_assoc, e]; ring
  obtain ⟨a, ha, hψa⟩ := GlobalTheory.T.theta_quasi_periodic_normal_form hτU (fun l b => Complex.exp (4 * π * Complex.I * s l b)) ψ hψ.1 hψ.2.1 hq
  have hexp : ∀ l ∈ stdLat g, ∀ b ∈ U, Complex.exp (a b ⬝ᵥ per (τ b) l) = Complex.exp (4 * π * Complex.I * s l b) := by
    intro l hl b hb
    have hP : ((b, 0) : Pt E g) ∈ cov U g := mem_cov.2 hb
    have e1 := hq l hl _ hP
    have e2 := hψa _ (transl_mem_cov (τ := τ) (x := l) hP)
    have hne := hψ.2.1 _ hP
    simp only [transl, zero_add] at e1 e2
    rw [e2] at e1
    exact mul_left_cancel₀ hne (by linear_combination e1)
  obtain ⟨x, hx⟩ := GlobalTheory.T.additive_period_exponent_linear hτU hUc s a hsc hsadd ha hexp
  refine ⟨U, hUo, hb₀U, hUB, x, _, iso_comp (theta_translate_iso_char hτU x) (iso_comp (iso_mul _ hx) (iso_congr (fun _ _ _ _ => rfl) ?_ (iso_mul (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) hφ₁)))⟩
  intro l hl P hP
  field_simp [Complex.exp_ne_zero]

end GlobalTheory.ThetaTranslateLocal
