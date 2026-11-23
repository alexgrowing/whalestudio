import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsomorphismLocalToGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLocalFactorSystemStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SquareIso

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem per_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (x : Fl g) :
    per τ (n • x) = n • per τ x := by
  ext i
  simp [per, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc, mul_add]

theorem transl_mulN (τ : E → Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (l : Fl g) (P : Pt E g) :
    transl τ (n • l) (mulN n P) = mulN n (transl τ l P) := by
  simp only [transl, mulN, per_zsmul, smul_add]

theorem thetaExp_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (l : Fl g) (z : Fin g → ℂ) :
    thetaExp τ (n • l) (n • z) = (n : ℂ) ^ 2 * thetaExp τ l z := by
  have h1 : (fun i => (((n • l) (Sum.inl i) : ℝ) : ℂ)) = (n : ℂ) • fun i => (l (Sum.inl i) : ℂ) := by
    ext i; simp
  have h2 : n • z = (n : ℂ) • z := by ext i; simp
  simp only [thetaExp, h1, h2, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem mulN_mem {B : Set E} (n : ℤ) {P : Pt E g} (hP : P ∈ cov B g) : mulN n P ∈ cov B g :=
  ⟨hP.1, trivial⟩

theorem transl_mem {B : Set E} (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) {P : Pt E g}
    (hP : P ∈ cov B g) : transl τ x P ∈ cov B g :=
  ⟨hP.1, trivial⟩

theorem differentiable_mulN (n : ℤ) : Differentiable ℂ (mulN (E := E) (g := g) n) := by
  have : mulN (E := E) (g := g) n = fun P => (P.1, (n : ℂ) • P.2) := by
    funext P; simp [mulN, Int.cast_smul_eq_zsmul]
  rw [this]
  fun_prop

def thetaFac (τ : E → Matrix (Fin g) (Fin g) ℂ) (l : Fl g) (P : Pt E g) : ℂ :=
  Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)

theorem thetaFac_ne_zero (τ : E → Matrix (Fin g) (Fin g) ℂ) (l : Fl g) (P : Pt E g) :
    thetaFac τ l P ≠ 0 := Complex.exp_ne_zero _

theorem thetaFac_mulN (τ : E → Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (l : Fl g) (P : Pt E g) :
    thetaFac τ (n • l) (mulN n P) = thetaFac τ l P ^ (n.natAbs ^ 2) := by
  have hN : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
    have h := Int.natAbs_sq n
    have : ((n.natAbs : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by exact_mod_cast h
    push_cast
    simpa using this
  simp only [thetaFac, mulN, thetaExp_zsmul, ← Complex.exp_nat_mul, hN]
  ring_nf

section Iso

variable {B U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
  {j₁ j₂ j₃ j₁' j₂' : Fl g → Pt E g → ℂ} {φ ψ : Pt E g → ℂ}

theorem iso_trans (h₁ : IsBundleIso B τ M j₁ j₂ φ) (h₂ : IsBundleIso B τ M j₂ j₃ ψ) :
    IsBundleIso B τ M j₁ j₃ (fun P => φ P * ψ P) := by
  refine ⟨h₁.1.mul h₂.1, fun P hP => mul_ne_zero (h₁.2.1 P hP) (h₂.2.1 P hP),
    fun l hl P hP => ?_⟩
  have e1 := h₁.2.2 l hl P hP
  have e2 := h₂.2.2 l hl P hP
  linear_combination ψ (transl τ l P) * e1 + φ P * e2

theorem iso_symm (h : IsBundleIso B τ M j₁ j₂ φ) :
    IsBundleIso B τ M j₂ j₁ (fun P => (φ P)⁻¹) := by
  refine ⟨h.1.inv h.2.1, fun P hP => inv_ne_zero (h.2.1 P hP), fun l hl P hP => ?_⟩
  have e := h.2.2 l hl P hP
  have a := h.2.1 _ (transl_mem τ l hP)
  have b := h.2.1 P hP
  field_simp
  linear_combination -e

theorem iso_pow (k : ℕ) (h : IsBundleIso B τ M j₁ j₂ φ) :
    IsBundleIso B τ M (fun l P => j₁ l P ^ k) (fun l P => j₂ l P ^ k) (fun P => φ P ^ k) :=
  ⟨h.1.pow k, fun P hP => pow_ne_zero _ (h.2.1 P hP), fun l hl P hP => by
    simp only
    rw [← mul_pow, h.2.2 l hl P hP, mul_pow]⟩

theorem iso_mono (hUB : U ⊆ B) (h : IsBundleIso B τ M j₁ j₂ φ) : IsBundleIso U τ M j₁ j₂ φ := by
  have hc : cov U g ⊆ cov B g := fun P hP => ⟨hUB hP.1, trivial⟩
  exact ⟨h.1.mono hc, fun P hP => h.2.1 P (hc hP), fun l hl P hP => h.2.2 l hl P (hc hP)⟩

theorem iso_base {c : E → ℂ} (hc : DifferentiableOn ℂ c B) (hc0 : ∀ b ∈ B, c b ≠ 0)
    (h : IsBundleIso B τ M j₁ j₂ φ) : IsBundleIso B τ M j₁ j₂ (fun P => φ P * c P.1) := by
  refine ⟨h.1.mul (hc.comp differentiableOn_fst fun P hP => hP.1),
    fun P hP => mul_ne_zero (h.2.1 P hP) (hc0 _ hP.1), fun l hl P hP => ?_⟩
  have e := h.2.2 l hl P hP
  show φ (transl τ l P) * c (transl τ l P).1 * j₁ l P = j₂ l P * (φ P * c P.1)
  have : (transl τ l P).1 = P.1 := rfl
  rw [this]
  linear_combination c P.1 * e

theorem iso_mulPull (n : ℤ) (h : IsBundleIso B τ (stdLat g) j₁ j₂ φ) :
    IsBundleIso B τ (stdLat g) (mulPullFactor n j₁) (mulPullFactor n j₂)
      (fun P => φ (mulN n P)) := by
  refine ⟨h.1.comp (differentiable_mulN n).differentiableOn fun P hP => mulN_mem n hP,
    fun P hP => h.2.1 _ (mulN_mem n hP), fun l hl P hP => ?_⟩
  simp only [mulPullFactor]
  rw [← transl_mulN]
  exact h.2.2 _ (Submodule.smul_mem _ n hl) _ (mulN_mem n hP)

end Iso

theorem char_zsmul {U : Set E} {χ : Fl g → E → ℂ}
    (hχ0 : ∀ l ∈ stdLat g, ∀ b ∈ U, χ l b ≠ 0)
    (hχ : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b ∈ U, χ (l + l') b = χ l b * χ l' b)
    {l : Fl g} (hl : l ∈ stdLat g) {b : E} (hb : b ∈ U) (n : ℤ) :
    χ (n • l) b = χ l b ^ n := by
  have h0 : χ 0 b = 1 := by
    have e := hχ 0 (zero_mem _) 0 (zero_mem _) b hb
    rw [add_zero] at e
    have hz := hχ0 0 (zero_mem _) b hb
    field_simp at e
    exact e.symm
  induction n using Int.induction_on with
  | zero => simp [h0]
  | succ k ih =>
    rw [add_smul, one_smul, hχ _ (Submodule.smul_mem _ _ hl) _ hl _ hb, ih,
      zpow_add_one₀ (hχ0 l hl b hb)]
  | pred k ih =>
    have e := hχ _ (Submodule.smul_mem _ (-(k : ℤ) - 1) hl) _ hl _ hb
    have hk : (-(k : ℤ) - 1) • l + l = (-(k : ℤ)) • l := by rw [sub_smul, one_smul]; abel
    rw [hk, ih] at e
    rw [zpow_sub_one₀ (hχ0 l hl b hb), e]
    field_simp [hχ0 l hl b hb]

end GlobalTheory.SquareIso

namespace GlobalTheory.SquareIso

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem local_sq {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (n : ℤ)
    {j : Fl g → Pt E g → ℂ} {χ : Fl g → E → ℂ}
    (hχ0 : ∀ l ∈ stdLat g, ∀ b ∈ U, χ l b ≠ 0)
    (hχ : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b ∈ U, χ (l + l') b = χ l b * χ l' b)
    {φ₀ ι : Pt E g → ℂ}
    (h₀ : IsBundleIso U τ (stdLat g) j (fun l P => thetaFac τ l P * χ l P.1) φ₀)
    (hι : IsBundleIso U τ (stdLat g) (mulPullFactor (-1) j) j ι) :
    ∃ φ, IsBundleIso U τ (stdLat g) (mulPullFactor n j)
      (fun l P => j l P ^ (n.natAbs ^ 2)) φ := by
  set K : Fl g → Pt E g → ℂ := fun l P => thetaFac τ l P * χ l P.1 with hK
  have hpullK : ∀ m : ℤ, ∀ l ∈ stdLat g, ∀ P ∈ cov U g,
      mulPullFactor m K l P = thetaFac τ l P ^ (m.natAbs ^ 2) * χ l P.1 ^ m := by
    intro m l hl P hP
    simp only [hK, mulPullFactor, thetaFac_mulN]
    rw [show (mulN m P).1 = P.1 from rfl, char_zsmul hχ0 hχ hl hP.1]
  obtain ⟨ψ, hψ⟩ : ∃ ψ, IsBundleIso U τ (stdLat g) (mulPullFactor (-1) K) K ψ :=
    ⟨_, iso_trans (iso_trans (iso_symm (iso_mulPull (-1) h₀)) hι) h₀⟩
  have hψe : ∀ l ∈ stdLat g, ∀ P ∈ cov U g, ψ (transl τ l P) = χ l P.1 ^ 2 * ψ P := by
    intro l hl P hP
    have e := hψ.2.2 l hl P hP
    rw [hpullK (-1) l hl P hP] at e
    have ht := thetaFac_ne_zero τ l P
    have hc := hχ0 l hl P.1 hP.1
    simp only [hK, Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, one_pow, pow_one, _root_.zpow_neg,
      zpow_one] at e
    have hcc : χ l P.1 ^ 2 * (χ l P.1)⁻¹ = χ l P.1 := by field_simp
    have e2 : thetaFac τ l P * (χ l P.1)⁻¹ * (ψ (transl τ l P) - χ l P.1 ^ 2 * ψ P) = 0 := by
      linear_combination e - thetaFac τ l P * ψ P * hcc
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd h (mul_ne_zero ht (inv_ne_zero hc))
    · exact sub_eq_zero.1 h
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have hnn : 0 ≤ n * (n - 1) := by rcases le_or_gt n 0 with h | h <;> nlinarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hN : ((n.natAbs ^ 2 : ℕ) : ℤ) = n + 2 * k := by
    have h := Int.natAbs_sq n
    rw [Nat.cast_pow, h, hk]
    linear_combination hm
  have hmid : IsBundleIso U τ (stdLat g) (mulPullFactor n K)
      (fun l P => K l P ^ (n.natAbs ^ 2)) (fun P => ψ P ^ k) := by
    refine ⟨hψ.1.pow k, fun P hP => pow_ne_zero _ (hψ.2.1 P hP), fun l hl P hP => ?_⟩
    have hc := hχ0 l hl P.1 hP.1
    have hpow : χ l P.1 ^ (n.natAbs ^ 2) = χ l P.1 ^ n * (χ l P.1 ^ 2) ^ k := by
      rw [← zpow_natCast, hN, zpow_add₀ hc, ← pow_mul, ← zpow_natCast]
      push_cast
      ring_nf
    show ψ (transl τ l P) ^ k * mulPullFactor n K l P = K l P ^ (n.natAbs ^ 2) * ψ P ^ k
    rw [hpullK n l hl P hP, hψe l hl P hP, hK]
    simp only
    rw [mul_pow, mul_pow, hpow]
    ring
  exact ⟨_, iso_trans (iso_trans (iso_mulPull n h₀) hmid) (iso_symm (iso_pow _ h₀))⟩

theorem exists_squareIso : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ →
    ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j →
    (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r →
    InducesPolarisation B τ (stdLat g) j → ∀ n : ℤ, ∃ φ, IsSquareIso B τ j r n φ := by
  intro g E _ _ _ B τ hτ j r hj ⟨ι, hι⟩ hr hpol n
  have hloc : ∀ b ∈ B, ∃ U : Set E, IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧ ∃ φ,
      IsBundleIso U τ (stdLat g) (mulPullFactor n j) (fun l P => j l P ^ (n.natAbs ^ 2)) φ := by
    intro b hb
    obtain ⟨U, hUo, hbU, hUB, χ, hχ1, hχ2, φ₀, h₀⟩ := GlobalTheory.T.polarisation_local_factor_system hτ j hj hpol b hb
    exact ⟨U, hUo, hbU, hUB,
      local_sq n (fun l hl b hb => (hχ1 l hl).2 b hb) hχ2 h₀ (iso_mono hUB hι)⟩
  obtain ⟨φ, hφ, hφ0⟩ := GlobalTheory.T.bundle_isomorphism_local_to_global hτ (mulPullFactor n j) _
    (fun l hl P hP => (hj.1 _ (Submodule.smul_mem _ n hl)).2 _ (mulN_mem n hP)) hloc
  refine ⟨fun P => φ P * (r P.1 ^ (n.natAbs ^ 2) * (r P.1)⁻¹), iso_base (c := fun b => r b ^ (n.natAbs ^ 2) * (r b)⁻¹) ?_ ?_ hφ, fun b hb => ?_⟩
  · exact (hr.1.pow _).mul (hr.1.inv hr.2)
  · intro b hb
    exact mul_ne_zero (pow_ne_zero _ (hr.2 b hb)) (inv_ne_zero (hr.2 b hb))
  · show φ (zeroSec g b) * (r b ^ (n.natAbs ^ 2) * (r b)⁻¹) * r b = r b ^ (n.natAbs ^ 2)
    rw [hφ0 b hb]
    field_simp [hr.2 b hb]

end GlobalTheory.SquareIso
