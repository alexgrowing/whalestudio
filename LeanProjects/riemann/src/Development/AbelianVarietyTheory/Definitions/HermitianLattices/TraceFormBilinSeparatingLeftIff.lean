import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Development.AbelianVarietyTheory.Definitions.HermitianLattices.ExistsZsmulMemOfIsLattice

noncomputable section

namespace GlobalTheory

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.FD hiding cc_cc cc_sub cc_mul cc_one cc_zero cc_eq_zero
open ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_forall_trace_mul {K : Type} [Field K] [NumberField K] {t : K}
    (h : ∀ a : K, Algebra.trace ℚ K (a * t) = 0) : t = 0 :=
  (traceForm_nondegenerate ℚ K).1 t fun a => by rw [Algebra.traceForm_apply, mul_comm]; exact h a

theorem herm_single_single (G : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
  rw [herm_single_right]; simp

theorem herm_injective {G G' : Matrix (Fin r) (Fin r) E} (h : ∀ x y, herm G x y = herm G' x y) :
    G = G' := by
  ext a b
  rw [← herm_single_single G, h, herm_single_single]

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ G *ᵥ fun b => cc (y b) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem herm_mulVec {s : ℕ} (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin s) E)
    (x y : Fin s → E) : herm G (γ *ᵥ x) (γ *ᵥ y) = herm (γᵀ * G * γ.map cc) x y := by
  have h : (fun b => cc ((γ *ᵥ y) b)) = γ.map cc *ᵥ fun b => cc (y b) := by
    funext b
    simp [mulVec, dotProduct, cc_sum]
  rw [herm_eq_dotProduct, herm_eq_dotProduct, h, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec x, vecMul_transpose]

def IsConjAdj (B : LinearMap.BilinForm ℚ (Fin r → E)) : Prop :=
  ∀ (a : E) (x y : Fin r → E), B (a • x) y = B x (cc a • y)

theorem EFf_neg_eq_trace (ξ : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    EFf (-ξ) G x y = Algebra.trace ℚ E (ξ * herm G x y) := by
  rw [EFf, neg_neg]

theorem EFf_smul_eq_trace (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    EFf ξ0 G (a • x) y = Algebra.trace ℚ E (a * (-ξ0 * herm G x y)) := by
  rw [EFf, herm_smul_left, mul_left_comm]

theorem traceFormBilin_isConjAdj (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) : IsConjAdj (traceFormBilin ξ0 G) :=
  EFf_smul_left ξ0 G

theorem EFf_swap {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) : EFf ξ0 G y x = -EFf ξ0 G x y := by
  rw [EFf, EFf, ← trace_cc, cc_mul, cc_neg, hξ, herm_conj G hG, ← map_neg]
  congr 1; ring

theorem EFf_self {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : EFf ξ0 G x x = 0 := by
  have := EFf_swap hξ hG x x
  linarith

theorem traceFormBilin_isAlt {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) : (traceFormBilin ξ0 G).IsAlt :=
  EFf_self hξ hG

theorem herm_eq_of_EFf_smul {s : ℕ} {ξ0 : E} (h0 : ξ0 ≠ 0) {G : Matrix (Fin r) (Fin r) E}
    {G' : Matrix (Fin s) (Fin s) E} {x y : Fin r → E} {x' y' : Fin s → E}
    (h : ∀ a : E, EFf ξ0 G (a • x) y = EFf ξ0 G' (a • x') y') : herm G x y = herm G' x' y' := by
  have : -ξ0 * herm G x y - -ξ0 * herm G' x' y' = 0 :=
    eq_zero_of_forall_trace_mul fun a => by
      rw [mul_sub, map_sub, ← EFf_smul_eq_trace, ← EFf_smul_eq_trace, h, sub_self]
  exact mul_left_cancel₀ (neg_ne_zero.mpr h0) (sub_eq_zero.mp this)

theorem traceFormBilin_injective {ξ0 : E} (h0 : ξ0 ≠ 0) :
    Function.Injective (traceFormBilin ξ0 : Matrix (Fin r) (Fin r) E → _) := fun G G' h =>
  herm_injective fun x y => herm_eq_of_EFf_smul h0 fun a => by
    rw [← traceFormBilin_apply, ← traceFormBilin_apply, h]

theorem traceFormBilin_isAlt_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    (G : Matrix (Fin r) (Fin r) E) : (traceFormBilin ξ0 G).IsAlt ↔ ∀ a b, cc (G a b) = G b a := by
  refine ⟨fun h a b => ?_, traceFormBilin_isAlt hξ⟩
  have : -ξ0 * G b a - -ξ0 * cc (G a b) = 0 :=
    eq_zero_of_forall_trace_mul fun t => by
      have h1 := h.neg_eq (t • Pi.single b 1) (Pi.single a 1)
      have h2 : EFf ξ0 G (Pi.single a 1) (t • Pi.single b 1) =
          -Algebra.trace ℚ E (t * (-ξ0 * cc (G a b))) := by
        rw [EFf, herm_smul_right, herm_single_single, ← trace_cc, ← map_neg]
        simp only [cc_mul, cc_neg, cc_cc, hξ]
        congr 1; ring
      rw [traceFormBilin_apply, traceFormBilin_apply, EFf_smul_eq_trace, herm_single_single, h2] at h1
      rw [mul_sub, map_sub, neg_inj.mp h1, sub_self]
  exact (mul_left_cancel₀ (neg_ne_zero.mpr h0) (sub_eq_zero.mp this)).symm

theorem forall_EFf_eq_zero_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x : Fin r → E) : (∀ y, EFf ξ0 G x y = 0) ↔ ∀ y, herm G x y = 0 := by
  refine ⟨fun h y => ?_, fun h y => by simp [EFf, h]⟩
  have : -ξ0 * herm G x y = 0 :=
    eq_zero_of_forall_trace_mul fun a => by rw [← EFf_smul_eq_trace, EFf_smul_left, h]
  exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr h0)

theorem traceFormBilin_separatingLeft_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    (traceFormBilin ξ0 G).SeparatingLeft ↔ G.det ≠ 0 := by
  constructor
  · intro h hd
    obtain ⟨v, hv, hvG⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    refine hv (h v ((forall_EFf_eq_zero_iff h0 G v).mpr fun y => ?_))
    rw [herm_eq_dotProduct, dotProduct_mulVec, hvG, zero_dotProduct]
  · intro hd v hv
    exact eq_zero_of_herm G hd v ((forall_EFf_eq_zero_iff h0 G v).mp hv)

theorem traceFormBilin_nondegenerate_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    (traceFormBilin ξ0 G).Nondegenerate ↔ G.det ≠ 0 := by
  rw [← traceFormBilin_separatingLeft_iff h0]
  exact ⟨fun h => h.1, LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft⟩

theorem EFf_mulVec_iff {s : ℕ} {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (G' : Matrix (Fin s) (Fin s) E) (γ : Matrix (Fin r) (Fin s) E) :
    (∀ x y, EFf ξ0 G (γ *ᵥ x) (γ *ᵥ y) = EFf ξ0 G' x y) ↔
      ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G' x y := by
  refine ⟨fun h x y => herm_eq_of_EFf_smul h0 fun a => ?_, fun h x y => by rw [EFf, EFf, h]⟩
  rw [← mulVec_smul, h]

def traceRep {K : Type} [Field K] [NumberField K] (f : Module.Dual ℚ K) : K :=
  ((Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)).symm f

theorem trace_mul_traceRep {K : Type} [Field K] [NumberField K] (f : Module.Dual ℚ K) (a : K) :
    Algebra.trace ℚ K (a * traceRep f) = f a := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

def skewGram (ξ0 : E) (B : LinearMap.BilinForm ℚ (Fin r → E)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b =>
    (-ξ0)⁻¹ * traceRep (B.flip (Pi.single b 1) ∘ₗ LinearMap.single ℚ (fun _ : Fin r => E) a)

omit [IsCMField E] in

theorem trace_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) (B : LinearMap.BilinForm ℚ (Fin r → E))
    (a b : Fin r) (t : E) :
    Algebra.trace ℚ E (t * (-ξ0 * skewGram ξ0 B a b)) = B (Pi.single a t) (Pi.single b 1) := by
  rw [skewGram, Matrix.of_apply, mul_inv_cancel_left₀ (neg_ne_zero.mpr h0), trace_mul_traceRep]
  rfl

theorem IsConjAdj.ext {B B' : LinearMap.BilinForm ℚ (Fin r → E)} (h : IsConjAdj B)
    (h' : IsConjAdj B')
    (hh : ∀ a b t, B (Pi.single a t) (Pi.single b 1) = B' (Pi.single a t) (Pi.single b 1)) :
    B = B' := by
  have key : ∀ a b t u, B (Pi.single a t) (Pi.single b u) = B' (Pi.single a t) (Pi.single b u) := by
    intro a b t u
    have hu : (Pi.single b u : Fin r → E) = cc (cc u) • Pi.single b 1 := by
      rw [cc_cc, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hu, ← h, ← h', ← Pi.single_smul, hh]
  refine LinearMap.pi_ext fun a t => LinearMap.pi_ext fun b u => key a b t u

theorem traceFormBilin_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) : traceFormBilin ξ0 (skewGram ξ0 B) = B := by
  refine (traceFormBilin_isConjAdj _ _).ext hB fun a b t => ?_
  have ht : (Pi.single a t : Fin r → E) = t • Pi.single a 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [← trace_skewGram h0 B, traceFormBilin_apply, ht, EFf_smul_eq_trace, herm_single_single]

theorem EFf_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) (x y : Fin r → E) : EFf ξ0 (skewGram ξ0 B) x y = B x y := by
  rw [← traceFormBilin_apply, traceFormBilin_skewGram h0 hB]

theorem skewGram_traceFormBilin {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    skewGram ξ0 (traceFormBilin ξ0 G) = G :=
  traceFormBilin_injective h0 (traceFormBilin_skewGram h0 (traceFormBilin_isConjAdj ξ0 G))

theorem eq_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    {G : Matrix (Fin r) (Fin r) E} (h : ∀ x y, B x y = EFf ξ0 G x y) : G = skewGram ξ0 B := by
  have : B = traceFormBilin ξ0 G := LinearMap.ext₂ h
  rw [this, skewGram_traceFormBilin h0]

theorem skewGram_herm {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {B : LinearMap.BilinForm ℚ (Fin r → E)} (hB : IsConjAdj B) (halt : B.IsAlt) (a b : Fin r) :
    cc (skewGram ξ0 B a b) = skewGram ξ0 B b a :=
  (traceFormBilin_isAlt_iff h0 hξ _).mp (by rwa [traceFormBilin_skewGram h0 hB]) a b

theorem skewGram_herm_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {B : LinearMap.BilinForm ℚ (Fin r → E)} (hB : IsConjAdj B) :
    (∀ a b, cc (skewGram ξ0 B a b) = skewGram ξ0 B b a) ↔ B.IsAlt := by
  rw [← traceFormBilin_isAlt_iff h0 hξ, traceFormBilin_skewGram h0 hB]

theorem skewGram_det_ne_zero_iff {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) : (skewGram ξ0 B).det ≠ 0 ↔ B.Nondegenerate := by
  rw [← traceFormBilin_nondegenerate_iff h0, traceFormBilin_skewGram h0 hB]

theorem existsUnique_herm_EFf {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {B : LinearMap.BilinForm ℚ (Fin r → E)} (hB : IsConjAdj B) (halt : B.IsAlt) :
    ∃! G : Matrix (Fin r) (Fin r) E,
      (∀ a b, cc (G a b) = G b a) ∧ ∀ x y, B x y = EFf ξ0 G x y :=
  ⟨skewGram ξ0 B, ⟨skewGram_herm h0 hξ hB halt, fun x y => (EFf_skewGram h0 hB x y).symm⟩,
    fun _ hG => eq_skewGram h0 hG.2⟩

def hermEquivSkew {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    {G : Matrix (Fin r) (Fin r) E // ∀ a b, cc (G a b) = G b a} ≃
      {B : LinearMap.BilinForm ℚ (Fin r → E) // IsConjAdj B ∧ B.IsAlt} where
  toFun G := ⟨traceFormBilin ξ0 G.1, traceFormBilin_isConjAdj _ _, traceFormBilin_isAlt hξ G.2⟩
  invFun B := ⟨skewGram ξ0 B.1, skewGram_herm h0 hξ B.2.1 B.2.2⟩
  left_inv G := Subtype.ext (skewGram_traceFormBilin h0 G.1)
  right_inv B := Subtype.ext (traceFormBilin_skewGram h0 B.2.1)

theorem preserves_iff_herm {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, B x y = EFf ξ0 G x y) (γ : GL (Fin r) E) :
    (∀ x y, B ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = B x y) ↔
      ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y := by
  simp only [hG]
  exact EFf_mulVec_iff h0 G G γ

omit [IsCMField E] in

theorem smul_skewGram_mul {c : E} (hc : c ≠ 0) (ξ0 : E) (B : LinearMap.BilinForm ℚ (Fin r → E)) :
    c • skewGram (c * ξ0) B = skewGram ξ0 B := by
  ext a b
  simp only [skewGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← mul_neg,
    _root_.mul_inv_rev]
  rw [mul_comm _ c⁻¹, mul_assoc, mul_inv_cancel_left₀ hc]

section Integral

variable {M M' : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup M'] [Module (𝓞 E) M']

def IsIntConjAdj (E : Type) [Field E] [NumberField E] [IsCMField E] {M : Type} [AddCommGroup M]
    [Module (𝓞 E) M] (β : LinearMap.BilinForm ℤ M) : Prop :=
  ∀ (a : 𝓞 E) (x y : M), β (a • x) y = β x (IsCMField.ringOfIntegersComplexConj E a • y)

theorem coe_ringOfIntegersComplexConj (a : 𝓞 E) :
    ((IsCMField.ringOfIntegersComplexConj E a : 𝓞 E) : E) = cc (a : E) :=
  IsCMField.coe_ringOfIntegersComplexConj E a

namespace IsLatticeEmb

variable {φ : M →ₗ[𝓞 E] (Fin r → E)}

theorem extend_isConjAdj (h : IsLatticeEmb φ) {β : LinearMap.BilinForm ℤ M}
    (hβ : IsIntConjAdj E β) : IsConjAdj (h.extend β) := by
  intro a v w
  obtain ⟨m, hm, x, hx⟩ := h.exists_zsmul v
  obtain ⟨n, hn, y, hy⟩ := h.exists_zsmul w
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hint⟩ := halg.exists_integral_multiple
  let α : 𝓞 E := ⟨k • a, hint⟩
  have hα : (α : E) = k • a := rfl
  have h1 : φ (α • x) = k • m • a • v := by
    rw [map_smul, ← algebraMap_smul E α, hx, smul_comm m a v, ← smul_assoc k]; rfl
  have h2 : φ (IsCMField.ringOfIntegersComplexConj E α • y) = k • n • cc a • w := by
    rw [map_smul, ← algebraMap_smul E (IsCMField.ringOfIntegersComplexConj E α), hy,
      smul_comm n (cc a) w, ← smul_assoc k]
    congr 1
    change ((IsCMField.ringOfIntegersComplexConj E α : 𝓞 E) : E) = _
    rw [coe_ringOfIntegersComplexConj, hα, zsmul_eq_mul, zsmul_eq_mul, cc_mul, cc_intCast]
  have h3 : h.extend β (φ (α • x)) (φ y) =
      h.extend β (φ x) (φ (IsCMField.ringOfIntegersComplexConj E α • y)) := by
    rw [extend_apply, extend_apply, hβ]
  simp only [h1, h2, hx, hy, map_zsmul, LinearMap.smul_apply] at h3
  rw [smul_comm k n] at h3
  exact smul_right_injective ℚ hm (smul_right_injective ℚ hk (smul_right_injective ℚ hn h3))

def gram (h : IsLatticeEmb φ) (ξ0 : E) (β : LinearMap.BilinForm ℤ M) : Matrix (Fin r) (Fin r) E :=
  skewGram ξ0 (h.extend β)

theorem EFf_gram (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    (hβ : IsIntConjAdj E β) (x y : M) : EFf ξ0 (h.gram ξ0 β) (φ x) (φ y) = β x y := by
  rw [gram, EFf_skewGram h0 (h.extend_isConjAdj hβ), extend_apply]

theorem eq_gram (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    G = h.gram ξ0 β := by
  have : h.extend β = traceFormBilin ξ0 G := h.bilin_ext fun x y => by rw [extend_apply, traceFormBilin_apply, hG]
  rw [gram, this, skewGram_traceFormBilin h0]

theorem gram_herm (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {β : LinearMap.BilinForm ℤ M} (hβ : IsIntConjAdj E β) (halt : ∀ x, β x x = 0) (a b : Fin r) :
    cc (h.gram ξ0 β a b) = h.gram ξ0 β b a :=
  skewGram_herm h0 hξ (h.extend_isConjAdj hβ) (h.extend_isAlt halt) a b

theorem gram_det_ne_zero_iff (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0)
    {β : LinearMap.BilinForm ℤ M} (hβ : IsIntConjAdj E β) :
    (h.gram ξ0 β).det ≠ 0 ↔ Function.Injective β := by
  rw [gram, skewGram_det_ne_zero_iff h0 (h.extend_isConjAdj hβ), extend_nondegenerate_iff]

theorem EF_int_of_eq {ξ0 : E} {β : LinearMap.BilinForm ℤ M} {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    ∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ, ∃ k : ℤ, EFf ξ0 G x y = k := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact ⟨β x y, hG x y⟩

theorem EF_perf_iff (h : IsLatticeEmb φ) {ξ0 : E} {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    (∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
      (f y : ℚ) = EFf ξ0 G x y) ↔ Function.Surjective β := by
  let e := LinearEquiv.ofInjective φ h.1
  have he : ∀ x, ((e x : LinearMap.range φ) : Fin r → E) = φ x := fun x => rfl
  constructor
  · intro hp f
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hp (f.toAddMonoidHom.comp e.symm.toAddEquiv.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => ?_⟩
    have := hx (e y)
    rw [he, hG] at this
    simpa using this.symm
  · intro hs f
    obtain ⟨x, hx⟩ := hs (f.comp e.toAddEquiv.toAddMonoidHom).toIntLinearMap
    refine ⟨φ x, ⟨x, rfl⟩, fun y => ?_⟩
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [he, hG, hx]
    rfl

theorem gram_eq_of_mulVec {s : ℕ} {φ' : M' →ₗ[𝓞 E] (Fin s → E)} (h : IsLatticeEmb φ)
    (h' : IsLatticeEmb φ') {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {β' : LinearMap.BilinForm ℤ M'} (hβ' : IsIntConjAdj E β') {g : M → M'}
    (hg : ∀ x y, β' (g x) (g y) = β x y) {γ : Matrix (Fin s) (Fin r) E}
    (hγ : ∀ x, γ *ᵥ φ x = φ' (g x)) : h.gram ξ0 β = γᵀ * h'.gram ξ0 β' * γ.map cc := by
  refine (h.eq_gram h0 fun x y => ?_).symm
  rw [← hg, ← h'.EFf_gram h0 hβ', ← hγ, ← hγ, EFf, EFf, herm_mulVec]

theorem isUStab_iff (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) (γ : GL (Fin r) E) :
    IsUStab G (LinearMap.range φ) γ ↔
      ∃ g : M ≃ₗ[𝓞 E] M, (∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ x = φ (g x)) ∧
        ∀ x y, β (g x) (g y) = β x y := by
  have hinj : Function.Injective (γ : Matrix (Fin r) (Fin r) E).mulVec :=
    mulVec_injective_iff_isUnit.mpr γ.isUnit
  constructor
  · rintro ⟨hu, hs⟩
    have h2 := h.comp_GL γ
    have hr : LinearMap.range (((γ : Matrix (Fin r) (Fin r) E).mulVecLin.restrictScalars (𝓞 E)) ∘ₗ φ)
        = LinearMap.range φ := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact (hs _).mp ⟨x, rfl⟩
      · intro hv
        obtain ⟨w, rfl⟩ := mulVec_surjective_iff_isUnit.mpr γ.isUnit v
        obtain ⟨x, rfl⟩ := (hs w).mpr hv
        exact ⟨x, rfl⟩
    let g : M ≃ₗ[𝓞 E] M := (LinearEquiv.ofInjective _ h2.1).trans
      ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective φ h.1).symm)
    have hg : ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ x = φ (g x) := fun x => by
      simp only [g, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
      rfl
    refine ⟨g, hg, fun x y => ?_⟩
    have : ((β (g x) (g y) : ℤ) : ℚ) = β x y := by rw [← hG, ← hG, ← hg, ← hg, EFf, EFf, hu]
    exact_mod_cast this
  · rintro ⟨g, hg, hβ⟩
    refine ⟨(EFf_mulVec_iff h0 G G _).mp fun v w => ?_, fun v => ⟨?_, ?_⟩⟩
    · have : traceFormBilin ξ0 ((γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc)
          = traceFormBilin ξ0 G := h.bilin_ext fun x y => by
        rw [traceFormBilin_apply, traceFormBilin_apply, EFf, ← herm_mulVec, hg, hg, ← EFf, hG, hG, hβ]
      rw [EFf, herm_mulVec, ← EFf, ← traceFormBilin_apply, this, traceFormBilin_apply]
    · rintro ⟨x, rfl⟩
      exact ⟨g x, (hg x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨g.symm x, hinj ?_⟩
      rw [hg, g.apply_symm_apply, hx]

end IsLatticeEmb

def latticeEF (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k) : LinearMap.BilinForm ℤ Λ :=
  have key : ∀ x y : Λ, (((EFf ξ0 G x y).num : ℤ) : ℚ) = traceFormBilin ξ0 G x y := fun x y => by
    obtain ⟨k, hk⟩ := hint x x.2 y y.2
    rw [traceFormBilin_apply, hk, Rat.num_intCast]
  LinearMap.mk₂ ℤ (fun x y => (EFf ξ0 G x y).num)
    (fun x x' y => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun n x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, key, key, Submodule.coe_smul_of_tower, map_zsmul,
        LinearMap.smul_apply, zsmul_eq_mul]))
    (fun x y y' => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add]))
    (fun n x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, key, key, Submodule.coe_smul_of_tower, map_zsmul,
        zsmul_eq_mul]))

section LatticeEF

variable {ξ0 : E} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
  (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k)

theorem latticeEF_apply (x y : Λ) : ((latticeEF ξ0 G Λ hint x y : ℤ) : ℚ) = EFf ξ0 G x y := by
  obtain ⟨k, hk⟩ := hint x x.2 y y.2
  change (((EFf ξ0 G x y).num : ℤ) : ℚ) = _
  rw [hk, Rat.num_intCast]

theorem latticeEF_isIntConjAdj : IsIntConjAdj E (latticeEF ξ0 G Λ hint) := fun a x y =>
  Int.cast_injective (α := ℚ) (by
    rw [latticeEF_apply, latticeEF_apply, Submodule.coe_smul, Submodule.coe_smul,
      ← algebraMap_smul E a, ← algebraMap_smul E (IsCMField.ringOfIntegersComplexConj E a),
      EFf_smul_left, ← coe_ringOfIntegersComplexConj])

theorem latticeEF_self (hξ : cc ξ0 = -ξ0) (hG : ∀ a b, cc (G a b) = G b a) (x : Λ) :
    latticeEF ξ0 G Λ hint x x = 0 :=
  Int.cast_injective (α := ℚ) (by rw [latticeEF_apply, EFf_self hξ hG, Int.cast_zero])

theorem gram_latticeEF (hΛ : IsLattice Λ) (h0 : ξ0 ≠ 0) :
    (isLatticeEmb_subtype hΛ).gram ξ0 (latticeEF ξ0 G Λ hint) = G :=
  ((isLatticeEmb_subtype hΛ).eq_gram h0 fun x y => (latticeEF_apply hint x y).symm).symm

theorem latticeEF_bijective_iff (hΛ : IsLattice Λ) (h0 : ξ0 ≠ 0) :
    Function.Bijective (latticeEF ξ0 G Λ hint) ↔
      G.det ≠ 0 ∧ ∀ f : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (f y : ℚ) = EFf ξ0 G x y := by
  have h := isLatticeEmb_subtype hΛ
  have h1 := h.gram_det_ne_zero_iff h0 (latticeEF_isIntConjAdj hint)
  rw [gram_latticeEF hint hΛ h0] at h1
  have h2 := h.EF_perf_iff (ξ0 := ξ0) (G := G) fun x y => (latticeEF_apply hint x y).symm
  rw [Submodule.range_subtype] at h2
  rw [h1, h2]
  rfl

end LatticeEF

theorem exists_lattice_EFf [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M]
    (hr : Module.finrank (𝓞 E) M = r) {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {β : LinearMap.BilinForm ℤ M} (halt : ∀ x, β x x = 0) (hβ : IsIntConjAdj E β)
    (hu : Function.Bijective β) :
    ∃ (φ : M →ₗ[𝓞 E] (Fin r → E)) (G : Matrix (Fin r) (Fin r) E),
      Function.Injective φ ∧ IsLattice (LinearMap.range φ) ∧ (∀ a b, cc (G a b) = G b a) ∧
      G.det ≠ 0 ∧ (∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) ∧
      (∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ, ∃ k : ℤ, EFf ξ0 G x y = k) ∧
      ∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
        (f y : ℚ) = EFf ξ0 G x y := by
  obtain ⟨φ, h⟩ := exists_isLatticeEmb (K := E) hr
  exact ⟨φ, h.gram ξ0 β, h.1, h.2, h.gram_herm h0 hξ hβ halt, (h.gram_det_ne_zero_iff h0 hβ).mpr hu.1,
    h.EFf_gram h0 hβ, IsLatticeEmb.EF_int_of_eq (h.EFf_gram h0 hβ),
    (h.EF_perf_iff (h.EFf_gram h0 hβ)).mpr hu.2⟩

end Integral

section Datum

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {H : Host E}

theorem host_bar_eq (H : Host E) (a : 𝓞 E) : H.bar a = IsCMField.ringOfIntegersComplexConj E a :=
  RingOfIntegers.ext (H.bar_eq a)

theorem datum_isIntConjAdj (D : Datum H) : IsIntConjAdj E D.EF := fun a x y => by
  rw [D.adj, host_bar_eq]

theorem datum_exists_isLatticeEmb (D : Datum H) :
    ∃ φ : D.La →ₗ[𝓞 E] (Fin (D.p + D.q) → E), IsLatticeEmb φ := by
  have := D.fin
  have := D.proj
  exact exists_isLatticeEmb D.rank

def datumEmb (D : Datum H) : D.La →ₗ[𝓞 E] (Fin (D.p + D.q) → E) :=
  (datum_exists_isLatticeEmb D).choose

theorem datumEmb_isLatticeEmb (D : Datum H) : IsLatticeEmb (datumEmb D) :=
  (datum_exists_isLatticeEmb D).choose_spec

abbrev datumLat (D : Datum H) : Submodule (𝓞 E) (Fin (D.p + D.q) → E) :=
  LinearMap.range (datumEmb D)

theorem datumLat_isLattice (D : Datum H) : IsLattice (datumLat D) := (datumEmb_isLatticeEmb D).2

def datumEquivLat (D : Datum H) : D.La ≃ₗ[𝓞 E] datumLat D :=
  LinearEquiv.ofInjective _ (datumEmb_isLatticeEmb D).1

@[simp] theorem coe_datumEquivLat (D : Datum H) (x : D.La) :
    (datumEquivLat D x : Fin (D.p + D.q) → E) = datumEmb D x := rfl

def datumGram (D : Datum H) (ξ0 : E) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) E :=
  (datumEmb_isLatticeEmb D).gram ξ0 D.EF

theorem datum_gram_spec (D : Datum H) {φ : D.La →ₗ[𝓞 E] (Fin r → E)} (h : IsLatticeEmb φ)
    {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    (∀ a b, cc (h.gram ξ0 D.EF a b) = h.gram ξ0 D.EF b a) ∧ (h.gram ξ0 D.EF).det ≠ 0 ∧
      (∀ x y, EFf ξ0 (h.gram ξ0 D.EF) (φ x) (φ y) = D.EF x y) ∧
      (∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
        ∃ k : ℤ, EFf ξ0 (h.gram ξ0 D.EF) x y = k) ∧
      ∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
        (f y : ℚ) = EFf ξ0 (h.gram ξ0 D.EF) x y :=
  have hβ := datum_isIntConjAdj D
  ⟨h.gram_herm h0 hξ hβ D.alt, (h.gram_det_ne_zero_iff h0 hβ).mpr D.unimod.1, h.EFf_gram h0 hβ,
    IsLatticeEmb.EF_int_of_eq (h.EFf_gram h0 hβ),
    (h.EF_perf_iff (h.EFf_gram h0 hβ)).mpr D.unimod.2⟩

theorem datum_exists_lattice_EFf (D : Datum H) {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    ∃ (Λ : Submodule (𝓞 E) (Fin (D.p + D.q) → E)) (e : D.La ≃ₗ[𝓞 E] Λ)
      (G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) E),
      IsLattice Λ ∧ (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      (∀ x y, EFf ξ0 G (e x) (e y) = D.EF x y) ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k) ∧
      ∀ f : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (f y : ℚ) = EFf ξ0 G x y :=
  ⟨datumLat D, datumEquivLat D, datumGram D ξ0, datumLat_isLattice D,
    datum_gram_spec D (datumEmb_isLatticeEmb D) h0 hξ⟩

theorem datum_rank_eq (D : Datum H) {φ : D.La →ₗ[𝓞 E] (Fin r → E)} (h : IsLatticeEmb φ) :
    r = D.p + D.q := by rw [← h.finrank_eq, D.rank]

section
variable (D : Datum H) {ξ0 : E}

theorem datumGram_herm (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) (a b : Fin (D.p + D.q)) :
    cc (datumGram D ξ0 a b) = datumGram D ξ0 b a :=
  (datum_gram_spec D (datumEmb_isLatticeEmb D) h0 hξ).1 a b

theorem datumGram_det_ne_zero (h0 : ξ0 ≠ 0) : (datumGram D ξ0).det ≠ 0 :=
  ((datumEmb_isLatticeEmb D).gram_det_ne_zero_iff h0 (datum_isIntConjAdj D)).mpr D.unimod.1

theorem EFf_datumGram (h0 : ξ0 ≠ 0) (x y : D.La) :
    EFf ξ0 (datumGram D ξ0) (datumEmb D x) (datumEmb D y) = D.EF x y :=
  (datumEmb_isLatticeEmb D).EFf_gram h0 (datum_isIntConjAdj D) x y

theorem eq_datumGram (h0 : ξ0 ≠ 0) {G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) E}
    (hG : ∀ x y, EFf ξ0 G (datumEmb D x) (datumEmb D y) = D.EF x y) : G = datumGram D ξ0 :=
  (datumEmb_isLatticeEmb D).eq_gram h0 hG

theorem datum_EF_int (h0 : ξ0 ≠ 0) :
    ∀ x ∈ datumLat D, ∀ y ∈ datumLat D, ∃ k : ℤ, EFf ξ0 (datumGram D ξ0) x y = k :=
  IsLatticeEmb.EF_int_of_eq (EFf_datumGram D h0)

theorem datum_EF_perf (h0 : ξ0 ≠ 0) : ∀ f : datumLat D →+ ℤ, ∃ x ∈ datumLat D,
    ∀ y : datumLat D, (f y : ℚ) = EFf ξ0 (datumGram D ξ0) x y :=
  ((datumEmb_isLatticeEmb D).EF_perf_iff (EFf_datumGram D h0)).mpr D.unimod.2

theorem traceFormDual_datumLat (h0 : ξ0 ≠ 0) :
    traceFormDual ξ0 (datumGram D ξ0) (datumLat D) = datumLat D :=
  (perfect_iff_traceFormDual_eq h0 (datumGram_det_ne_zero D h0) (datumLat_isLattice D)).mp
    ⟨datum_EF_int D h0, datum_EF_perf D h0⟩

theorem datum_isUStab_iff (h0 : ξ0 ≠ 0) (γ : GL (Fin (D.p + D.q)) E) :
    IsUStab (datumGram D ξ0) (datumLat D) γ ↔
      ∃ g : D.La ≃ₗ[𝓞 E] D.La,
        (∀ x, (γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) E) *ᵥ datumEmb D x = datumEmb D (g x)) ∧
        ∀ x y, D.EF (g x) (g y) = D.EF x y :=
  (datumEmb_isLatticeEmb D).isUStab_iff h0 (EFf_datumGram D h0) γ

end

end Datum

namespace SkewModel

def ConjDual (E : Type) [Field E] [NumberField E] [IsCMField E] : Type := Module.Dual ℤ (𝓞 E)

namespace ConjDual

instance : AddCommGroup (ConjDual E) := inferInstanceAs (AddCommGroup (Module.Dual ℤ (𝓞 E)))

def val : ConjDual E ≃ₗ[ℤ] Module.Dual ℤ (𝓞 E) := (AddEquiv.refl _).toIntLinearEquiv

instance : SMul (𝓞 E) (ConjDual E) where
  smul a f := val.symm (val f ∘ₗ LinearMap.mulLeft ℤ (IsCMField.ringOfIntegersComplexConj E a))

@[simp] theorem val_smul (a : 𝓞 E) (f : ConjDual E) (x : 𝓞 E) :
    val (a • f) x = val f (IsCMField.ringOfIntegersComplexConj E a * x) := rfl

@[ext] theorem ext {f g : ConjDual E} (h : ∀ x, val f x = val g x) : f = g :=
  val.injective (LinearMap.ext h)

instance : Module (𝓞 E) (ConjDual E) where
  one_smul f := ext fun x => by simp
  mul_smul a b f := ext fun x => by simp only [val_smul, map_mul]; congr 1; ring
  smul_zero a := ext fun x => by simp
  smul_add a f g := ext fun x => by simp
  add_smul a b f := ext fun x => by simp [add_mul]
  zero_smul f := ext fun x => by simp

instance : Module.Finite ℤ (ConjDual E) := Module.Finite.equiv val.symm

instance : Module.Finite (𝓞 E) (ConjDual E) := Module.Finite.of_restrictScalars_finite ℤ _ _

instance : Module.IsTorsionFree (𝓞 E) (ConjDual E) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a f h
  refine or_iff_not_imp_left.mpr fun ha => ext fun x => ?_
  have ha' : IsCMField.ringOfIntegersComplexConj E a ≠ 0 := by simpa using ha
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ)
    (IsCMField.ringOfIntegersComplexConj E a)).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha')
  have h1 : val (a • f) (c * x) = 0 := by rw [h]; simp
  rw [val_smul, ← mul_assoc, ← hc, ← Algebra.smul_def, map_smul, smul_eq_mul] at h1
  simpa [hn] using h1

end ConjDual

def hypForm (E : Type) [Field E] [NumberField E] [IsCMField E] :
    LinearMap.BilinForm ℤ (𝓞 E × ConjDual E) :=
  LinearMap.mk₂ ℤ (fun u v => ConjDual.val v.2 u.1 - ConjDual.val u.2 v.1)
    (fun u u' v => by simp; ring) (fun n u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, LinearMap.smul_apply, smul_sub])
    (fun u v v' => by simp; ring) (fun n u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, LinearMap.smul_apply, smul_sub])

@[simp] theorem hypForm_apply (u v : 𝓞 E × ConjDual E) :
    hypForm E u v = ConjDual.val v.2 u.1 - ConjDual.val u.2 v.1 := rfl

theorem hypForm_self (u : 𝓞 E × ConjDual E) : hypForm E u u = 0 := by simp

theorem hypForm_isIntConjAdj : IsIntConjAdj E (hypForm E) := fun a u v => by
  have : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E a) = a :=
    RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (a : E))
  simp [this]

theorem hypForm_bijective : Function.Bijective (hypForm E) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x, f⟩ h
    refine Prod.ext ?_ (ConjDual.ext fun y => ?_)
    · refine (Module.forall_dual_apply_eq_zero_iff ℤ x).mp fun g => ?_
      simpa using LinearMap.congr_fun h (0, ConjDual.val.symm g)
    · simpa using LinearMap.congr_fun h (y, 0)
  · intro F
    obtain ⟨x, hx⟩ := (Module.bijective_dual_eval ℤ (𝓞 E)).2
      (F ∘ₗ LinearMap.inr ℤ _ _ ∘ₗ ConjDual.val.symm.toLinearMap)
    refine ⟨(x, ConjDual.val.symm (-(F ∘ₗ LinearMap.inl ℤ _ _))), LinearMap.ext fun v => ?_⟩
    have h1 := LinearMap.congr_fun hx (ConjDual.val v.2)
    have h2 : F v = F (v.1, 0) + F (0, v.2) := by rw [← map_add]; simp
    simp only [Module.Dual.eval_apply] at h1
    simp [h1, h2, add_comm]

theorem finrank_hyp : Module.finrank (𝓞 E) (𝓞 E × ConjDual E) = 2 := by
  obtain ⟨φ, h⟩ := exists_isLatticeEmb (K := E) (M := 𝓞 E × ConjDual E) rfl
  have h1 := h.finrank_int_eq
  have : Module.Free ℤ (ConjDual E) := Module.Free.of_equiv ConjDual.val.symm
  rw [Module.finrank_prod, ConjDual.val.finrank_eq, Module.finrank_linearMap_self,
    RingOfIntegers.rank, ← two_mul] at h1
  exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1).symm

theorem exists_perfect_lattice_rank_two {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    ∃ (Λ : Submodule (𝓞 E) (Fin 2 → E)) (G : Matrix (Fin 2) (Fin 2) E),
      IsLattice Λ ∧ (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k) ∧
      ∀ f : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (f y : ℚ) = EFf ξ0 G x y := by
  obtain ⟨φ, G, -, h1, h2, h3, -, h4, h5⟩ := exists_lattice_EFf finrank_hyp h0 hξ
    hypForm_self hypForm_isIntConjAdj hypForm_bijective
  exact ⟨_, G, h1, h2, h3, h4, h5⟩

end SkewModel

example {ξ0 : E} (hξ : cc ξ0 = -ξ0) (d : ℚ) (hd : ξ0 ^ 2 = -algebraMap ℚ E d) :
    EFf ξ0 (1 : Matrix (Fin 1) (Fin 1) E) ![1] ![ξ0] = -(d * Module.finrank ℚ E) ∧
      EFf ξ0 (1 : Matrix (Fin 1) (Fin 1) E) ![ξ0] ![1] = d * Module.finrank ℚ E := by
  constructor
  · have : -ξ0 * (1 * -ξ0) = -algebraMap ℚ E d := by rw [← hd]; ring
    rw [EFf, herm_one, Matrix.cons_val_zero, Matrix.cons_val_zero, hξ, this, map_neg,
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm]
  · have : -ξ0 * (ξ0 * 1) = algebraMap ℚ E d := by rw [← neg_inj, ← hd]; ring
    rw [EFf, herm_one, Matrix.cons_val_zero, Matrix.cons_val_zero, cc_one, this,
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm]

example : ∃ (ξ0 : E) (B : LinearMap.BilinForm ℚ (Fin r → E)), ξ0 ≠ 0 ∧ cc ξ0 = -ξ0 ∧
    IsConjAdj B ∧ B.IsAlt ∧ B.Nondegenerate ∧ skewGram ξ0 B = 1 := by
  obtain ⟨ξ0, hξ, h0⟩ := exists_imag (E := E)
  refine ⟨ξ0, traceFormBilin ξ0 1, h0, hξ, traceFormBilin_isConjAdj _ _, traceFormBilin_isAlt hξ fun a b => ?_,
    (traceFormBilin_nondegenerate_iff h0 _).mpr (by simp), skewGram_traceFormBilin h0 _⟩
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

example : ¬ (traceFormBilin (1 : E) (1 : Matrix (Fin 1) (Fin 1) E)).IsAlt := by
  intro h
  have h1 := h ![1]
  have : -(1 : E) * (1 * 1) = -algebraMap ℚ E 1 := by simp
  rw [traceFormBilin_apply, EFf, herm_one, Matrix.cons_val_zero, cc_one, this, map_neg,
    Algebra.trace_algebraMap] at h1
  have := Module.finrank_pos (R := ℚ) (M := E)
  simp at h1
  omega

example : ¬ IsConjAdj ((Algebra.traceForm ℚ E).compl₁₂ (LinearMap.proj (0 : Fin 1))
    (LinearMap.proj (φ := fun _ : Fin 1 => E) (0 : Fin 1))) := by
  intro h
  obtain ⟨ξ0, hξ, h0⟩ := exists_imag (E := E)
  have : ξ0 + ξ0 = 0 := eq_zero_of_forall_trace_mul fun a => by
    have h1 := h ξ0 ![a] ![1]
    simp only [LinearMap.compl₁₂_apply, LinearMap.proj_apply, Algebra.traceForm_apply,
      Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, hξ, mul_one, map_neg] at h1
    rw [mul_add, map_add]
    rw [mul_comm ξ0 a] at h1
    linarith
  exact h0 (by linear_combination this / 2)

end GlobalTheory
