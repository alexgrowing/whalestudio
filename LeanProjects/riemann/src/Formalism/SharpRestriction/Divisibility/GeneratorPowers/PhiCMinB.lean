import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinA
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def comp (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a : Y) : ℂ :=
  ∑ i, (η (RingOfIntegers.basis E i • a) : ℂ) * σ (ed E i)

theorem comp_add (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a b : Y) :
    comp η σ (a + b) = comp η σ a + comp η σ b := by
  simp only [comp, smul_add, map_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

theorem comp_fadd (η ζ : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a : Y) :
    comp (η + ζ) σ a = comp η σ a + comp ζ σ a := by
  simp only [comp, LinearMap.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

theorem comp_fsmul (r : ℝ) (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (a : Y) :
    comp (r • η) σ a = r * comp η σ a := by
  simp only [comp, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def compL (σ : E →+* ℂ) (a : Y) : (Y →ₗ[ℤ] ℝ) →ₗ[ℝ] ℂ where
  toFun η := comp η σ a
  map_add' η ζ := comp_fadd η ζ σ a
  map_smul' r η := by rw [comp_fsmul, RingHom.id_apply, Complex.real_smul]

theorem compL_apply (σ : E →+* ℂ) (a : Y) (η : Y →ₗ[ℤ] ℝ) : compL σ a η = comp η σ a := rfl

theorem key_exp (u : 𝓞 E) (j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∑ i, (((RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * u) j : ℤ) : E) * ed E i =
      ed E j * (u : E) := by
  conv_rhs => rw [← (ed E).sum_repr (ed E j * (u : E))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (ed E).repr (ed E j * (u : E)) i
      = ((RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * u) j : ℚ) := by
    rw [ed, LinearMap.BilinForm.dualBasis_repr_apply, ← ed, Algebra.traceForm_apply,
      ← tr_ed_int, integralBasis_apply]
    congr 1
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring
  rw [hr, Algebra.smul_def]
  simp

theorem smul_expand (u : 𝓞 E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) (a : Y) :
    RingOfIntegers.basis E i • u • a = ∑ j, (RingOfIntegers.basis E).repr
      (RingOfIntegers.basis E i * u) j • (RingOfIntegers.basis E j • a) := by
  rw [← mul_smul]
  conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (RingOfIntegers.basis E i * u)]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => smul_assoc _ _ _

theorem comp_smul (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (u : 𝓞 E) (a : Y) :
    comp η σ (u • a) = σ (u : E) * comp η σ a := by
  have hk : ∀ j, ∑ i, (((RingOfIntegers.basis E).repr (RingOfIntegers.basis E i * u) j : ℤ) : ℂ)
      * σ (ed E i) = σ (ed E j) * σ (u : E) := fun j => by
    have := congrArg σ (key_exp u j)
    simpa [map_sum, map_mul, map_intCast] using this
  unfold comp
  simp_rw [smul_expand u _ a, map_sum, map_zsmul, zsmul_eq_mul]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, mul_comm (σ (u : E)), ← hk j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_comp (η : Y →ₗ[ℤ] ℝ) (a : Y) : ∑ σ : E →+* ℂ, comp η σ a = (η a : ℂ) := by
  have htr : ∀ x : E, ∑ σ : E →+* ℂ, σ x = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by
    intro x
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun σ => rfl)
  have h1 : ∑ i, (RingOfIntegers.basis E).repr 1 i • (RingOfIntegers.basis E i • a) = a := by
    simp_rw [← smul_assoc, ← Finset.sum_smul, (RingOfIntegers.basis E).sum_repr, one_smul]
  have htr1 : ∀ i, Algebra.trace ℚ E (ed E i) = ((RingOfIntegers.basis E).repr 1 i : ℚ) := fun i => by
    rw [← tr_ed_int]; simp
  unfold comp
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, htr, htr1]
  conv_rhs => rw [← h1]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Rat.cast_intCast]
  exact Finset.sum_congr rfl fun i _ => by ring

def smulZ (u : 𝓞 E) : Y →ₗ[ℤ] Y where
  toFun y := u • y
  map_add' := smul_add u
  map_smul' n y := smul_comm u n y

theorem comp_pre (η : Y →ₗ[ℤ] ℝ) (σ : E →+* ℂ) (u : 𝓞 E) (a : Y) :
    comp (η ∘ₗ smulZ u) σ a = σ (u : E) * comp η σ a := by
  rw [← comp_smul]
  unfold comp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.comp_apply, smulZ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [smul_comm]

variable (E) in

def Pf (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) : ℝ :=
  (∑ σ : E →+* ℂ, (comp η σ a * conj (comp ζ σ c) + comp ζ σ a * conj (comp η σ c))).re

theorem Pf_add_left (η ζ : Y →ₗ[ℤ] ℝ) (a b c : Y) :
    Pf E η ζ (a + b) c = Pf E η ζ a c + Pf E η ζ b c := by
  simp only [Pf, comp_add, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_add_right (η ζ : Y →ₗ[ℤ] ℝ) (a b c : Y) :
    Pf E η ζ a (b + c) = Pf E η ζ a b + Pf E η ζ a c := by
  simp only [Pf, comp_add, map_add, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_symm (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) : Pf E η ζ a c = Pf E η ζ c a := by
  simp only [Pf, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_comm (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) : Pf E η ζ a c = Pf E ζ η a c := by
  simp only [Pf, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_fadd (η η' ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    Pf E (η + η') ζ a c = Pf E η ζ a c + Pf E η' ζ a c := by
  simp only [Pf, comp_fadd, map_add, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_fsmul (r : ℝ) (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    Pf E (r • η) ζ a c = r * Pf E η ζ a c := by
  simp only [Pf, comp_fsmul, map_mul, Complex.conj_ofReal, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_self (η : Y →ₗ[ℤ] ℝ) (a : Y) :
    Pf E η η a a = 2 * ∑ σ : E →+* ℂ, Complex.normSq (comp η σ a) := by
  simp only [Pf, Complex.re_sum, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem Pf_self_nonneg (η : Y →ₗ[ℤ] ℝ) (a : Y) : 0 ≤ Pf E η η a a := by
  rw [Pf_self]
  exact mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

section Forms

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem Pf_bal (η ζ : Y →ₗ[ℤ] ℝ) (c c' : 𝓞 E) (h : (c' : E) = cj (c : E)) (a b : Y) :
    Pf E η ζ (c • a) b = Pf E η ζ a (c' • b) := by
  have hs : ∀ σ : E →+* ℂ, conj (σ (c' : E)) = σ (c : E) := fun σ => by
    rw [h, hcj]; simp
  simp only [Pf, comp_smul, map_mul, hs]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring

omit hcj in
variable (E) in

def PfB (η ζ : Y →ₗ[ℤ] ℝ) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun c => Pf E η ζ a c)
      (Pf_add_right η ζ a)).toIntLinearMap)
    (fun a b => LinearMap.ext fun c => Pf_add_left η ζ a b c)).toIntLinearMap

theorem PfB_mem (η ζ : Y →ₗ[ℤ] ℝ) : PfB E η ζ ∈ SymB cj Y :=
  ⟨fun a b => Pf_symm η ζ a b, fun c c' h a b => Pf_bal hcj η ζ c c' h a b⟩

def Pm : (Y →ₗ[ℤ] ℝ) →ₗ[ℝ] (Y →ₗ[ℤ] ℝ) →ₗ[ℝ] SymB cj Y :=
  LinearMap.mk₂ ℝ (fun η ζ => ⟨PfB E η ζ, PfB_mem hcj η ζ⟩)
    (fun η η' ζ => Subtype.ext (LinearMap.ext₂ fun a c => Pf_fadd η η' ζ a c))
    (fun r η ζ => Subtype.ext (LinearMap.ext₂ fun a c => Pf_fsmul r η ζ a c))
    (fun η ζ ζ' => Subtype.ext (LinearMap.ext₂ fun a c => by
      show Pf E η (ζ + ζ') a c = Pf E η ζ a c + Pf E η ζ' a c
      rw [Pf_comm, Pf_fadd, Pf_comm η ζ, Pf_comm η ζ']))
    (fun r η ζ => Subtype.ext (LinearMap.ext₂ fun a c => by
      show Pf E η (r • ζ) a c = r * Pf E η ζ a c
      rw [Pf_comm, Pf_fsmul, Pf_comm η ζ]))

theorem Pm_apply (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = Pf E η ζ a c := rfl

theorem Pm_psd (η : Y →ₗ[ℤ] ℝ) (a : Y) :
    0 ≤ ((Pm hcj η η : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a :=
  Pf_self_nonneg η a

theorem Pm_ne_zero {η : Y →ₗ[ℤ] ℝ} (hη : η ≠ 0) : Pm hcj η η ≠ 0 := by
  intro h0
  apply hη
  ext a
  have hP : Pf E η η a a = 0 := by
    have := congrArg (fun β : SymB cj Y => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) h0
    simpa [Pm_apply] using this
  rw [Pf_self] at hP
  have hsum : ∑ σ : E →+* ℂ, Complex.normSq (comp η σ a) = 0 := by linarith
  have hc : ∀ σ : E →+* ℂ, comp η σ a = 0 := fun σ =>
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hsum σ (Finset.mem_univ σ))
  have := sum_comp (E := E) η a
  simp only [hc, Finset.sum_const_zero] at this
  simp only [LinearMap.zero_apply]
  exact_mod_cast this.symm

omit hcj in

theorem Pf_skew (θ : 𝓞 E) (hθ : ∀ σ : E →+* ℂ, star (σ (θ : E)) = -σ (θ : E))
    (η ζ : Y →ₗ[ℤ] ℝ) (a c : Y) :
    Pf E (η ∘ₗ smulZ θ) ζ a c = -Pf E η (ζ ∘ₗ smulZ θ) a c := by
  have hs : ∀ σ : E →+* ℂ, conj (σ (θ : E)) = -σ (θ : E) := hθ
  simp only [Pf, comp_pre, map_mul, hs]
  rw [← Complex.neg_re, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => by ring

end Forms

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
