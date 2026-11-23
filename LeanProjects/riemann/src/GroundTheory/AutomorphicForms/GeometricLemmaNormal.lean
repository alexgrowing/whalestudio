import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaUnnormalized
import GroundTheory.AutomorphicForms.GeometricLemmaCharacters
import GroundTheory.AutomorphicForms.GeometricLemmaModular
import GroundTheory.AutomorphicForms.GeometricLemmaCellChar
import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel
open scoped NNReal

section Pairs

variable {ι : Type*} [Fintype ι]

theorem prod_pow_eq_of_sub_swap (f : ι × ι → ℝ≥0) (hf : ∀ p, f p.swap * f p = 1)
    (A B : ι × ι → ℕ) (hAB : ∀ p, (A p : ℤ) - A p.swap = (B p : ℤ) - B p.swap) :
    ∏ p, f p ^ A p = ∏ p, f p ^ B p := by
  have hf0 : ∀ p, f p ≠ 0 := fun p h => by simpa [h] using hf p
  have hswap : ∀ p, f p.swap = (f p)⁻¹ := fun p => eq_inv_of_mul_eq_one_left (hf p)
  have key : ∀ C : ι × ι → ℕ,
      (∏ p, f p ^ C p) ^ 2 = ∏ p : ι × ι, f p ^ ((C p : ℤ) - C p.swap) := by
    intro C
    have h1 : ∏ p : ι × ι, f p.swap ^ C p.swap = ∏ p, f p ^ C p :=
      Fintype.prod_equiv (Equiv.prodComm ι ι) _ _ fun p => rfl
    rw [sq]
    conv_lhs => arg 2; rw [← h1]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hswap, inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ (hf0 p),
      sub_eq_add_neg]
  have h2 : (∏ p, f p ^ A p) ^ 2 = (∏ p, f p ^ B p) ^ 2 := by
    rw [key, key]
    exact Finset.prod_congr rfl fun p _ => by rw [hAB p]
  rw [← NNReal.sqrt_sq (∏ p, f p ^ A p), h2, NNReal.sqrt_sq]

theorem prod_subtype_eq_prod_pow (P : ι × ι → Prop) [DecidablePred P] (f : ι × ι → ℝ≥0) :
    ∏ s : {p : ι × ι // P p}, f s.1 = ∏ p, f p ^ (if P p then 1 else 0) := by
  rw [← Finset.prod_subtype (Finset.univ.filter P) (by simp) f, Finset.prod_filter]
  refine Finset.prod_congr rfl fun p _ => ?_
  split_ifs <;> simp

end Pairs

section DiagonalIdentity

open Measures

variable {n : ℕ}

def leftExponent (γ δ : Fin n → ℕ) (p : Fin n × Fin n) : ℕ :=
  (if γ p.1 < γ p.2 ∧ δ p.2 < δ p.1 then 1 else 0) * 2 + (if δ p.1 < δ p.2 then 1 else 0) +
    (if δ p.1 = δ p.2 ∧ γ p.1 < γ p.2 then 1 else 0)

def rightExponent (γ δ : Fin n → ℕ) (p : Fin n × Fin n) : ℕ :=
  (if γ p.1 = γ p.2 ∧ δ p.1 < δ p.2 then 1 else 0) + (if γ p.1 < γ p.2 then 1 else 0)

theorem exponent_antisymm (γ δ : Fin n → ℕ) (p : Fin n × Fin n) :
    (leftExponent γ δ p : ℤ) - leftExponent γ δ p.swap =
      (rightExponent γ δ p : ℤ) - rightExponent γ δ p.swap := by
  simp only [leftExponent, rightExponent, Prod.fst_swap, Prod.snd_swap]
  split_ifs <;> omega

theorem prod_character_identity (γ δ : Fin n → ℕ) (m : Fin n → ℝ≥0) (hm : ∀ i, m i ≠ 0) :
    (∏ s : {p : Fin n × Fin n // γ p.1 < γ p.2 ∧ δ p.2 < δ p.1}, m s.1.1 / m s.1.2) ^ 2 *
        (∏ s : {p : Fin n × Fin n // δ p.1 < δ p.2}, m s.1.1 / m s.1.2) *
        (∏ s : {p : Fin n × Fin n // δ p.1 = δ p.2 ∧ γ p.1 < γ p.2}, m s.1.1 / m s.1.2) =
      (∏ s : {p : Fin n × Fin n // γ p.1 = γ p.2 ∧ δ p.1 < δ p.2}, m s.1.1 / m s.1.2) *
        (∏ s : {p : Fin n × Fin n // γ p.1 < γ p.2}, m s.1.1 / m s.1.2) := by
  classical
  set f : Fin n × Fin n → ℝ≥0 := fun p => m p.1 / m p.2
  have hf : ∀ p, f p.swap * f p = 1 := fun p => by
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [div_mul_div_comm, mul_comm (m p.2), div_self (mul_ne_zero (hm _) (hm _))]
  have e : ∀ (P : Fin n × Fin n → Prop) [DecidablePred P],
      ∏ s : {p : Fin n × Fin n // P p}, m s.1.1 / m s.1.2 = ∏ p, f p ^ (if P p then 1 else 0) :=
    fun P _ => prod_subtype_eq_prod_pow P f
  have hL : (∏ s : {p : Fin n × Fin n // γ p.1 < γ p.2 ∧ δ p.2 < δ p.1}, m s.1.1 / m s.1.2) ^ 2 *
        (∏ s : {p : Fin n × Fin n // δ p.1 < δ p.2}, m s.1.1 / m s.1.2) *
        (∏ s : {p : Fin n × Fin n // δ p.1 = δ p.2 ∧ γ p.1 < γ p.2}, m s.1.1 / m s.1.2) =
      ∏ p, f p ^ leftExponent γ δ p := by
    rw [e, e, e, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [leftExponent, ← pow_mul, ← pow_add, ← pow_add]
  have hR : (∏ s : {p : Fin n × Fin n // γ p.1 = γ p.2 ∧ δ p.1 < δ p.2}, m s.1.1 / m s.1.2) *
        (∏ s : {p : Fin n × Fin n // γ p.1 < γ p.2}, m s.1.1 / m s.1.2) =
      ∏ p, f p ^ rightExponent γ δ p := by
    rw [e, e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [rightExponent, ← pow_add]
  rw [hL, hR]
  exact prod_pow_eq_of_sub_swap f hf _ _ (exponent_antisymm γ δ)

end DiagonalIdentity

section Normalized

open MeasureTheory Measure Measures

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

variable (F) in

def normLeviParSqrtModular (γ δ : Fin n → ℕ) : leviPar F n γ δ →* ℂ where
  toFun l := ((NNReal.sqrt (modularCharacter l) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' l l' := by simp [NNReal.sqrt_mul]

variable (F) in

def normLeviParInvSqrtModular (γ δ : Fin n → ℕ) : leviPar F n γ δ →* ℂ where
  toFun l := (normLeviParSqrtModular F γ δ l)⁻¹
  map_one' := by simp
  map_mul' l l' := by rw [map_mul, mul_inv]

variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

variable (β) in

def innerJacquetRep (δ : Fin n → ℕ) :
    Representation ℂ (leviPar F n β δ)
      (Representation.Coinvariants (σ.comp (leviUnipotent F n β δ).subtype)) :=
  twist (normLeviParInvSqrtModular F β δ) (levJacquetAction β σ δ)

variable {γ : Fin n → ℕ} (w : Equiv.Perm (Fin n))

variable (γ) in

def normInducing : Representation ℂ (cellLeviSub F β γ w) (innerJacquetSpace β γ w σ) :=
  twist ((normLeviParSqrtModular F γ (β ∘ w)).comp (cellLeviSubIncl F β γ w))
    ((innerJacquetRep β σ (γ ∘ ⇑w⁻¹)).comp ((cellInnerHom β γ w).comp (cellLeviSubIncl F β γ w)))

end Normalized

section DiagonalValues

open MeasureTheory Measure Measures

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem diagPow_apply_self (μ : Fin n → ℤ) (i : Fin n) :
    ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
      (GLnLocal.uniformizer F : F) ^ μ i := by
  rw [Cartan.coe_diagPow, Matrix.diagonal_apply_eq]

theorem diagPow_apply_ne (μ : Fin n → ℤ) {i j : Fin n} (h : i ≠ j) :
    ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  rw [Cartan.coe_diagPow, Matrix.diagonal_apply_ne _ h]

theorem permGL_conj_diagPow_apply (μ : Fin n → ℤ) (r c : Fin n) :
    ((permGL F w * Cartan.diagPow F n μ * (permGL F w)⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) r c =
      if r = c then (GLnLocal.uniformizer F : F) ^ μ (w⁻¹ r) else 0 := by
  rw [permGL_conj_apply]
  split_ifs with h
  · rw [h, diagPow_apply_self]
  · exact diagPow_apply_ne μ fun e => h (w⁻¹.injective e)

theorem diagPow_mem_blockUpper' {α : Type*} [LinearOrder α] (δ : Fin n → α) (μ : Fin n → ℤ) :
    Cartan.diagPow F n μ ∈ blockUpper F n δ := fun i j hij =>
  diagPow_apply_ne μ fun e => by rw [e] at hij; exact lt_irrefl _ hij

theorem modularCharacter_leviIncl_diagPow (μ : Fin n → ℤ) :
    modularCharacter (leviIncl (⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ : levi F n γ)) =
      ∏ s : {p : Fin n × Fin n // γ p.1 < γ p.2},
        modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) := by
  rw [Measures.modularCharacter_blockUpper_of_mem_borel' _ (fun i j hij => diagPow_apply_ne μ
    (ne_of_gt hij))]
  simp only [leviIncl_coe, diagPow_apply_self]

theorem modularCharacter_permConj_diagPow (μ : Fin n → ℤ) :
    modularCharacter (permConj F β w ⟨Cartan.diagPow F n μ, diagPow_mem_blockUpper' (β ∘ w) μ⟩) =
      ∏ s : {p : Fin n × Fin n // (β ∘ w) p.1 < (β ∘ w) p.2},
        modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) := by
  rw [Measures.modularCharacter_blockUpper_of_mem_borel' _ (fun i j hij => by
    rw [coe_permConj, permGL_conj_diagPow_apply, if_neg (fun h => by simp [h] at hij)])]
  symm
  refine Fintype.prod_equiv (Equiv.subtypeEquiv
    (p := fun q : Fin n × Fin n => (β ∘ w) q.1 < (β ∘ w) q.2) (q := fun q => β q.1 < β q.2)
    (Equiv.prodCongr w w) fun p => Iff.rfl)
    (fun s => modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
      modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2)) _ fun s => ?_
  show modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
      modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) =
    modulus (((permGL F w * Cartan.diagPow F n μ * (permGL F w)⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) (w s.1.1) (w s.1.1)) /
    modulus (((permGL F w * Cartan.diagPow F n μ * (permGL F w)⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) (w s.1.2) (w s.1.2))
  rw [permGL_conj_diagPow_apply, permGL_conj_diagPow_apply, if_pos rfl, if_pos rfl]
  simp

theorem modularCharacter_cellInnerHom_diagPow (μ : Fin n → ℤ) :
    modularCharacter (cellInnerHom β γ w ⟨Cartan.diagPow F n μ,
      diagPow_mem_levi μ, diagPow_mem_blockUpper' (β ∘ w) μ⟩) =
      ∏ s : {p : Fin n × Fin n // (β ∘ w) p.1 = (β ∘ w) p.2 ∧ γ p.1 < γ p.2},
        modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) := by
  have hentry : ∀ r c, (((cellInnerHom β γ w ⟨Cartan.diagPow F n μ,
      diagPow_mem_levi μ, diagPow_mem_blockUpper' (β ∘ w) μ⟩ : leviPar F n β (γ ∘ ⇑w⁻¹)) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
        if r = c then (GLnLocal.uniformizer F : F) ^ μ (w⁻¹ r) else 0 := by
    intro r c
    show ((leviProj F n β _ : levi F n β) : GL (Fin n) F) r c = _
    rw [leviProj_apply]
    simp only [coe_permConj, Subgroup.coe_inclusion]
    rw [permGL_conj_diagPow_apply]
    split_ifs with h1 h2 h2
    · rfl
    · rfl
    · exact absurd (h2 ▸ rfl) h1
    · rfl
  rw [modularCharacter_leviPar_of_diagonal _ fun i j hij => by rw [hentry, if_neg hij]]
  symm
  refine Fintype.prod_equiv (Equiv.subtypeEquiv
    (p := fun q : Fin n × Fin n => (β ∘ w) q.1 = (β ∘ w) q.2 ∧ γ q.1 < γ q.2)
    (q := fun q => β q.1 = β q.2 ∧ (γ ∘ ⇑w⁻¹) q.1 < (γ ∘ ⇑w⁻¹) q.2)
    (Equiv.prodCongr w w) fun p => by simp)
    (fun s => modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
      modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2)) _ fun s => ?_
  show _ = modulus ((((cellInnerHom β γ w ⟨Cartan.diagPow F n μ,
      diagPow_mem_levi μ, diagPow_mem_blockUpper' (β ∘ w) μ⟩ : leviPar F n β (γ ∘ ⇑w⁻¹)) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (w s.1.1) (w s.1.1)) /
    modulus ((((cellInnerHom β γ w ⟨Cartan.diagPow F n μ,
      diagPow_mem_levi μ, diagPow_mem_blockUpper' (β ∘ w) μ⟩ : leviPar F n β (γ ∘ ⇑w⁻¹)) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (w s.1.2) (w s.1.2))
  rw [hentry, hentry, if_pos rfl, if_pos rfl]
  simp

end DiagonalValues

section Identity

open MeasureTheory Measure Measures

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

theorem sqrt_identity {a b c d x : ℝ≥0} (ha : a ≠ 0) (hd : d ≠ 0) (h : x ^ 2 * b * d = c * a) :
    (((NNReal.sqrt a : ℝ) : ℂ))⁻¹ * ((x : ℝ) : ℂ) * ((NNReal.sqrt b : ℝ) : ℂ) =
      ((NNReal.sqrt c : ℝ) : ℂ) * (((NNReal.sqrt d : ℝ) : ℂ))⁻¹ := by
  have key : x * NNReal.sqrt b * NNReal.sqrt d = NNReal.sqrt c * NNReal.sqrt a := by
    have := congrArg NNReal.sqrt h
    rwa [NNReal.sqrt_mul, NNReal.sqrt_mul, NNReal.sqrt_mul, NNReal.sqrt_sq] at this
  have hsa : (NNReal.sqrt a : ℝ) ≠ 0 := by simpa using ha
  have hsd : (NNReal.sqrt d : ℝ) ≠ 0 := by simpa using hd
  have key' : (x : ℝ) * (NNReal.sqrt b : ℝ) * (NNReal.sqrt d : ℝ) =
      (NNReal.sqrt c : ℝ) * (NNReal.sqrt a : ℝ) := by exact_mod_cast key
  have hsa' : ((NNReal.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsa
  have hsd' : ((NNReal.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd
  have key'' : ((x : ℝ) : ℂ) * ((NNReal.sqrt b : ℝ) : ℂ) * ((NNReal.sqrt d : ℝ) : ℂ) =
      ((NNReal.sqrt c : ℝ) : ℂ) * ((NNReal.sqrt a : ℝ) : ℂ) := by exact_mod_cast key'
  field_simp
  linear_combination key''

theorem modulus_uniformizer_zpow_ne_zero (k : ℤ) :
    Measures.modulus ((GLnLocal.uniformizer F : F) ^ k) ≠ 0 :=
  Measures.modulus_ne_zero (zpow_ne_zero _ uniformizer_ne_zero)

theorem prod_modulus_ne_zero (μ : Fin n → ℤ) (P : Fin n × Fin n → Prop) [DecidablePred P] :
    ∏ s : {p : Fin n × Fin n // P p}, Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
      Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ =>
    div_ne_zero (modulus_uniformizer_zpow_ne_zero _) (modulus_uniformizer_zpow_ne_zero _)

variable (F β γ w) in

def cellScalarHom : leviPar F n γ (β ∘ w) →* ℂ :=
  ((invSqrtModular F n γ).comp (leviIncl.comp (Subgroup.inclusion
      (cellLeviParabolic_le_levi (F := F) (β := β) (γ := γ) (w := w))))) *
    cellCharHom F β γ w *
    ((sqrtModular F n β).comp ((permConj F β w).comp
      (Subgroup.inclusion (cellLeviParabolic_le_blockUpper (F := F) (β := β) (γ := γ) (w := w)))))

variable (F β γ w) in

def normScalarHom : leviPar F n γ (β ∘ w) →* ℂ :=
  normLeviParSqrtModular F γ (β ∘ w) *
    (normLeviParInvSqrtModular F β (γ ∘ ⇑w⁻¹)).comp ((cellInnerHom β γ w).comp
      (MonoidHom.id (leviPar F n γ (β ∘ w)) : leviPar F n γ (β ∘ w) →* cellLeviParabolic F β γ w))

theorem normLeviParSqrtModular_eq_one {γ δ : Fin n → ℕ} {l : leviPar F n γ δ}
    (hl : (l : GL (Fin n) F) ∈ integralGL F n) : normLeviParSqrtModular F γ δ l = 1 := by
  show ((NNReal.sqrt (modularCharacter l) : ℝ) : ℂ) = 1
  rw [modularCharacter_leviPar_eq_one_of_mem_integralGL l hl]
  simp

theorem cellScalarHom_eq_normScalarHom : cellScalarHom F β γ w = normScalarHom F β γ w := by
  ext b
  obtain ⟨μ, hμ⟩ := exists_diagPow_eq (γ := γ) (δ := β ∘ w) b
  have hint : ∀ k : leviPar F n γ (β ∘ w), (k : GL (Fin n) F) ∈ integralGL F n →
      permGL F w * (k : GL (Fin n) F) * (permGL F w)⁻¹ ∈ integralGL F n := fun k hk =>
    (integralGL F n).mul_mem ((integralGL F n).mul_mem (permGL_mem_integralGL w) hk)
      ((integralGL F n).inv_mem (permGL_mem_integralGL w))
  rw [hμ (cellScalarHom F β γ w) fun k hk => ?_, hμ (normScalarHom F β γ w) fun k hk => ?_]
  ·
    set t := Cartan.diagPow F n μ
    have hA := modularCharacter_leviIncl_diagPow (F := F) (γ := γ) μ
    have hB := modularCharacter_permConj_diagPow (F := F) (β := β) (w := w) μ
    have hC := modularCharacter_leviPar_diagPow (F := F) (γ := γ) (δ := β ∘ w) μ
    have hD := modularCharacter_cellInnerHom_diagPow (F := F) (β := β) (γ := γ) (w := w) μ
    have hX := cellChar_diagPow (F := F) (β := β) (γ := γ) (w := w) μ
    set m : Fin n → ℝ≥0 := fun i => Measures.modulus ((GLnLocal.uniformizer F : F) ^ μ i)
    have hm : ∀ i, m i ≠ 0 := fun i => modulus_uniformizer_zpow_ne_zero _
    set X : ℝ≥0 := ∏ s : {p : Fin n × Fin n // γ p.1 < γ p.2 ∧ (β ∘ w) p.2 < (β ∘ w) p.1},
      m s.1.1 / m s.1.2
    have hXr : cellChar F β γ w t = (X : ℝ) := by
      rw [hX]
      simp only [X, NNReal.coe_prod]
      rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n =>
        γ p.1 < γ p.2 ∧ β (w p.2) < β (w p.1)) (fun p => by simp [Function.comp])
        (fun p => ((m p.1 / m p.2 : ℝ≥0) : ℝ))]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [m, diagPow_apply_self]
    have hid := prod_character_identity γ (β ∘ w) m hm
    show (invSqrtModular F n γ (leviIncl ⟨t, diagPow_mem_levi μ⟩)) *
        ((cellChar F β γ w t : ℝ) : ℂ) *
        sqrtModular F n β (permConj F β w ⟨t, diagPow_mem_blockUpper' (β ∘ w) μ⟩) =
      ((NNReal.sqrt (modularCharacter (⟨t, diagPow_mem_leviPar μ⟩ : leviPar F n γ (β ∘ w))) : ℝ) :
          ℂ) *
        (((NNReal.sqrt (modularCharacter (cellInnerHom β γ w ⟨t, diagPow_mem_levi μ,
          diagPow_mem_blockUpper' (β ∘ w) μ⟩)) : ℝ) : ℂ))⁻¹
    rw [hXr]
    show (((NNReal.sqrt (modularCharacter (leviIncl (⟨t, diagPow_mem_levi μ⟩ : levi F n γ))) :
        ℝ) : ℂ))⁻¹ * ((X : ℝ) : ℂ) *
        ((NNReal.sqrt (modularCharacter (permConj F β w ⟨t, diagPow_mem_blockUpper' (β ∘ w) μ⟩)) :
          ℝ) : ℂ) = _
    rw [hA, hB, hC, hD]
    exact sqrt_identity (prod_modulus_ne_zero μ _) (prod_modulus_ne_zero μ _) hid
  · change normLeviParSqrtModular F γ (β ∘ w) k *
      (normLeviParSqrtModular F β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w k))⁻¹ = 1
    rw [normLeviParSqrtModular_eq_one hk, normLeviParSqrtModular_eq_one
      (leviProj_mem_integralGL (p := permConj F β w
        (Subgroup.inclusion cellLeviParabolic_le_blockUpper k)) (hint k hk))]
    simp
  ·
    change invSqrtModular F n γ (leviIncl _) * ((cellChar F β γ w (k : GL (Fin n) F) : ℝ) : ℂ) *
      sqrtModular F n β (permConj F β w _) = 1
    rw [invSqrtModular_leviIncl_of_mem _ hk, sqrtModular_of_mem_integralGL' (hint k hk),
      cellChar_eq_one_of_mem_integralGL (β := β) (γ := γ) (w := w) k.2 hk]
    simp

end Identity

end Parabolic

end GroundTheory.Automorphic
