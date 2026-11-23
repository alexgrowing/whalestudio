import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.CMExtend

section Mult

variable {E : Type} [Field E] [NumberField E]

theorem exists_natMul_isIntegral (x : E) : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * x) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x))
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this

theorem exists_natMul_mem_orderC {c : Ideal (OF E)} (hc : c ≠ ⊥) (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  obtain ⟨m, hm, hint⟩ := exists_natMul_isIntegral x
  have hk0 : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (m : E) * x :=
    ⟨⟨(m : E) * x, (mem_integralClosure_iff ℤ E).2 hint⟩, rfl⟩
  refine ⟨Ideal.absNorm c * m, mul_ne_zero hk0 hm, ?_⟩
  refine mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) ((Ideal.absNorm c : ℕ) : OF E) * y,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.absNorm_mem c)), ?_⟩
  rw [map_zero, zero_add, map_mul, hy, map_natCast, map_natCast, Nat.cast_mul, mul_assoc]

end Mult

section Ext

variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)}
variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]

def mulN (hc : c ≠ ⊥) (x : E) : ℕ := Classical.choose (exists_natMul_mem_orderC hc x)

theorem mulN_ne_zero (hc : c ≠ ⊥) (x : E) : mulN hc x ≠ 0 :=
  (Classical.choose_spec (exists_natMul_mem_orderC hc x)).1

theorem mulN_mem (hc : c ≠ ⊥) (x : E) : (mulN hc x : E) * x ∈ orderC c :=
  (Classical.choose_spec (exists_natMul_mem_orderC hc x)).2

variable (K) in

def extFun (hc : c ≠ ⊥) (g : orderC c →+* A) (x : E) : A :=
  ((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩

theorem map_natMul (g : orderC c →+* A) (n : ℕ) (z : orderC c) : g ((n : orderC c) * z) = (n : K) • g z := by
  rw [map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem extFun_eq (hc : c ≠ ⊥) (g : orderC c →+* A) {x : E} {m : ℕ} (hm : m ≠ 0) (h : (m : E) * x ∈ orderC c) :
    extFun K hc g x = ((m : K))⁻¹ • g ⟨(m : E) * x, h⟩ := by
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hn0 : (mulN hc x : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc x)
  have key : (m : K) • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩ = (mulN hc x : K) • g ⟨(m : E) * x, h⟩ := by
    rw [← map_natMul, ← map_natMul]
    congr 1
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_natCast]
    ring
  calc extFun K hc g x = ((mulN hc x : K))⁻¹ • ((m : K)⁻¹ • ((m : K) • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩)) := by
        rw [inv_smul_smul₀ hm0]; rfl
    _ = ((mulN hc x : K))⁻¹ • ((m : K)⁻¹ • ((mulN hc x : K) • g ⟨(m : E) * x, h⟩)) := by rw [key]
    _ = ((m : K))⁻¹ • g ⟨(m : E) * x, h⟩ := by
        rw [smul_comm ((m : K)⁻¹) ((mulN hc x : K)), inv_smul_smul₀ hn0]

variable (K) in

def extHom (hc : c ≠ ⊥) (g : orderC c →+* A) : E →+* A where
  toFun := extFun K hc g
  map_one' := by
    rw [extFun_eq hc g one_ne_zero (by simpa using (orderC c).one_mem)]
    simp only [Nat.cast_one, inv_one, one_smul]
    convert g.map_one using 2
    apply Subtype.ext; simp
  map_mul' x y := by
    have hx := mulN_mem hc x
    have hy := mulN_mem hc y
    have hxy : ((mulN hc x * mulN hc y : ℕ) : E) * (x * y) ∈ orderC c := by
      convert mul_mem hx hy using 1; push_cast; ring
    rw [extFun_eq hc g (mul_ne_zero (mulN_ne_zero hc x) (mulN_ne_zero hc y)) hxy]
    have e : (⟨((mulN hc x * mulN hc y : ℕ) : E) * (x * y), hxy⟩ : orderC c) =
        ⟨(mulN hc x : E) * x, hx⟩ * ⟨(mulN hc y : E) * y, hy⟩ := by
      apply Subtype.ext; simp only [Subring.coe_mul]; push_cast; ring
    rw [e, map_mul]
    show _ = (((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, hx⟩) * (((mulN hc y : K))⁻¹ • g ⟨(mulN hc y : E) * y, hy⟩)
    rw [smul_mul_smul_comm]
    push_cast
    rw [mul_inv]
  map_zero' := by
    rw [extFun_eq hc g one_ne_zero (by simpa using (orderC c).zero_mem)]
    convert smul_zero _ using 2
    convert g.map_zero using 2
    apply Subtype.ext; simp
  map_add' x y := by
    have hx := mulN_mem hc x
    have hy := mulN_mem hc y
    have hx0 : (mulN hc x : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc x)
    have hy0 : (mulN hc y : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc y)
    have e : ((mulN hc x * mulN hc y : ℕ) : E) * (x + y) =
        (((mulN hc y : ℕ) : orderC c) * ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc x : ℕ) : orderC c) * ⟨(mulN hc y : E) * y, hy⟩ :
          orderC c) := by
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]; push_cast; ring
    have hxy : ((mulN hc x * mulN hc y : ℕ) : E) * (x + y) ∈ orderC c := by rw [e]; exact Subtype.property _
    rw [extFun_eq hc g (mul_ne_zero (mulN_ne_zero hc x) (mulN_ne_zero hc y)) hxy]
    have e' : (⟨((mulN hc x * mulN hc y : ℕ) : E) * (x + y), hxy⟩ : orderC c) =
        ((mulN hc y : ℕ) : orderC c) * ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc x : ℕ) : orderC c) * ⟨(mulN hc y : E) * y, hy⟩ :=
      Subtype.ext e
    rw [e', map_add, map_natMul (K := K), map_natMul (K := K)]
    show _ = ((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc y : K))⁻¹ • g ⟨(mulN hc y : E) * y, hy⟩
    rw [smul_add, smul_smul, smul_smul]
    congr 2
    · push_cast; field_simp
    · push_cast; field_simp

theorem extHom_apply (hc : c ≠ ⊥) (g : orderC c →+* A) (a : orderC c) : extHom K hc g a = g a := by
  show extFun K hc g a = g a
  rw [extFun_eq hc g one_ne_zero (by simpa using a.2)]
  simp only [Nat.cast_one, inv_one, one_smul]
  congr 1
  apply Subtype.ext; simp

theorem ringHom_ext_orderC (hc : c ≠ ⊥) {B : Type} [Ring B] (f₁ f₂ : E →+* B) (h : ∀ a : orderC c, f₁ a = f₂ a) :
    f₁ = f₂ := by
  ext x
  obtain ⟨n, hn, hnx⟩ := exists_natMul_mem_orderC hc x
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : f₁ ((n : E)⁻¹) * (n : B) = 1 := by
    rw [← map_natCast f₁, ← map_mul, inv_mul_cancel₀ hnE, map_one]
  have h2 : (n : B) * f₂ ((n : E)⁻¹) = 1 := by
    rw [← map_natCast f₂, ← map_mul, mul_inv_cancel₀ hnE, map_one]
  have hinv : f₁ ((n : E)⁻¹) = f₂ ((n : E)⁻¹) := by
    calc f₁ ((n : E)⁻¹) = f₁ ((n : E)⁻¹) * ((n : B) * f₂ ((n : E)⁻¹)) := by rw [h2, mul_one]
      _ = f₂ ((n : E)⁻¹) := by rw [← mul_assoc, h1, one_mul]
  have hx : x = (n : E)⁻¹ * ((n : E) * x) := by rw [← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
  have := h ⟨(n : E) * x, hnx⟩
  simp only at this
  calc f₁ x = f₁ ((n : E)⁻¹ * ((n : E) * x)) := congrArg f₁ hx
    _ = f₂ ((n : E)⁻¹ * ((n : E) * x)) := by rw [map_mul f₁, hinv, this, ← map_mul]
    _ = f₂ x := (congrArg f₂ hx).symm

end Ext

def baseChangeRingHom (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (H : Type) [AddCommGroup H] [Module O H] :
    Module.End O H →+* Module.End K (K ⊗[O] H) where
  toFun f := f.baseChange K
  map_one' := LinearMap.baseChange_one O H
  map_mul' f g := LinearMap.baseChange_mul f g
  map_zero' := LinearMap.baseChange_zero
  map_add' f g := LinearMap.baseChange_add f g

theorem exists_unique_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) := by
  intro E _ _ _ c hc l hl O _ _ _ _ K _ _ _ hlm hcard D hD hcl I _ φ hφ H _ _ ρ Fil B hlat heig
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  refine ⟨extHom K hc ((baseChangeRingHom O K H).comp ρ), fun a => extHom_apply hc _ a, ?_⟩
  intro f hf
  exact ringHom_ext_orderC hc f _ fun a => by rw [hf a, extHom_apply hc _ a]; rfl

end GlobalTheory.CMExtend
