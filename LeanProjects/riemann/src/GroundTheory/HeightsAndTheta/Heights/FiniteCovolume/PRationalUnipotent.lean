import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StRationalUnipotent

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace RationalUnipotent

def unipMap (h : HermitianForm F E W) (x₀ y : W) (c : E) : W →ₗ[E] W where
  toFun x := x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y
  map_add' a b := by
    simp only [map_add]
    module
  map_smul' r a := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    module

omit [NumberField E] in
theorem unipMap_apply (h : HermitianForm F E W) (x₀ y : W) (c : E) (x : W) :
    unipMap h x₀ y c x = x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y := rfl

omit [NumberField E] in

theorem sesq_swap (h : HermitianForm F E W) (u v : W) :
    h.toSesq u v = conj F E (h.toSesq v u) :=
  (h.isSymm.eq v u).symm

omit [NumberField E] in

theorem sesq_smul_left (h : HermitianForm F E W) (r : E) (u v : W) :
    h.toSesq (r • u) v = conj F E r * h.toSesq u v := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl

theorem unipMap_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipMap h x₀ y c (unipMap h x₀ (-y) (conj F E c) x) = x := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add, map_smul, map_neg, LinearMap.neg_apply, hx₀, hy, hy']
  have key : h.toSesq x₀ x * conj F E c - -h.toSesq y x +
      (h.toSesq x₀ x * c - (h.toSesq y x + -(h.toSesq x₀ x * h.toSesq y y))) = 0 := by
    linear_combination h.toSesq x₀ x * hc
  linear_combination (norm := module) key • x₀

theorem sesq_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x x' : W) :
    h.toSesq (unipMap h x₀ y c x) (unipMap h x₀ y c x') = h.toSesq x x' := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
    sesq_smul_left, hx₀, hy, hy', map_sub, map_mul, mul_zero, add_zero]
  rw [sesq_swap h x x₀, sesq_swap h x y]
  linear_combination conj F E (h.toSesq x₀ x) * h.toSesq x₀ x' * hc

def unipElem (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) : h.unitaryGroup :=
  ⟨LinearEquiv.ofLinearMap (unipMap h x₀ y c) (unipMap h x₀ (-y) (conj F E c))
    (LinearMap.ext fun x => unipMap_unipMap h hx₀ hy hc x)
    (LinearMap.ext fun x => by
      have e := unipMap_unipMap h (y := -y) (c := conj F E c) hx₀
        (by rw [map_neg, hy, neg_zero])
        (by rw [conj_conj, add_comm, hc, map_neg, LinearMap.map_neg₂, neg_neg]) x
      rwa [neg_neg, conj_conj] at e),
    fun x x' => sesq_unipMap h hx₀ hy hc x x'⟩

theorem unipElem_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipElem h hx₀ hy hc • x = unipMap h x₀ y c x := rfl

theorem unipElem_inv_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    (unipElem h hx₀ hy hc)⁻¹ • x = unipMap h x₀ (-y) (conj F E c) x := rfl

theorem unipMap_mem (h : HermitianForm F E W) {La : AddSubgroup W}
    (hsm : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) (hint : IsIntegralOn h La)
    {x₀ y : W} {c : E} (hx₀ : x₀ ∈ La) (hy : y ∈ La) (hc : c ∈ integralClosure ℤ E)
    {x : W} (hx : x ∈ La) : unipMap h x₀ y c x ∈ La := by
  have smul_mem : ∀ {α : E} {v : W}, α ∈ integralClosure ℤ E → v ∈ La → α • v ∈ La :=
    fun {α} {v} hα hv => hsm ⟨α, hα⟩ v hv
  rw [unipMap_apply]
  refine add_mem (add_mem hx (smul_mem ?_ hx₀)) (smul_mem (hint x₀ hx₀ x hx) hy)
  exact sub_mem (mul_mem (hint x₀ hx₀ x hx) hc) (hint y hy x hx)

omit [NumberField E] in

theorem conj_mem_integralClosure {c : E} (hc : c ∈ integralClosure ℤ E) :
    conj F E c ∈ integralClosure ℤ E :=
  (mem_integralClosure_iff ℤ E).2
    (((mem_integralClosure_iff ℤ E).1 hc).map (conj F E).toAlgHom.toRingHom.toIntAlgHom)

end RationalUnipotent

open RationalUnipotent in

theorem RationalUnipotent.proof (h : HermitianForm F E W) : RationalUnipotent.Statement h := by
  intro D La x₀ w₀ hD hx₀ hp
  refine ⟨1, one_pos, ?_⟩
  rintro y c hyW ⟨z₁, hz₁, rfl⟩ ⟨a, rfl⟩ hc
  simp only [Nat.cast_one, one_mul, one_smul] at hyW hc ⊢
  obtain ⟨hxx, hww, hxw⟩ := hp
  have hyx : h.toSesq x₀ z₁ = 0 := (mem_hypComplement.1 hyW).1
  have hyw : h.toSesq w₀ z₁ = 0 := (mem_hypComplement.1 hyW).2
  have hzx : h.toSesq z₁ x₀ = 0 := by rw [sesq_swap, hyx, map_zero]
  have hzw : h.toSesq z₁ w₀ = 0 := by rw [sesq_swap, hyw, map_zero]
  have haI : (a : E) ∈ integralClosure ℤ E :=
    (mem_integralClosure_iff ℤ E).2 (RingOfIntegers.isIntegral_coe a)
  set γ := unipElem h hxx hyx hc with hγ
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists v γ La).1 hv
      rw [hγ, unipElem_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ hz₁ haI hu
    · intro hv
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      rw [hγ, unipElem_inv_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ (neg_mem hz₁)
        (conj_mem_integralClosure haI) hv
  · rw [hγ, unipElem_smul, unipMap_apply, hxx, hzx]
    simp
  · rw [hγ, unipElem_smul, unipMap_apply, hxw, hzw]
    simp only [one_mul, sub_zero, one_smul]
    abel
  · intro z hz
    rw [hγ, unipElem_smul, unipMap_apply, (mem_hypComplement.1 hz).1]
    simp only [zero_mul, zero_sub, zero_smul, add_zero, neg_smul]
    abel

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
