import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace IsotropicScaling

section Maps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def scalingMap (h : HermitianForm F E W) (v w : W) (α β : E) : W →ₗ[E] W :=
  LinearMap.id + α • (h.toSesq w).smulRight v + β • (h.toSesq v).smulRight w

variable (h : HermitianForm F E W) {v w : W}

theorem scalingMap_apply (α β : E) (x : W) :
    scalingMap h v w α β x = x + (α * h.toSesq w x) • v + (β * h.toSesq v x) • w := by
  simp [scalingMap, mul_smul]

theorem scalingMap_zero : scalingMap h v w 0 0 = LinearMap.id := by
  simp [scalingMap]

theorem pairing_left (hww : h.toSesq w w = 0) (hwv : h.toSesq w v = 1) (α β : E) (x : W) :
    h.toSesq w (scalingMap h v w α β x) = (1 + α) * h.toSesq w x := by
  rw [scalingMap_apply, map_add, map_add, map_smul, map_smul, hwv, hww, smul_eq_mul, smul_eq_mul]
  ring

theorem pairing_right (hvv : h.toSesq v v = 0) (hvw : h.toSesq v w = 1) (α β : E) (x : W) :
    h.toSesq v (scalingMap h v w α β x) = (1 + β) * h.toSesq v x := by
  rw [scalingMap_apply, map_add, map_add, map_smul, map_smul, hvv, hvw, smul_eq_mul, smul_eq_mul]
  ring

variable (hvv : h.toSesq v v = 0) (hww : h.toSesq w w = 0) (hvw : h.toSesq v w = 1)
  (hwv : h.toSesq w v = 1)
include hvv hww hvw hwv

theorem scalingMap_comp (α β α' β' : E) :
    scalingMap h v w α β ∘ₗ scalingMap h v w α' β' =
      scalingMap h v w (α + α' + α * α') (β + β' + β * β') := by
  ext x
  rw [LinearMap.comp_apply, scalingMap_apply h α β, pairing_left h hww hwv,
    pairing_right h hvv hvw, scalingMap_apply, scalingMap_apply]
  module

theorem scalingMap_isometry {α β : E} (hαβ : α + conj F E β + α * conj F E β = 0) (x y : W) :
    h.toSesq (scalingMap h v w α β x) (scalingMap h v w α β y) = h.toSesq x y := by
  have hαβ' : conj F E α + β + conj F E α * β = 0 := by
    simpa [conj_conj] using congrArg (conj F E) hαβ
  have hc : ∀ z, conjHom F E z = conj F E z := fun _ => rfl
  have hxv : h.toSesq x v = conj F E (h.toSesq v x) := (h.isSymm.eq v x).symm
  have hxw : h.toSesq x w = conj F E (h.toSesq w x) := (h.isSymm.eq w x).symm
  rw [scalingMap_apply, scalingMap_apply]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hvv, hww, hvw, hwv, hxv, hxw, hc, map_mul]
  linear_combination (h.toSesq w y * conj F E (h.toSesq v x)) * hαβ +
    (h.toSesq v y * conj F E (h.toSesq w x)) * hαβ'

end Maps

theorem sub_one_add_inv_sub_one_add_mul_eq_zero {E : Type*} [Field E] {u : E} (hu : u ≠ 0) :
    u - 1 + (u⁻¹ - 1) + (u - 1) * (u⁻¹ - 1) = 0 := by
  field_simp
  ring

section Lattice

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_nsmul_mem {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ La := by
  let S : Submodule E W :=
    { carrier := {w | ∃ N : ℕ, 0 < N ∧ N • w ∈ La}
      add_mem' := by
        rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
        refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
        rw [smul_add, mul_smul, mul_comm, mul_smul]
        exact add_mem (La.nsmul_mem ha N) (La.nsmul_mem hb M)
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c a ⟨N, hN, ha⟩
        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨m, s, hm, hs⟩ := hc.exists_nsmul_eq (𝓞 E)
        refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, ?_⟩
        have : (m * N) • (c • a) = (algebraMap (𝓞 E) E s) • (N • a) := by
          rw [← hs]
          module
        rw [this]
        exact hLa.smul_mem s _ ha }
  have hS : Submodule.span E (La : Set W) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_pos, by simpa using hx⟩
  exact (hS (hLa.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W)))

omit [NumberField E] in
theorem conj_mem_integralClosure {z : E}
    (hz : z ∈ integralClosure ℤ E) : conj F E z ∈ integralClosure ℤ E :=
  IsIntegral.map ((conj F E : E ≃ₐ[F] E) : E →+* E).toIntAlgHom hz

omit [NumberField E] in

theorem scalingMap_mem (h : HermitianForm F E W) {La : AddSubgroup W} (hLa : IsLattice E La)
    (hint : IsIntegralOn h La) {v w : W} (hv : v ∈ La) {N : ℕ} (hNw : N • w ∈ La)
    {u : (𝓞 E)ˣ} (hu : u ∈ congruenceUnits E N) {x : W} (hx : x ∈ La) :
    scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x ∈ La := by
  have smem : ∀ z ∈ integralClosure ℤ E, ∀ y ∈ La, z • y ∈ La :=
    fun z hz y hy => hLa.smul_mem ⟨z, hz⟩ y hy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (mem_congruenceUnits.1 hu)
  have ht' : ((u : 𝓞 E) : E) - 1 = (t : E) * N := by exact_mod_cast ht.symm
  have hu0 : conj F E ((u : 𝓞 E) : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast u.ne_zero
  have hinv : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    exact_mod_cast u.inv_mul
  have hN : h.toSesq (N • w) x = N * h.toSesq w x := by
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  have e2 : ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) * h.toSesq v x =
      (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) * N := by
    have hct : conj F E ((u : 𝓞 E) : E) - 1 = conj F E (t : E) * N := by
      rw [← map_one (conj F E), ← map_sub, ht', map_mul, map_natCast]
    rw [hinv, map_inv₀]
    field_simp
    linear_combination (-h.toSesq v x) * hct
  have key : scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x =
      x + ((t : E) * h.toSesq (N • w) x) • v +
        (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) • (N • w) := by
    rw [scalingMap_apply, e2, ht', hN, ← Nat.cast_smul_eq_nsmul E]
    module
  rw [key]
  refine add_mem (add_mem hx (smem _ ?_ v hv)) (smem _ ?_ _ hNw)
  · exact mul_mem t.2 (hint _ hNw x hx)
  · exact mul_mem (mul_mem (neg_mem (conj_mem_integralClosure (u⁻¹ : (𝓞 E)ˣ).val.2))
      (conj_mem_integralClosure t.2)) (hint v hv x hx)

end Lattice

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem proof (h : HermitianForm F E W) (h₁ : WittPartner.Statement h) :
    IsotropicScaling.Statement h := by
  intro La x₀ hLa hint hx₀ hne hiso
  obtain ⟨w₀, hvw, hww⟩ := h₁ x₀ hne hiso
  have hwv : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hvw, map_one]
  obtain ⟨N, hN, hNw⟩ := exists_nsmul_mem hLa w₀
  refine ⟨N, hN, fun ε hε => ?_⟩
  have he : ((ε : 𝓞 E) : E) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hce : conj F E ((ε : 𝓞 E) : E) ≠ 0 := (map_ne_zero _).2 he
  have hinv : (((ε⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((ε : 𝓞 E) : E)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by exact_mod_cast ε.inv_mul)
  set e : E := ((ε : 𝓞 E) : E)
  have hcinv : (conj F E e⁻¹)⁻¹ = conj F E e := by rw [map_inv₀, inv_inv]
  have k1 : e - 1 + (e⁻¹ - 1) + (e - 1) * (e⁻¹ - 1) = 0 := sub_one_add_inv_sub_one_add_mul_eq_zero he
  have k2 : (conj F E e)⁻¹ - 1 + (conj F E e - 1) + ((conj F E e)⁻¹ - 1) * (conj F E e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero hce); rwa [inv_inv] at this
  have k3 : e⁻¹ - 1 + (e - 1) + (e⁻¹ - 1) * (e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero he); rwa [inv_inv] at this
  have k4 : conj F E e - 1 + ((conj F E e)⁻¹ - 1) + (conj F E e - 1) * ((conj F E e)⁻¹ - 1) = 0 :=
    sub_one_add_inv_sub_one_add_mul_eq_zero hce
  have h1 : scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) ∘ₗ
      scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k1, k2, scalingMap_zero]
  have h2 : scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) ∘ₗ
      scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k3, k4, scalingMap_zero]
  let γ : W ≃ₗ[E] W := LinearEquiv.ofLinearMap _ _ h1 h2
  have hγU : γ ∈ h.unitaryGroup := HermitianForm.mem_unitaryGroup.2 fun x y =>
    scalingMap_isometry h hiso hww hvw hwv
      (by rw [map_sub, map_inv₀, conj_conj, map_one]; exact k1) x y
  have memT : ∀ x ∈ La, scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x ∈ La :=
    fun x hx => scalingMap_mem h hLa hint hx₀ hNw hε hx
  have memT' : ∀ x ∈ La, scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) x ∈ La := fun x hx => by
    have := scalingMap_mem h hLa hint hx₀ hNw (inv_mem hε) hx
    rwa [hinv, hcinv] at this
  refine ⟨⟨γ, hγU⟩, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext y
    refine ⟨fun hy => ?_, fun hy => ⟨_, memT' y hy, ?_⟩⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact memT x hx
    change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1)
      (scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) y) = y
    rw [← LinearMap.comp_apply, h1, LinearMap.id_apply]
  · change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x₀ = e • x₀
    rw [scalingMap_apply, hwv, hiso]
    module

end Main

end IsotropicScaling

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
