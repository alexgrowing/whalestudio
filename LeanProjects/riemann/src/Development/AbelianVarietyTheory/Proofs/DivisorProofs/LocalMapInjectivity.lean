import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSigmaLiftW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorNumberFieldIsReduced
import GroundTheory.Brauer.TensorSimple
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.HTGroupLocInj
variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

noncomputable def iotaZ : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem locW_iotaZ (i : Fin G.m) (z : ℚ_[p] ⊗[ℚ] G.F) :
    G.locW i (iotaZ G z) = algebraMap (G.Fw i) (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (G.liftW i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    change (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) a) * (G.rho i (algebraMap G.F G.C y)) =
      algebraMap (G.Fw i) _ (algebraMap ℚ_[p] (G.Fw i) a * G.embW i y)
    rw [G.rho_F, Algebra.ofId_apply, map_mul, ← IsScalarTower.algebraMap_apply]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

theorem starT_iotaZ (z : ℚ_[p] ⊗[ℚ] G.F) :
    (starT G.star ℚ_[p] (iotaZ G z)).unop = iotaZ G (conjT G.F ℚ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp [iotaZ, starT_tmul, G.star_F]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem inj_Z (z : ℚ_[p] ⊗[ℚ] G.F) (h1 : ∀ i, G.liftW i z = 0) (h2 : ∀ i, G.liftW i (conjT G.F ℚ_[p] z) = 0) :
    z = 0 := by
  have hJ : z ∈ (⊥ : Ideal (ℚ_[p] ⊗[ℚ] G.F)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    obtain ⟨i, hi | hi⟩ := GlobalTheory.MaxIdealTensorPadic.main p G M hM <;> rw [hi, RingHom.mem_ker]
    · exact h1 i
    · exact h2 i
  haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] G.F) := IsArtinianRing.of_finite ℚ_[p] _
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ℚ_[p] ⊗[ℚ] G.F)
  have hk0 : z ^ k = 0 := by
    have := Ideal.pow_mem_pow hJ k
    rw [hk] at this
    simpa using this
  haveI := GlobalTheory.padic_tensor_numberField_isReduced p G.F
  exact IsReduced.eq_zero _ ⟨k, hk0⟩

theorem iotaZ_comm (d : ℚ_[p] ⊗[ℚ] G.C) (z : ℚ_[p] ⊗[ℚ] G.F) : Commute d (iotaZ G z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact hx.add_right hy
  | tmul a y =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => exact hx.add_left hy
    | tmul b c =>
      simp only [iotaZ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (b ⊗ₜ c) * (a ⊗ₜ algebraMap G.F G.C y) = (a ⊗ₜ algebraMap G.F G.C y) * (b ⊗ₜ c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b a,
        Algebra.commutes]

theorem locW_inj (x : ℚ_[p] ⊗[ℚ] G.C) (h1 : ∀ i, G.locW i x = 0)
    (h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = 0) : x = 0 := by
  classical
  letI algD : Algebra G.F (ℚ_[p] ⊗[ℚ] G.C) :=
    RingHom.toAlgebra' ((iotaZ G).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)) (by
      intro c d
      show iotaZ G ((1 : ℚ_[p]) ⊗ₜ c) * d = d * iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
      exact (iotaZ_comm G d _).symm.eq)
  letI algZ : Algebra G.F (ℚ_[p] ⊗[ℚ] G.F) := Algebra.TensorProduct.rightAlgebra
  let f : G.C →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).toRingHom with
      commutes' := fun c => by
        show (1 : ℚ_[p]) ⊗ₜ algebraMap G.F G.C c = iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
        simp [iotaZ] }
  let g : (ℚ_[p] ⊗[ℚ] G.F) →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (iotaZ G).toRingHom with
      commutes' := fun c => rfl }
  let Φ := Algebra.TensorProduct.lift f g (fun c z => iotaZ_comm G _ _)
  have hΦ1 : ∀ z, Φ ((1 : G.C) ⊗ₜ z) = iotaZ G z := fun z => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hΦs : Function.Surjective Φ := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
      refine ⟨c ⊗ₜ (a ⊗ₜ (1 : G.F)), ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show ((1 : ℚ_[p]) ⊗ₜ c) * iotaZ G (a ⊗ₜ 1) = a ⊗ₜ c
      simp [iotaZ, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  let ψ : ℚ_[p] ⊗[ℚ] G.C →+* ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) ×
      ((i : Fin G.m) → (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ᵐᵒᵖ) :=
    RingHom.prod (RingHom.pi fun i => (G.locW i).toRingHom)
      (RingHom.pi fun i => (RingHom.op (G.locW i).toRingHom).comp (starT G.star ℚ_[p]))
  have hψ : ∀ d, ψ d = 0 ↔ (∀ i, G.locW i d = 0) ∧ ∀ i, G.locW i (starT G.star ℚ_[p] d).unop = 0 := by
    intro d
    simp only [ψ, Prod.ext_iff, funext_iff, RingHom.prod_apply, Pi.ringHom_apply, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, RingHom.comp_apply]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [← MulOpposite.unop_inj]
    rfl
  let J : TwoSidedIdeal (G.C ⊗[G.F] (ℚ_[p] ⊗[ℚ] G.F)) := TwoSidedIdeal.ker (ψ.comp Φ.toRingHom)
  have hJ : J = ⊥ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot J hne
    apply hz0
    rw [TwoSidedIdeal.mem_ker, RingHom.comp_apply] at hz
    change ψ (Φ ((1 : G.C) ⊗ₜ z)) = 0 at hz
    rw [hΦ1, hψ] at hz
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    apply inj_Z G z
    · intro i
      have := hz.1 i
      rw [locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
    · intro i
      have := hz.2 i
      rw [starT_iotaZ, locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
  obtain ⟨y, rfl⟩ := hΦs x
  have hy : y ∈ J := by
    rw [TwoSidedIdeal.mem_ker]
    exact (hψ _).2 ⟨h1, h2⟩
  rw [hJ, TwoSidedIdeal.mem_bot] at hy
  rw [hy, map_zero]

end GlobalTheory.HTGroupLocInj
