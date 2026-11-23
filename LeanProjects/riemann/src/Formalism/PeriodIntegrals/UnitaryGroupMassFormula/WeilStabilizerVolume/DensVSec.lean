import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVSecSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem exists_leftInv_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let ι : (Fin a → K) →ₗ[K] (Fin M → K) := Fintype.linearCombination K Z
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h0 : ∑ i, (x - y) i • Z i = 0 := by
      have := congrArg (fun v => v) hxy
      simp only [ι, Fintype.linearCombination_apply] at this
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range ι)
  let e := LinearEquiv.ofInjective ι hinj
  let p : (Fin M → K) →ₗ[K] (Fin a → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq
  have hp : ∀ x, p (ι x) = x := by
    intro x
    have e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K) := rfl
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  refine ⟨fun k i' => p (Pi.single k 1) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * p (Pi.single k 1) i' = p (Z i) i' := by
    conv_rhs => rw [hZi]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, ← hι, hp, Pi.single_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp [h, Ne.symm h]

theorem secGram_holds : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  have := hss
  let s := sigR R σ
  let Z : Fin a → Fin M → R ⊗[F] E := fun i => Matrix.vecMul (fun l => s (x i l)) (JR (F := F) R J)
  have hZh : ∀ i y, hR R σ J (x i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) R) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR R)).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  have hZ : LinearIndependent (R ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → R ⊗[F] E := fun l => ∑ i, g i * s (x i l)
    have hv0 : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • x i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [v, map_sum, map_mul, s, sigR_invol R σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hx _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol R σ hσ, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep Z hZ
  refine ⟨q, fun S hS => ?_⟩
  have hh : algebraMap F (R ⊗[F] E) (1 / 2) + algebraMap F (R ⊗[F] E) (1 / 2) = 1 := by
    rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : sigR R σ (algebraMap F (R ⊗[F] E) (1 / 2)) = algebraMap F (R ⊗[F] E) (1 / 2) :=
    (Algebra.TensorProduct.map (AlgHom.id F R) σ).commutes _
  have h1 : ∀ i j, hR R σ J (x i)
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [hZh]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e3 : ∀ i', ∑ k, Z i k * (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * (if i = i' then 1 else 0) := fun i' => by
      rw [← hq i i', Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ i j, hR R σ J
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [← hR_herm R σ hσ J hJ (x j), h1 j i, map_mul, hsh, hS i j]
  funext i j
  show hR R σ J (x i) (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') +
    hR R σ J (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) = S i j
  rw [h1, h2, ← add_mul, hh, one_mul]

end PI.VolStabW
