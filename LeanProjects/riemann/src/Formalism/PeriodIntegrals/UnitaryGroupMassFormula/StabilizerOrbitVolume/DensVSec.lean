import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSecSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem exists_leftInv_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let f : (Fin a → K) →ₗ[K] (Fin M → K) := ∑ i, (LinearMap.proj i).smulRight (Z i)
  have hf_apply : ∀ c, f c = ∑ i, c i • Z i := by
    intro c
    simp [f, LinearMap.sum_apply]
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [hf_apply] at hc
    funext i
    exact Fintype.linearIndependent_iff.1 hZ c hc i
  obtain ⟨g, hg⟩ : ∃ g : (Fin M → K) →ₗ[K] (Fin a → K), g ∘ₗ f = LinearMap.id := by
    first
    | exact IsSemisimpleModule.extension_property f hf LinearMap.id
    | (obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.range f)
       exact ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
         Submodule.linearProjOfIsCompl _ _ hC, by
           ext c : 1
           simp [Submodule.linearProjOfIsCompl_apply_left]⟩)
  refine ⟨fun k i' => g (fun j => if k = j then 1 else 0) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (fun j => if k = j then (1 : K) else 0) := pi_eq_sum_univ (Z i)
  have key : g (Z i) = fun j => if i = j then 1 else 0 := by
    have hZf : Z i = f (fun j => if i = j then 1 else 0) := by
      rw [hf_apply]
      simp
    rw [hZf, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have h2 := congrFun key i'
  rw [hZi, map_sum] at h2
  simpa [Finset.sum_apply, map_smul] using h2

theorem secGram_holds : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  classical
  have hs2 : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσ]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  have hsF : ∀ c : F, sigR R σ (algebraMap F (R ⊗[F] E) c) = algebraMap F (R ⊗[F] E) c := by
    intro c
    simp [sigR]
  have hJR : ∀ k l, sigR R σ (JR (F := F) R J l k) = JR (F := F) R J k l := by
    intro k l
    simp [JR, inclR, sigR, hJ]
  have hJunit : IsUnit (JR (F := F) R J).det := by
    have hd : (JR (F := F) R J).det = inclR (F := F) R J.det := (RingHom.map_det (inclR (F := F) R) J).symm
    rw [hd]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  set s := sigR R σ with hs
  let w : Fin a → Fin M → R ⊗[F] E := fun i l => ∑ k, s (x i k) * JR (F := F) R J k l
  have hw : LinearIndependent (R ⊗[F] E) w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    set v : Fin M → R ⊗[F] E := fun k => ∑ i, c i * s (x i k) with hv
    have hvJ : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext l
      have hl := congrFun hc l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, Finset.mul_sum] at hl
      simp only [Matrix.vecMul, dotProduct, hv, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      simpa [mul_assoc] using hl
    have hv0 : v = 0 := by
      have h3 := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hvJ
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJunit] using h3
    have hx0 : ∑ i, s (c i) • x i = 0 := by
      funext k
      have h4 := congrArg s (congrFun hv0 k)
      simp only [hv, map_sum, map_mul, hs2, map_zero, Pi.zero_apply] at h4
      simpa [Finset.sum_apply, smul_eq_mul] using h4
    have h5 := Fintype.linearIndependent_iff.1 hx _ hx0 i
    rw [← hs2 (c i), h5, map_zero]
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep w hw
  refine ⟨q, fun S hS => ?_⟩
  have hS' : ∀ i j, s (S j i) = S i j := hS
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  set Y : Fin a → Fin M → R ⊗[F] E := fun j k => ∑ i', c * S i' j * q k i' with hY
  have hsum3 : ∀ f : Fin M → Fin M → Fin a → R ⊗[F] E,
      ∑ k, ∑ l, ∑ i', f k l i' = ∑ i', ∑ l, ∑ k, f k l i' := by
    intro f
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
  have h1 : ∀ i j, hR R σ J (x i) (Y j) = c * S i j := by
    intro i j
    have e1 : hR R σ J (x i) (Y j) =
        ∑ k, ∑ l, ∑ i', s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i') := by
      simp only [hR, Formalism.UG.hform, hY, Finset.mul_sum, ← hs]
    have e2 : ∑ i', c * S i' j * ∑ l, w i l * q l i' =
        ∑ i', ∑ l, ∑ k, s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i') := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e1, hsum3 (fun k l i' => s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i')), ← e2]
    simp [hq]
  have h2 : ∀ i j, hR R σ J (Y i) (x j) = s (hR R σ J (x j) (Y i)) := by
    intro i j
    simp only [hR, Formalism.UG.hform, ← hs, map_sum, map_mul, hs2, hJR]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsc : s c = c := hsF _
  have hcc : c + c = 1 := by
    rw [hc, ← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  unfold gramB
  funext i j
  show hR R σ J (x i) (Y j) + hR R σ J (Y i) (x j) = S i j
  rw [h2, h1, h1, map_mul, hsc, hS', ← add_mul, hcc, one_mul]

end PI.VolStabSW
