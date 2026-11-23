import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipRadicalOfRational
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipRadicalOfRational.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipRadicalOfRational.Statement h v := by
  classical
  intro x₀ γ hx hz
  have hγ : ∀ u : W, γ • u = (γ : W ≃ₗ[E] W) u := fun _ => rfl

  have key : ∃ y : W, ∀ u : W, ∃ a : E,
      γ • u = u + h.toSesq x₀ u • (γ • y - y) + a • x₀ := by
    by_cases hy : ∃ y, h.toSesq x₀ y = 1
    · obtain ⟨y, hy⟩ := hy
      refine ⟨y, fun u => ?_⟩
      obtain ⟨a, ha⟩ := hz (u - h.toSesq x₀ u • y)
        (by rw [map_sub, map_smul, smul_eq_mul, hy, mul_one, sub_self])
      have hs : γ • (u - h.toSesq x₀ u • y) = γ • u - h.toSesq x₀ u • (γ • y) := by
        simp only [hγ, map_sub, map_smul]
      rw [hs] at ha
      refine ⟨a, ?_⟩
      rw [smul_sub, sub_eq_iff_eq_add.mp ha]
      abel
    · refine ⟨0, fun u => ?_⟩
      have h0 : h.toSesq x₀ u = 0 := by
        by_contra hu
        exact hy ⟨(h.toSesq x₀ u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
      obtain ⟨a, ha⟩ := hz u h0
      exact ⟨a, by simp [ha]⟩
  obtain ⟨y, hy⟩ := key
  choose a ha using fun j => hy (v j)
  rw [mem_unipRadical]
  intro w
  set M : Matrix ι ι ℂ := (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
    Matrix ι ι ℂ) with hM
  have hvec : ∀ x : W, M *ᵥ vecAt v x w = vecAt v (γ • x) w := fun x =>
    congrFun (archEmbed_smul_vecAt h v γ x) w

  have hcol : ∀ i j, M i j = w.embedding (v.repr (γ • v j) i) := by
    intro i j
    have := congrFun (hvec (v j)) i
    simpa [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite,
      eq_comm] using this
  refine ⟨by rw [hvec, hx], fun z hz0 => ?_⟩

  have hℓ : ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j = 0 := by
    rw [← hz0]
    have hH : ∀ j, w.embedding (h.toSesq x₀ (v j)) =
        ∑ i, star (vecAt v x₀ w i) * gramAt h v w i j := by
      intro j
      rw [HermAtPlace.proof h v w x₀ (v j)]
      simp [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite]
    simp only [hH, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∑ j, w.embedding (a j) * z j, ?_⟩
  funext i
  have hrow : (M *ᵥ z) i = ∑ j, (w.embedding (if i = j then 1 else 0) +
      w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) +
      w.embedding (a j) * w.embedding (v.repr x₀ i)) * z j := by
    simp only [mulVec, dotProduct, hcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]
    simp [Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  have e1 : ∑ j, w.embedding (if i = j then 1 else 0) * z j = z i := by
    simp [apply_ite]
  have e2 : ∑ j, w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) * z j =
      w.embedding (v.repr (γ • y - y) i) * ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, w.embedding (a j) * w.embedding (v.repr x₀ i) * z j =
      (∑ j, w.embedding (a j) * z j) * w.embedding (v.repr x₀ i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, hℓ]
  simp [vecAt]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
