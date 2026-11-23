import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_mk_one {K : UQ} (B₁ B₂ : InvAlg K) (y : B₁.A) :
    Algebra.norm K.E ((y, 1) : B₁.A × B₂.A) = Algebra.norm K.E y := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul K.E (B₁.A × B₂.A) (y, 1) =
      LinearMap.prodMap (Algebra.lmul K.E B₁.A y) (Algebra.lmul K.E B₂.A 1) := by
    ext z <;> simp
  rw [h, LinearMap.det_prodMap, map_one, map_one, mul_one]

theorem chi_prod_inl : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  intro K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ x
  have hS : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
      (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
    unfold eS
    rw [Finset.sum_map]
    show (∑ i ∈ S₁, ((e₁ i, 0) : B₁.A × B₂.A)) = ((∑ i ∈ S₁, e₁ i, 0) : B₁.A × B₂.A)
    rw [Prod.ext_iff]
    simp [Prod.fst_sum, Prod.snd_sum]
  unfold chi
  rw [hS]
  have hx : (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)) : B₁.A × B₂.A) =
      ((x.1 * eS B₁ e₁ S₁ + (1 - eS B₁ e₁ S₁), 1) : B₁.A × B₂.A) := by
    ext <;> simp
  change K.eta (Algebra.norm K.E (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)))) = _
  rw [hx, norm_prod_mk_one]

end GlobalTheory.UnitLemma.Desc
