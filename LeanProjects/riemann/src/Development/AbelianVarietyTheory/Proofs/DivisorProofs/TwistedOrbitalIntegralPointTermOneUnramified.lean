import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem avg_const_one {H : Type} [Group H] : avg (fun _ : H => (1 : ℂ)) = 1 := by
  have hs : rStab (fun _ : H => (1 : ℂ)) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  rw [finsum_unique]
  simp

theorem twTerm_one_eq_one {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (hθ : ∀ k ∈ K, θ k ∈ K) (hδ : δ ∈ K) (hc : cptPart (twCent θ δ) ≤ K) :
    twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  have hT : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hmap : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
    ext x; simp
  have hidx : ((twCent θ δ ⊓ K.map (MulAut.conj (1 : G)).toMonoidHom).relIndex (cptPart (twCent θ δ))) = 1 := by
    rw [hmap, Subgroup.relIndex_eq_one]
    exact le_inf hT hc
  have hf : (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((1 * (k : G))⁻¹ * δ * θ (1 * k))) = fun _ => 1 := by
    funext k
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [one_mul, SetLike.mem_coe]
      exact K.mul_mem (K.mul_mem (K.inv_mem k.2) hδ) (hθ _ k.2)
  unfold twTerm
  rw [hidx, hf, avg_const_one]
  simp

end GlobalTheory.EulerAbs
