import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem exists_siegelH_proj_eq (x : ∀ v : HeightOneSpectrum (𝓞 F), siegelH (Fv F v) σ Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ∃ p : siegelH (AF F) σ Q,
      (∀ v ∈ S, proj σ Q v p = x v) ∧ (∀ v ∉ S, proj σ Q v p = 1) ∧ ∀ w, projArch σ Q w p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [proj_emb_self, h2 _ hu, mul_one]
      · rw [proj_emb_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embP, proj_emb_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embP, projArch_emb, h3, mul_one]

theorem exists_siegelH_projArch_eq (x : ∀ w : InfinitePlace F, siegelH w.Completion σ Q)
    (S : Finset (InfinitePlace F)) : ∃ p : siegelH (AF F) σ Q,
      (∀ w ∈ S, projArch σ Q w p = x w) ∧ (∀ w ∉ S, projArch σ Q w p = 1) ∧ ∀ v, proj σ Q v p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embArchP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [projArch_embArch_self, h2 _ hu, mul_one]
      · rw [projArch_embArch_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embArchP, projArch_embArch_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP, proj_embArch, h3, mul_one]

variable {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}

theorem HasIwasawa.adelic (hf : ∀ v : HeightOneSpectrum (𝓞 F), HasIwasawa σ Q (KFin σ Q L v))
    (hi : ∀ w : InfinitePlace F, HasIwasawa σ Q (KArch σ Q w (bc (compInf F E w) a))) :
    HasIwasawa σ Q (KAd σ Q L a) := fun g => by
  choose x k hk hx using fun v => hf v (proj σ Q v g)
  choose y l hl hy using fun w => hi w (projArch σ Q w g)
  have hS := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ Q (sumLat finSumFinEquiv L L) g)
  obtain ⟨p, h1, h2, h3⟩ := exists_siegelH_proj_eq x hS.toFinset
  obtain ⟨q, h4, -, h5⟩ := exists_siegelH_projArch_eq y Finset.univ
  refine ⟨p * q, (↑(p * q) : GAd σ Q)⁻¹ * g, mem_KAd.2 ⟨fun v => ?_, fun w => ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h5, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [h1 v hv, hx v, inv_mul_cancel_left]
      exact hk v
    · rw [h2 v hv, inv_one, one_mul]
      exact not_not.1 fun h => hv (hS.mem_toFinset.2 h)
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h3, one_mul, h4 w (Finset.mem_univ w), hy w, inv_mul_cancel_left]
    exact hl w

end GlobalTheory.Doubling

end
