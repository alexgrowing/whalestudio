import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem continuous_of_isom (σ : E ≃+* E) (h : Isom σ) : Continuous σ := by
  have h0 : ContinuousAt ((σ : E →+* E) : E →+ E) 0 := by
    rw [ContinuousAt, map_zero]
    intro s hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hs
    refine Filter.mem_map.2 ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun x hx => hγ ?_⟩)
    change valuation E (σ x) < γ
    rw [h x]
    exact hx
  exact continuous_of_continuousAt_zero ((σ : E →+* E) : E →+ E) h0

private theorem continuous_sg (σ : E ≃+* E) (h : Continuous σ) : Continuous (sg (n := n) σ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact h.comp (Units.continuous_val.matrix_elem i j)
  · have he : ∀ g : GL (Fin n) E, (((sg σ g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        ((sg σ g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := fun g => by rw [map_inv]
    refine continuous_matrix fun i j => ?_
    simp only [he, sg_val]
    exact h.comp ((Units.continuous_val.comp continuous_inv).matrix_elem i j)

private theorem sg_iterate (σ : E ≃+* E) (i : ℕ) (g : GL (Fin n) E) (a b : Fin n) :
    (((sg σ)^[i] g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) a b =
      σ^[i] ((g : Matrix (Fin n) (Fin n) E) a b) := by
  induction i generalizing g with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, sg_val]

private theorem isClosed_borel : IsClosed (borel E (Fin n) : Set (GL (Fin n) E)) := by
  have : (borel E (Fin n) : Set (GL (Fin n) E)) =
      ⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) E | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_borel, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

private theorem isClosed_unipB : IsClosed (unipB E (Fin n) : Set (GL (Fin n) E)) := by
  have : (unipB E (Fin n) : Set (GL (Fin n) E)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) E | g.val i j = 0}) ∩
        ⋂ i, {g : GL (Fin n) E | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)

private theorem whitChar_sg (σ : E ≃+* E) (ψ : AddChar E Circle) (hψ : ∀ x, ψ (σ x) = ψ x)
    (u u' : unipB E (Fin n)) (h : (u' : GL (Fin n) E) = sg σ u) : whitChar ψ n u' = whitChar ψ n u := by
  have hs : ∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u' : GL (Fin n) E).val p.1 p.2 =
      σ (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin n) E).val p.1 p.2) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [h]; rfl
  change Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  rw [hs, hψ]

theorem gLFacts : GLFacts := by
  intro E _ _ _ _ n
  refine ⟨isClosed_borel, isClosed_unipB, ⟨GroundTheory.Automorphic.GLnLocal.integralGL E n,
    GroundTheory.Automorphic.GLnLocal.isOpen_integralGL E n, GroundTheory.Automorphic.GLnLocal.isCompact_integralGL E n, fun g => ?_⟩,
    fun ψ hψ => GlobalTheory.Whittaker.isSmoothChar_whitChar hψ, fun σ q hq => ⟨continuous_sg σ (continuous_of_isom σ hq.isom),
      fun g => ?_, fun b hb => ?_, fun ψ hψ u u' h => whitChar_sg σ ψ hψ u u' h⟩⟩
  · obtain ⟨b, hb, k, hk, e⟩ := GroundTheory.Automorphic.Iwasawa.exists_borel_mul_integralGL E n g
    exact ⟨b, (mem_borel E).2 fun i j h => hb h, k, hk, e⟩
  · exact Units.ext (Matrix.ext fun a c => by rw [sg_iterate, hq.ord])
  · exact (mem_borel E).2 fun i j h => by rw [sg_val, (mem_borel E).1 hb i j h, map_zero]

end UpperTheory.Gal.LocD

end
