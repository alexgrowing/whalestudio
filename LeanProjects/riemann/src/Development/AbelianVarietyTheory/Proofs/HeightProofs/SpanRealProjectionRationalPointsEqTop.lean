import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare

variable {D : D7}

theorem span_tauE_eq_top {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) :
    Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) = ⊤ := by
  set S := Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) with hS
  have hθ := h.inf
  have hcl : IsClosed (S : Set (D.what₂.Tau → ℂ)) := S.closed_of_finiteDimensional
  have key : ∀ y : Ainf D.host.F ⊗[D.host.F] D.host.E, (fun τ => θ τ y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have : (fun τ => θ τ 0) = 0 := by funext τ; exact RingHom.map_zero _
      rw [this]; exact S.zero_mem
    | add a b ha hb =>
      have : (fun τ => θ τ (a + b)) = (fun τ => θ τ a) + fun τ => θ τ b := by
        funext τ; exact RingHom.map_add _ _ _
      rw [this]; exact S.add_mem ha hb
    | tmul a x =>
      have e : ∀ (a : Ainf D.host.F) τ, θ τ (a ⊗ₜ[D.host.F] x) =
          θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
        intro a τ
        rw [← (hθ τ).1, ← RingHom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hc : Continuous fun a : Ainf D.host.F => fun τ => θ τ (a ⊗ₜ[D.host.F] x) := by
        refine continuous_pi fun τ => ?_
        simp only [e]
        exact (hθ τ).2.mul continuous_const
      refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
        (hcl.preimage hc) fun f => ?_
      have e1 : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
        exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes f |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
      refine Submodule.subset_span ⟨algebraMap D.host.F D.host.E f * x, ?_⟩
      funext τ
      show tauE D τ _ = θ τ ((algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] x)
      rw [e, e1, (hθ τ).1, RingHom.map_mul]
  rw [eq_top_iff]
  intro z _
  have := key (infPart D (σ z))
  rwa [show (fun τ => θ τ (infPart D (σ z))) = z from funext fun τ => h.comp z τ] at this

theorem span_piW_ratW_eq_top (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V W : HSp D) :
    Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) = ⊤ := by
  classical
  set T := Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) with hT
  let L : Fin V.rank → Fin W.rank → (D.what₂.Tau → ℂ) →ₗ[ℝ] RW V W := fun i j =>
    { toFun := fun z τ k l => if i = k ∧ j = l then z τ else 0
      map_add' := fun x y => by funext τ k l; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext τ k l; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hL : ∀ i j z, L i j z ∈ T := by
    intro i j z
    have hz : z ∈ Submodule.comap (L i j) T := by
      refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.comap (L i j) T) ((span_tauE_eq_top h).ge Submodule.mem_top)
      rintro _ ⟨e, rfl⟩
      refine Submodule.subset_span ⟨Matrix.single i j e, ?_⟩
      funext τ k l
      show θ τ (infPart D (incA D (Matrix.single i j e k l))) = if i = k ∧ j = l then tauE D τ e else 0
      rw [comp_incA h.inf, Matrix.single_apply]
      split_ifs
      · rfl
      · exact RingHom.map_zero _
    exact hz
  rw [eq_top_iff]
  intro z _
  have : z = ∑ i, ∑ j, L i j fun τ => z τ i j := by
    funext τ k l
    simp only [Finset.sum_apply]
    show z τ k l = ∑ i, ∑ j, if i = k ∧ j = l then z τ i j else 0
    simp [ite_and]
  rw [this]
  exact T.sum_mem fun i _ => T.sum_mem fun j _ => hL i j _

end GlobalTheory.FockCompare

end
