import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesExtendBasis

theorem span_single_eq_top (K : Type) [Field K] (n : ℕ) :
    Submodule.span K (Set.range fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⊤ := by
  have h : (fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⇑(Pi.basisFun K (Fin n)) := by
    funext x
    simp
  rw [h]
  exact (Pi.basisFun K (Fin n)).span_eq

end KLinesExtendBasis

open KLinesExtendBasis in

theorem LinesExtendBasis.proof : LinesExtendBasis.Statement := by
  intro K _ n m k b hb hn
  set W : Submodule K (Fin n → K) := Submodule.span K (Set.range b) with hW
  let e : Fin n → (Fin n → K) := fun x => Pi.single x 1
  have hspan : Submodule.span K (Set.range (W.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, span_single_eq_top, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ : ∃ (κ : Type) (a : κ → Fin n), Function.Injective a ∧
      Submodule.span K (Set.range ((W.mkQ ∘ e) ∘ a)) = Submodule.span K (Set.range (W.mkQ ∘ e)) ∧
      LinearIndependent K ((W.mkQ ∘ e) ∘ a) := exists_linearIndependent' K (W.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ K ((Fin n → K) ⧸ W) := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = k := by
    have h1 := W.finrank_quotient_add_finrank
    rw [Module.finrank_eq_card_basis B, hW, finrank_span_eq_card hb, Module.finrank_fin_fun,
      Fintype.card_fin] at h1
    omega
  let σ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ σ, ha.comp σ.injective, ?_⟩
  let f : Fin m → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp W.subtype hb
  have hg : LinearIndependent K (Submodule.Quotient.mk (p := W) ∘ fun j => e (a (σ j))) :=
    hli.comp σ σ.injective
  exact LinearIndependent.sumElim_of_quotient hf (fun j => e (a (σ j))) hg

end GroundTheory.Heights₂.Heights
