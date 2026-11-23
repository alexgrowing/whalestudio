import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem basicOpen_res_eq {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    Y₀.basicOpen ((res i U).hom b) = i ⁻¹ᵁ Y₁.basicOpen b := by
  change Y₀.basicOpen (i.appLE (upOpen i U) U (preimage_upOpen i U).ge b) = _
  rw [Scheme.basicOpen_appLE]
  refine inf_eq_right.mpr ?_
  calc i ⁻¹ᵁ Y₁.basicOpen b ≤ i ⁻¹ᵁ upOpen i U := fun x hx => Y₁.basicOpen_le b hx
    _ = U := preimage_upOpen i U

theorem upOpen_basicOpen_res {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    upOpen i (Y₀.basicOpen ((res i U).hom b)) = Y₁.basicOpen b := by
  rw [basicOpen_res_eq, upOpen_preimage]

theorem basicOpen_fibπ_mem_good {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] :
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
      Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈
        GlobalTheory.FerrandPush.good i₁ i₂ := by
  intro U hU a
  obtain ⟨h0, h1, h2⟩ := hU
  have e1 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₁ U).hom ((cone i₁ i₂ U).fst.hom a) := rfl
  have e2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := by
    rw [e1]
    exact congrArg (fun f : (cone i₁ i₂ U).pt ⟶ Γ(Y₀, U) => f.hom a) (cone i₁ i₂ U).condition
  refine ⟨h0.basicOpen _, ?_, ?_⟩
  · rw [e1, upOpen_basicOpen_res]
    exact h1.basicOpen _
  · rw [e2, upOpen_basicOpen_res]
    exact h2.basicOpen _

end GlobalTheory.FerrandPush
