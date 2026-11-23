import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Inhabit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def blockLinSubst {F : Type*} [Field F] {K K' : Type*} {ι : K → Type*} {ι' : K' → Type*} [∀ k, Fintype (ι k)]
    (e : K' ≃ K) (A : ∀ k', ι' k' → ι (e k') → F) : MRingOver F ι' →ₐ[F] MRingOver F ι :=
  aeval fun q => ∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩

def LinEmbed.Statement : Prop :=
  ∀ (F : Type) [Field F] (K K' : Type) [Fintype K] [Fintype K'] (ι : K → Type) (ι' : K' → Type)
    [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] (e : K' ≃ K) (A : ∀ k', ι' k' → ι (e k') → F),
    (∀ k', Function.Injective (Matrix.of (A k')).mulVec) →
    ∀ (I : IFamily F ι) (I' : IFamily F ι'), IsFieldIntersection I → IsFieldIntersection I' →
      ∀ (V : Ideal (MRingOver F ι)) (d : ℕ) (L : Fin d → K → ℤ), IsProjVarF V d →
        I' (V.comap (blockLinSubst e A).toRingHom) d (fun j => L j ∘ e) = I V d L

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
