import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem exists_nAut_unramified (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂)
    (h : IsEmpty nd.Loc) : ∃ A : NAut nd, (∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p) ∧
      ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := by
  choose pl h1 h2 h3 using fun k => GaloisStage.exists_places B.host (B.host.g_prime k) (nd.g_split k)
  let e : ∀ k, nd.PlG k ≃ Fin B.R.f := fun k => Fintype.equivFinOfCardEq (nd.card_PlG k)
  exact ⟨GaloisStage.nAut nd (fun k v => pl k (e k v)) (fun k v => h1 k _)
    (fun k => (h2 k).comp (e k).injective) (fun k v v' => h3 k _ _), fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end GlobalTheory.MemN
