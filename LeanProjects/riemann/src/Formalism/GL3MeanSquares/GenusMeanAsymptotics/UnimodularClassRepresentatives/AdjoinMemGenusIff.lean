import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtAdjoinIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtOfSymmApply
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open SplitBAux in
theorem VecSplit.card_stab (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : S.adjoin (S.cut L) = L) :
    Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g S.x₀ = S.x₀} =
      Nat.card (Formalism.ThetaLiftIndependence.autL h' (S.cut L)) := by
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨res S g.1 (autL_iff.mp g.2.1).1 g.2.2,
        autL_iff.mpr ⟨res_mem_isom S _ _ _, gmap_res S _ _ _ (autL_iff.mp g.2.1).2⟩⟩
      invFun := fun g' => ⟨extOf S g'.1,
        autL_iff.mpr ⟨extOf_mem_isom hs S (autL_iff.mp g'.2).1, by
          have := gmap_extOf S g'.1 (autL_iff.mp g'.2).2
          rwa [hL] at this⟩, extOf_x₀ S _⟩
      left_inv := fun g => Subtype.ext (LinearEquiv.toLinearMap_injective
        (linearMap_ext S (by simp [extOf_x₀, g.2.2]) (fun a => by simp [extOf_ι, res_spec])))
      right_inv := fun g' => Subtype.ext (LinearEquiv.ext fun a => S.inj (by
        simp [res_spec, extOf_ι])) }

end Formalism.HermitianLattices.Ext.L3
