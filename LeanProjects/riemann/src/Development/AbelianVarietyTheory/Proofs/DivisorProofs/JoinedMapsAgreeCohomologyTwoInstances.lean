import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.JoinedTwoProof

universe a b

theorem main : JoinedTwo.{a, b} := by
  intro C _ C' _ K K' m m' θ j c
  obtain ⟨⟨⟨z, w, η⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨h1, h2, h3, -⟩ := hc
  dsimp only at h1 h2 h3
  refine QuotientAddGroup.eq.2 ⟨(fun T T' φ ↦ m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T')),
    fun T ↦ m'.a1 T (w _ _ (θ.app T))), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · change K'.M0.map ψ (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) -
        m'.a0 T'' (z _ _ _ (θ.app T) (m'.G.map (φ ≫ ψ)) - z _ _ _ (m.G.map (φ ≫ ψ)) (θ.app T'')) +
        m'.a0 T'' (z _ _ _ (θ.app T') (m'.G.map ψ) - z _ _ _ (m.G.map ψ) (θ.app T'')) =
      -m.a0 T'' (z _ _ _ (m.G.map φ) (m.G.map ψ)) + m'.a0 T'' (z _ _ _ (m'.G.map φ) (m'.G.map ψ))
    have e1 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.a0 T'') (h1 _ _ _ _ (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    rw [← m.G.map_comp] at e1
    rw [← m'.G.map_comp] at e3
    simp only [map_add, j.e0, m'.compDegreeZero_natural] at e1 e2 e3
    simp only [map_sub, m'.compDegreeZero_natural]
    linear_combination (norm := abel1) e1 - e2 + e3
  · change m'.a1 T' (w _ _ (θ.app T')) - K'.M1.map φ (m'.a1 T (w _ _ (θ.app T))) -
        K'.d0 T' (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) =
      -m.a1 T' (w _ _ (m.G.map φ)) + m'.a1 T' (w _ _ (m'.G.map φ))
    have e := congrArg (m'.a1 T') ((h2 _ _ _ (m.G.map φ) (θ.app T')).symm.trans
      ((congrArg (w _ _) (θ.naturality φ)).trans (h2 _ _ _ (θ.app T) (m'.G.map φ))))
    simp only [map_add, j.e1, m'.compDegreeOne_natural, m'.comp_commutes_diffZero] at e
    simp only [map_sub]
    linear_combination (norm := abel1) e
  · change K'.d1 T (m'.a1 T (w _ _ (θ.app T))) = -m.a2 T (η _) + m'.a2 T (η _)
    rw [h3 _ _ (θ.app T), map_add, j.e2, m'.comp_commutes_diffOne]; abel

theorem joinedTwo_inst : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := ⟨main, main, main⟩

end GlobalTheory.CxCoh.JoinedTwoProof
