import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HsymmPairFlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hClos : GenericProjClosureModel.Statement) (hSeg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 n z z' fz gz hz a r R hR As Bs hAs hBs Q hQ
  classical
  have hA : (hsymmTimes N n a R).IsHomogeneous (a + r) :=
    (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
  rcases Nat.eq_zero_or_pos N with rfl | hN
  ·
    obtain rfl : x = u := funext fun i => i.elim0
    obtain rfl : x' = u' := funext fun i => i.elim0
    obtain rfl : f = f₂ := funext fun i => i.elim0
    obtain rfl : g = g₂ := funext fun i => i.elim0
    refine hExp O ϖ hϖ K ι (pointIdeal O y) d hV (0 + n) _ _ _ _ (fun i => ?_) (a + r) _ hA As Bs
      hAs hBs Q hQ
    refine Fin.addCases (fun i => i.elim0) (fun j => ?_) i
    simp only [Fin.append_right]
    exact hz j
  ·
    let Φ := FractionRing (MvPolynomial (Fin N) Ω)
    let t : Fin N → Φ := fun i => algebraMap (MvPolynomial (Fin N) Ω) Φ (X i)
    have ht : AlgebraicIndependent Ω t :=
      (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) Φ)
        (IsFractionRing.injective (MvPolynomial (Fin N) Ω) Φ)
    obtain ⟨M, M', a₀, a₀', φ, φ', hφ, hφ', hZ, f₀, g₀, hD₀, hD₀gen⟩ :=
      hClos O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' Φ w t ht
    have hC : (zetaPowTimes n (N - 1 + a) R).IsHomogeneous (N - 1 + a + r) := by
      have h := ((isHomogeneous_X ℤ (Fin.castAdd n (0 : Fin 1))).pow (N - 1 + a)).mul
        (hR.rename_isHomogeneous (f := (Fin.natAdd 1 : Fin n → Fin (1 + n))))
      rwa [one_mul] at h
    obtain ⟨Cs, hCs⟩ := exists_isPairExpansion hC
    rw [hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' w w' x x' f g hF1 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR As hAs Cs hCs Q hQ,
      hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' v v' u u' f₂ g₂ hF2 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR Bs hBs Cs hCs Q hQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
