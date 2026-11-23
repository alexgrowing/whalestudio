import ReciprocityTheory.DualLattices.IsPairingValueAddRight
import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties
import ReciprocityTheory.DualLattices.TangentPairingStatementOfHeightFunctional
import ReciprocityTheory.DualLattices.ThmAFull
import ReciprocityTheory.DualLattices.AinfTower

namespace ReciprocityTheory.PGsh

theorem bx_heightFunctional {R₀ : Type*} [CommRing R₀] (B : BX R₀) : HighestWeightVectorUniformBounds B := heightFunctionalStatement_of_pairingProperties B (pairingProperties B)

theorem bx_tangentPairing {R₀ : Type*} [CommRing R₀] (B : BX R₀) : TangentPairingStatement B := B.tangentPairingStatement_of_heightFunctional (bx_heightFunctional B)

theorem bx_towerPairing {R₀ : Type*} [CommRing R₀] (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw :=
  b4 B (pairingProperties B) (bx_tangentPairing B) Tw

end ReciprocityTheory.PGsh
