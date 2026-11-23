import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem admissibleBase_of_completeNormalLocalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) :
    AdmBase R (maximalIdeal R) :=
  ⟨h.1, inferInstance, h.2.1, h.2.2.1⟩

theorem pullSt : PullSt := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t P hR hR' hφ hloc _
  obtain ⟨h1, -, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aR' := admissibleBase_of_completeNormalLocalCharZero hR'
  have : CharZero R' := hR'.2.2.2
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  obtain ⟨t', m₀, P', hD, -, -, -, -, xl, -⟩ :=
    GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5 aR aR' t P φ hφ hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  exact ⟨t', m₀, P', e, GlobalTheory.FlatTors.torsionIso_holds E H R' _ aR' t' P',
    fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩

end GlobalTheory.TorRef
