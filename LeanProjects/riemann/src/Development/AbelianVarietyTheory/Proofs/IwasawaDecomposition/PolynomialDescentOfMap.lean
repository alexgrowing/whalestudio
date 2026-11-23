import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFibreOpenEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenEmbeddingOfLevelOneStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

theorem polDescSt_of_polMapSt : PolMapSt → PolDescSt := by
  intro hPM E _ _ _ H D Xo s l hg Z BD φ m hA htw hall c
  exact GlobalTheory.T.open_embedding_of_level_one E H D Xo s l hg c (Z c) hA (hall c).1
    (GlobalTheory.T.exists_generic_fibre_open_embedding E H D l (Xo l) Z BD φ m hPM htw (fun c => (hall c).2) c)

end GlobalTheory.TorRef
