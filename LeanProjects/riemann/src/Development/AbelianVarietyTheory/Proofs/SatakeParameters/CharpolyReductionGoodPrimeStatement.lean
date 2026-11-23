import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyReductionGoodPrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_reduction_good_prime : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.IotaRed D → GlobalTheory.RowTie.RowRepAtG D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩; Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _) = ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  first | exact @GlobalTheory.ResidualTame.charpoly_tameGen | exact GlobalTheory.ResidualTame.charpoly_tameGen | (intros; apply GlobalTheory.ResidualTame.charpoly_tameGen <;> assumption)
