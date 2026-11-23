import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagPairGenericIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_pair_generic_iso : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (E E' : B.X.Modules) (ψ : E' ⟶ E) [IsIso (B.genRes.map ψ)] (r : ℕ) (fl : Vert.Flag E r) (fl' : Vert.Flag E' r) (a : ∀ i, fl'.F i ⟶ fl.F i), (∀ i, a i ≫ fl.ι i = fl'.ι i ≫ ψ) → ∃ P : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom ψ) r, ∃ (_ : P.fl = fl) (_ : P.fl' = fl'), ∀ i, ∃ (φ : B.GenIso (fl.gr i) (fl'.gr i)) (b : fl'.gr i ⟶ fl.gr i), φ.inv = B.genRes.map b ∧ fl'.π i ≫ b = a i.succ ≫ fl.π i ∧ P.div i = φ.div (fl.isVB_gr i) (fl'.isVB_gr i) := by
  first | exact @GlobalTheory.FlagPairOfHom.exists_flagPair | exact GlobalTheory.FlagPairOfHom.exists_flagPair | (intros; apply GlobalTheory.FlagPairOfHom.exists_flagPair <;> assumption)
