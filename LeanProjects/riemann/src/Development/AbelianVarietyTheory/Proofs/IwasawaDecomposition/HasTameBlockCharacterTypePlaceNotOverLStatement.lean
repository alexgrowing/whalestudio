import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  first | exact @GlobalTheory.TameTau.tauTame | exact GlobalTheory.TameTau.tauTame | (intros; apply GlobalTheory.TameTau.tauTame <;> assumption)
