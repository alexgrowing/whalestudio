import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.TwistGoodCounterexample

variable {D : D7}

def PartCUp (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) (e : ℝ) : Prop :=
  ∀ lam : D.ntw.abelian₂ i, BlochKatoReduction.Gen.thEval D.ntw i Q lam k' (BlochKatoReduction.Gen.psiAt (D.ntw.sideL i lam) ψ') ≠ 0 ∧
    BlochKatoReduction.Gen.vK (D.ntw.Ok i k') (D.ntw.l i) (BlochKatoReduction.Gen.thEval D.ntw i Q lam k' (BlochKatoReduction.Gen.psiAt (D.ntw.sideL i lam) ψ')) ≤
      BlochKatoReduction.Gen.c0 D.ntw i lam + e

def GoodUp (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∃ n : ℕ, TwGoodOne D ⟨I.E, fun _ => n, I.S⟩ i b Q k' ψ

def patch (p : D.what₂.places.Pl → NChoice D) : NChoice D where
  twI w := (p w).twI w
  twI_l w := (p w).twI_l w
  sd w := (p w).sd w
  Q w := (p w).Q w
  k' w := (p w).k' w
  psi' w := (p w).psi' w
  Oe w := (p w).Oe w
  crOe w := (p w).crOe w
  domOe w := (p w).domOe w
  dvrOe w := (p w).dvrOe w
  algOe w := (p w).algOe w
  algOOe w := (p w).algOOe w
  towOe w := (p w).towOe w
  Oe_inj w := (p w).Oe_inj w
  Oe_fin w := (p w).Oe_fin w
  Oe_loc w := (p w).Oe_loc w
  embW w := (p w).embW w
  embW_w w := (p w).embW_w w
  eMt w := (p w).eMt w
  eMt_basis w := (p w).eMt_basis w
  eMt_lat w := (p w).eMt_lat w

end GlobalTheory.TwistGoodCounterexample

end
