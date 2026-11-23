import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

namespace PI.SupportParts

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def normG (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : ℚ := |Algebra.norm ℚ (Gpt T T' w)|

def SupportLoc (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (p : PlF D), Agree δ M p →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)), kind w = kind w' → KtopP M δ T T' p w w' ≠ 0 →
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) = (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
    (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))

def SupportVec (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) (κ : Option D.host.E)
    (th : ∀ p, Option ((M p).Cls D.R.rS)),
    (Function.mulSupport fun p => BBtop M δ T T' p w (th p)).Finite →
    (Function.mulSupport fun p => BBtop M δ T T' p w' (th p)).Finite →
    BBG M δ T T' w κ th ≠ 0 → BBG M δ T T' w' κ th ≠ 0 → normG T T' w = normG T T' w'

def SupportLocAll : Prop := ∀ D : Formalism.BasicNotions.D7, SupportLoc D

def SupportVecAll : Prop := ∀ D : Formalism.BasicNotions.D7, SupportVec D

end PI.SupportParts
