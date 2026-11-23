import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChtTrueYEta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EvlTrueIncTInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FibLatPreSubSpanSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def IsHTLatOf {ct : At S κ p} (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (B : ct.Mdl) (L : Lat B) : Prop :=
  (∃ n, 3 ≤ n ∧ hm.IsHTBlowup B (ct.Xn n)) ∧ ∀ y : ct.Pt B,
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing
    hm.omPat y = (GlobalTheory.HTSheaf.fibLat (ct.isGrpPullback_htToMdl y) L.N).toAddSubgroup

def stagesOf (ct : At S κ p) (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (jt : JetSt ct (uniTrue ct) (thgTrue ct)) : Stages ct where
  lw := SharedLaws.lawSt _ _ _ _ _ _ _ ct
  mo := motTrue ct
  sh := shfTrue ct
  fg := flgOf ct (IsHTLatOf hm)
  fr := frmTrue ct
  ch := chtTrue ct
  tr := torTrue ct
  fj := fjTrue ct
  un := uniTrue ct
  tb := thbTrue ct
  ky := keyTrue ct
  bd := bdyTrue ct
  tg := thgTrue ct
  jt := jt
  ev := evlTrue ct
  hq := htpTrue ct
  hm := hm
  cd := crdTrue ct
  cr := crhOf ct (IsHTLatOf hm) (classFam (IsHTLatOf hm))

abbrev HTmFam (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  HTmSt ct (shfTrue ct) (htpTrue ct)

abbrev JetFam (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  JetSt ct (uniTrue ct) (thgTrue ct)

def stOf (hm : HTmFam D) (jt : JetFam D)  (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) : StFam S κ :=
  ⟨fun {p} ct => stagesOf ct (hm A N j S κ p ct) (jt A N j S κ p ct), alpOf D, fun _ => rfl⟩

end GlobalTheory.LocM
