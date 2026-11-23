import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.PairingRatioBijection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfIsAddSelf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiOperatorCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
open GlobalTheory.GtPointsCompare (castGen pairEquiv ptEquiv rel_iff)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns

variable (D F k) in

def rigPow := GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TF (R := R) F)).left) k

def LineCorr {b : TF (R := R) F ⟶ D.P.A} (t : LineGen D F k b)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b) (DegPre.lineε k))) : Prop :=
  LB.Gen.Corr D.P.L _ _ _ _ w (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ t.1) (rigPow D F k))

theorem phiRel_total (hB : D.TauBimult) (q : QkPt D F k)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) (s : Fam D F k) :
    ∃ s', PhiRel D F k q w s s' :=
  (exists_phi hG q w hw hB s).imp fun _ h => (phiRel_iff hG q w hw _ _).2 h

theorem phiRel_transfer (hB : D.TauBimult) {q q' : QkPt D F k} (he : QkPt.Equiv D F q q')
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q'.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s s', PhiRel D F k q w s s' ↔ PhiRel D F k q' w' s s' := by
  obtain ⟨w', hw', h⟩ := UT.PhiProj.phiRel_of_equiv hG he hw
  refine ⟨w', hw', fun s s' => ⟨h s s', fun H => ?_⟩⟩
  obtain ⟨r, hr⟩ := phiRel_total hB q hw s
  exact ThetaTranslate.phiRel_unique hG q' hw' (h s r hr) H ▸ hr

theorem weilQkIs_of_equiv (hB : D.TauBimult) {p p' q q' : QkPt D F k} (h : QkPt.Equiv D F p q)
    (h' : QkPt.Equiv D F p' q') {ζ : F} (H : WeilQkIs D F k p p' ζ) : WeilQkIs D F k q q' ζ := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  obtain ⟨v, hv, e⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h) hw
  obtain ⟨v', hv', e'⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h') hw'
  exact H v v' hv hv' s s₁ s₂ s₃ s₄ ((e' _ _).1 h₁) ((e _ _).1 h₂) ((e _ _).1 h₃) ((e' _ _).1 h₄)

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {E : SecA F P k → Fam D F k → Prop}

section Unif

variable {I : Ideal R} {Dd : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I Dd P G)

end Unif

end GlobalTheory.PhiOperatorCompare
