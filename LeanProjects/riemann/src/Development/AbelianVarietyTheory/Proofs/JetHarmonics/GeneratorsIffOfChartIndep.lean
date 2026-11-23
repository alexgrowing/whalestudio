import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasFinOrderIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaValueNaturalField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSectionNormMultiple
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SectionNormMultipleAgree
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorsCompare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

section Trans

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing V) F]

def GeoTrans (U : UnifPre (maximalIdeal V) D A G) (φ ψ : G ⟶ G) (k M : ℕ) (σ' : U.SecGF F k) (τ' : U.SecGF F M) :
    Prop :=
  ∃ (σ : LB.Sec (LPow G U.LG.L (k : ℤ) (TF (R := V) F))) (ga : ThetaGrp G U.LG.L (M : ℤ) (TF (R := V) F))
    (σ₁ σ₂ : LB.Sec (LPow G U.LG.L (M : ℤ) (TF (R := V) F))),
    RigidNormaliserGenerators.SameSec F U k σ σ' ∧ ga.pt ≫ ψ = 1 ∧ RigidNormaliserGenerators.HasFinOrder G U.LG ga ∧
      RigidNormaliserGenerators.IsRigPull G U.LG φ (k : ℤ) (M : ℤ) σ σ₁ ∧ IsActOf G U.LG.L (M : ℤ) ga σ₁ σ₂ ∧ RigidNormaliserGenerators.SameSec F U M σ₂ τ'

def FamTrans {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a b : O) (k N : ℕ)
    (s : Fam D.toPre F k) (s₂ : Fam D.toPre F (k * N)) : Prop :=
  ∃ (s₁ : Fam D.toPre F (k * N)) (p : QkPt D.toPre F (k * N))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (k * N)))) (ζ : F)
    (t : Fam D.toPre F (k * N)),
    PullAl D F oa a k N s s₁ ∧ DiagonalActionLiftPull.QkKilledBy oa b p ∧ w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D F (k * N) p w ζ ∧
      PhiRel D.toPre F (k * N) p w s₁ t ∧ Fam.IsSmul D.toPre F ζ t s₂

variable {F}

end Trans

section PEL

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
  [CharZero V] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsionIso {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t) : P.TorsionIso := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.lawsAndExpansions
  exact GlobalTheory.UT.torsionIso_of_pelUnif h₁ h₂ h₃ h₄ h₅ E H _ _
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t P

end PEL

section Concl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable (nab : NabV Xo c) (y) (F : Type) [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ)) (ν : c.F)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (val : MvPolynomial (LtN Dw n) c.F → F)

def ConclVal : Prop :=
  ∃ (u : F) (m : ℕ) (cf : Fin m → F) (x : Fin m → Fin n → Dw.La),
    v u = v (algebraMap T.Fr F (io ν)) ∧ (∀ i, 0 ≤ v (cf i)) ∧
    ∀ P ∈ harmA (Dw := Dw) c a n, ∃ w : Fin m → T.Fr, (∀ i, RigidNormaliserGenerators.IsThetaValue Xo c nab y (x i) P (w i)) ∧
      val P = u * ∑ i, cf i * algebraMap T.Fr F (w i)

def ConclRule : Prop :=
  ∃ (u : F) (m : ℕ) (cf : Fin m → F) (x : Fin m → Fin n → Dw.La),
    v u = v (algebraMap T.Fr F (io ν)) ∧ (∀ i, 0 ≤ v (cf i)) ∧
    ∀ P ∈ harmA c a n, ∀ f : Fin m → Rul Xo c, (∀ i, IsThRule Xo c nab (x i) P (f i)) →
      val P = u * ∑ i, cf i * algebraMap T.Fr F (evI y (f i))

variable {nab y F v ν a val}

end Concl

section Germs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ) {n : ℕ}
  {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)} [GrpObj G']
  [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' C.I.G.G n}
  {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
  (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ))

def GeoGerm (π : 𝓞 E) (g' M : ℕ) (h : PS F n (chD C.ch)) : Prop :=
  ∃ (σ' : U'.toUnifPre.SecGF F g') (s : Fam D'.toPre F g') (τ' : U'.toUnifPre.SecGF F M),
    U'.toUnifPre.ExpandsG F g' σ' s ∧ NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
    GeoTrans F U'.toUnifPre (RigidNormaliserGenerators.diagEnd pG (C.I.G.act.act (H.bar π))) (RigidNormaliserGenerators.diagEnd pG (C.I.G.act.act π)) g' M
      σ' τ' ∧ IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F M τ' h

def FamGerm (π : 𝓞 E) (g' g : ℕ) (h : PS F n (chD C.ch)) : Prop :=
  ∃ (_ : Module (𝓞 E) D'.toPre.X) (oa' : letI := H.starRing; D'.toPre.OAct (𝓞 E)) (s : Fam D'.toPre F g')
    (s₂ : Fam D'.toPre F (g' * g)) (τ' : U'.toUnifPre.SecGF F (g' * g)),
    (letI := H.starRing; DiagonalActionLiftPull.IsDiagAct pD oa' P.oD) ∧ NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
    (letI := H.starRing; FamTrans F oa' (H.bar π) π g' g s s₂) ∧ U'.toUnifPre.ExpandsG F (g' * g) τ' s₂ ∧
    IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) τ' h

end Germs

def GaugeClause : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l),
  letI := H.starRing
  ∀ (k : Type) [Field k] [CharZero k] [Algebra c.F k] (y : FrPt Xo c k) (C : ChartAt Xo c y)
    (h' : PS k 2 C.d), DiagonalActionLiftPull.IsBalancedGauge C.B k h' →
  ∀ (N n : ℕ) (P : MvPolynomial (LtN Dw n) k),
    P ∈ harmK Dw.mult n k ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    ∀ f : PS k n C.d,
      nabValN C.B k h' H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) P =
        nabValN C.B k C.h H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) P

end GlobalTheory.GeneratorsCompare
