import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeafDepthAllRunUnconditional
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndexAssembly

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.OntoChain GlobalTheory.RunDepth GlobalTheory.TraceLattice GlobalTheory.TraceClassRank
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {L : SizeData₂ D} {Pm : ParameterChoice' D L}

def ownPrime (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℕ := if plc v = D.host.pde then D.host.pde' else D.host.pde

abbrev kap (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m) : WeightFamilies.Wt D ((i : ℕ) + 1) := kaR Tp hK ((i : ℕ) + 1)

abbrev LevelMaps (J : CoreJ D) (G : Type) (i : Fin D.R.m) : Type :=
  G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)

def BoundTie (L : SizeData₂ D) {Bs : DefBase D.what₂.LL} (N : IndefNum Bs) (C : ℝ) : Prop :=
  ∀ j, N.E1 j = C * (L.sc.x ^ L.sc.eps *
    (sizeBudget D.R L.sc.x L.sc.eps + budgetNc D.R L.sc.x L.sc.eps D.host.T2.card))

section Comparison₂

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

def DepthTie (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    {P : Type} [Group P] [Finite P] (O : OnObj S P c) (ι : Bs.J → Fin D.R.m) : Prop :=
  letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar J.Q.H
  letI := (Model.hostMap D).toAlgebra
  RunTie J.toCore EX Tp hK O fun i => (ι i : ℕ) + 1

variable (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (fw : FWTie J R (kap Tp hK) v₀) (F : Face D A)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J) (hr : ∀ v, LawsFull (r v).full)
  (ι : Bs.J → Fin D.R.m) (ℓ : ∀ i, LevelMaps J G i) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)

def FormsTie (O : OnObj S (Mir R) c) : Prop :=
  ∃ (hc : LawsCore J.toCore)
    (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB hc).KO] (recB hc).Cusp ((ι i : ℕ) + 1) (kap Tp hK (ι i)))
    (act : ∀ i, Mir R → (recB hc).Cusp ((ι i : ℕ) + 1) (kap Tp hK (ι i)) → (recB hc).Cusp ((ι i : ℕ) + 1) (kap Tp hK (ι i)))
    (y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A (ι i) (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)),
    ∀ v i, OnTie (T := (r v).full) (R := R) (hr v).p fw hinj EX (ownPrime D v) (ι i) (lR Tp hK ((ι i : ℕ) + 1))
      (fR Tp hK ((ι i : ℕ) + 1)) Tp.TO O v i (z i) (act i) (mirIncl R) (ℓ (ι i)) F.P0 F.ψ0⁻¹ (ph v i) (y v i)

def Tied (O : OnObj S (Mir R) c) : Prop :=
  FormsTie Tp hK hinj EX fw F r hr ι ℓ ph O ∧ DepthTie J EX Tp hK O ι ∧ NumTie Tp hK O

variable (R S) in

def RunsPinned : Prop :=
  (∀ v i, OneCover (r v).full.toTop ((ι i : ℕ) + 1) ∧ TwistTrivialOnRational (r v).full ((ι i : ℕ) + 1)) ∧
    (AtPair S fun v => ∀ i, RunPin (T := (r v).full) R (ι i) D.R.nV v (ownPrime D v)) ∧
    ∀ v, HalfPin (T := (r v).full) R ∧ ∀ i, LevelPin (T := (r v).full) R (ι i) (ℓ (ι i))

def GeneratorInputs : Prop :=
  ∀ v i, Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB (hr v).p.toLawsCore) ((ι i : ℕ) + 1) (kap Tp hK (ι i)) ∧
    ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ (hr v).p ((ι i : ℕ) + 1) (inR_succ (ι i))) (kap Tp hK (ι i)) ∧
    WeightAlgebra.H2 (recPJ (hr v).p ((ι i : ℕ) + 1) (inR_succ (ι i)))
      (scalOfP (recB (hr v).p.toLawsCore) hinj EX (ownPrime D v) (kap Tp hK (ι i)) (lR Tp hK ((ι i : ℕ) + 1))
        (fR Tp hK ((ι i : ℕ) + 1)) Tp.TO) (kap Tp hK (ι i)) (lR Tp hK ((ι i : ℕ) + 1)) (fR Tp hK ((ι i : ℕ) + 1))

variable {Tp hK hinj EX fw F r hr ι ℓ ph} {O : OnObj S (Mir R) c}

variable (Tp hK) in

def withNumbers {P : Type} [Group P] [Finite P] (O : OnObj S P c) : OnObj S P c :=
  { O with
    rr := D.R.r
    T2 := D.host.T2.card
    Nc := budgetNc D.R L.sc.x L.sc.eps D.host.T2.card
    DF := topDeg Tp hK
    de2 := L.de2
    pde := D.host.pde }

variable (J Tp hK EX ι) in

def withDepth {P : Type} [Group P] [Finite P] (O : OnObj S P c) : OnObj S P c :=
  letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar J.Q.H
  letI := (Model.hostMap D).toAlgebra
  withNumbers Tp hK (Model.retie J.toCore EX Tp hK O fun i => (ι i : ℕ) + 1)

end Comparison₂

def depthConst : ℝ := max 1 leafDepth_all_run_unconditional.choose

def absConst : OnConst := ⟨depthConst, 14, 66 * depthConst + 4⟩

section Bound

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df}
  {Tp : ParamsT D L Pm} {hK : DV.KapDef D} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {fw : FWTie J R (kap Tp hK) v₀} {F : Face D A}
  {r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J} {hr : ∀ v, LawsFull (r v).full}
  {ι : Bs.J → Fin D.R.m} {ℓ : ∀ i, LevelMaps J G i} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {O : OnObj S (Mir R) absConst} {N : IndefNum Bs} {C : ℝ}

end Bound

def IndexBoundInput (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df}
    {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c) : Prop := DomPlus Tp hK → LatticeIndexBoundAtPairs O

def BadShareInput (L : SizeData₂ D) (x₁ : ℝ → ℝ) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df}
    {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c) : Prop := x₁ L.sc.eps ≤ L.sc.x → LeafBadShare O

end GlobalTheory.IndexAssembly
