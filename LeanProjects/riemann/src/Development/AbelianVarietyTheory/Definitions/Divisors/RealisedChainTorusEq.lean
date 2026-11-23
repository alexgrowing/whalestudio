import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONPage

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def ownAt (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℕ := if plc v = D.host.pde then D.host.pde' else D.host.pde

structure TwoRuns (J : CoreJ D) (G : Type) : Type 1 where
  first : RunData J
  second : RunData J
  lev : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)

def TwoRuns.used {J : CoreJ D} (r : TwoRuns J G) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : RunData J :=
  if plc v = D.host.pde then r.second else r.first

section Rec

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}
variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg' (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

structure RunsOk (fw : FWTie J R κ v₀) (r : TwoRuns J G) : Prop where
  laws : ∀ v, LawsFull (r.used v).full
  cover : ∀ v (i : Fin D.R.m), OneCover (r.used v).full.toTop ((i : ℕ) + 1)
  xiRat : ∀ v (i : Fin D.R.m), ∀ γ₀ ∈ GQ ((r.used v).full.V ((i : ℕ) + 1) (r.used v).full.σ₀),
    (r.used v).full.xi (Matrix.GeneralLinearGroup.det (finHom ((r.used v).full.V ((i : ℕ) + 1) (r.used v).full.σ₀) γ₀)) = 1
  run : ∀ v ∈ R.twPl, ∀ i : Fin D.R.m, RunPin (T := (r.used v).full) R i (κ i).n v (ownAt D v)
  level : ∀ v (i : Fin D.R.m), LevelPin (T := (r.used v).full) R i (r.lev i)
  action : ∀ v (i : Fin D.R.m), ActionPin (T := (r.used v).full) (R := R) (laws v).p fw i (r.lev i)
  half : J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal

@[reducible] def hostAlg (D : D7) : Algebra (𝓞 D.host.E) D.what₂.LL :=
  (D.embE.comp (algebraMap (𝓞 D.host.E) D.host.E)).toAlgebra

structure IsRec (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (F : Face D A) (fw : FWTie J R κ v₀) (r : TwoRuns J G)
    {c : OnConst} (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c) : Prop where
  ok : RunsOk fw r
  kap : ∀ i : Fin D.R.m, κ i = kaR Tp hK ((i : ℕ) + 1)
  tied : ∃ (hc : LawsCore J.toCore) (hinj : Function.Injective D.what₂.OtoLL),
    OnObjLevelCompatibility F fw hc r.used (fun v => (ok.laws v).p) hinj EX (ownAt D) (fun _ i => lR Tp hK ((i : ℕ) + 1))
      (fun _ i => fR Tp hK ((i : ℕ) + 1)) Tp.TO r.lev (fun _ => 1) (mirIncl R) O
  depth : ∃ st : StarRing (𝓞 D.host.E), letI := st; letI := hostAlg D
    GlobalTheory.RunDepth.RunTie J.toCore EX Tp hK O fun j : Fin D.R.m => (j : ℕ) + 1
  DF_eq : O.DF = ((Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1)) : ℕ) : ℝ)
  rr_eq : O.rr = (D.R.r : ℝ)
  Nc_eq : O.Nc = L.Nc
  realisedChain_torus_eq : O.T2 = D.host.T2.card
  pde_eq : O.pde = D.host.pde

end Rec

section Leaves

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def HasIndexBound (O : OnObj S P c) : Prop :=
  ∃ Th1 a r1 r2 de2, LatticeIndexBoundAtPairs ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2 } : OnObj S P c)

def HasTwistBound (O : OnObj S P c) : Prop := ∃ ε, LeafTW1 ({ O with ε0 := ε } : OnObj S P c)

def HasExpBound (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  (∀ w ∈ S.Tw, ∀ j, 0 ≤ N.J0 (S.μ w) w j) ∧
    ∃ Jp, LeafJSum ({ O with Jp := Jp } : OnObj S P c) ∧ LeafJExp N ({ O with Jp := Jp } : OnObj S P c)

end Leaves

section Low

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def BaseLinks (R : RealDat D A Ks) (F : Face D A) : Prop :=
  (R.toCx F).H5 F.cr false ∧ (R.toCx F).RATth F.cr false ∧ (lv (F.fc (R.toCx F).zs) false).Proviso

def lowB (D : D7) (i : Fin D.R.m) (b : ℝ) : ℝ :=
  GlobalTheory.LiftLower.hookPlus D i - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D b

def LowTop (R : RealDat D A Ks) (b : ℝ) : Prop :=
  ∀ (i : Fin D.R.m) (l : ℝ) (x : (R.HW i (sg0 D A)).H), x ≠ 0 → 0 < l →
    R.thG i A.μ0 (LinearMap.adjoint (R.thG i A.μ0) x) = (l : ℂ) • x → lowB D i b ≤ Real.log l

def LowForm (R : RealDat D A Ks) (F : Face D A) (b : ℝ) : Prop :=
  ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A.v0 →
    ∀ x : Fin ((lv (F.fc (R.toCx F).zs) false).dZ i A.μ0) → D.what₂.LL,
      Real.exp (lowB D i b) * (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx F).zs) false).XT i A.μ0) v x x).re ≤
        ‖(R.toCx F).wC false i v (cpt v.embedding (((R.toCx F).liftMat F.cr false i A.μ0).mulVec x))‖ ^ 2

def reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) : RealDat D A Ks := { R with lam := lam, kap := kap }

end Low

end GlobalTheory.BigOn

end
