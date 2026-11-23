import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri
open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem reference_tuple_used (D : D7) : Used0 D D.what₂.mu0 := Or.inl rfl

abbrev t0 (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : T := Y.tupT D.what₂.mu0

def repY (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : D.what₂.FT → NG.FinTyp D.host.E D.R.r :=
  fun σ => rowRepR R.θ (Y.eFT σ)

def IsCanonR (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (i : Fin D.R.m) {j : ℕ} (hj : i.1 + 1 = j) (X : GlobalTheory.NPin.RowMod D rep j) : Prop :=
  ∃ (e : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    X.C.map e = Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) ∧
    (∀ h x, e (X.ρ h x) = actM (Y.PW i) (R.MW i (sg0 D A3.A)) h (e x)) ∧
    (∀ x ∈ X.C, ∀ y ∈ X.C, X.B x y = (c : ℂ) * Mult.ipM (R.MW i (sg0 D A3.A)) (R.νW i) (R.fdW i) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (i.1 + 1), PiTensorProduct.lift (e (X.φ (hj ▸ y))) = (Y.IL.jMj i y).1

variable {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def eC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A)) :=
  Classical.choose hc

def cC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : ℝ :=
  Classical.choose (Classical.choose_spec hc)

def yv {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥X.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D i) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype)
      (kUnit (R.MW i (sg0 D A3.A)))) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ eC hc ∘ₗ X.C.subtype

variable {M : MtFam D}

def fV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) :
    ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ]
      (Formalism.L2.Theta.GA D (Vc D i) → (R.cV i).W) :=
  (R.cV i).ext ∘ₗ
    { toFun := fun F k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
        ((F : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }

def omStd (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (t : T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
  (R.ωP i t).comp ((Ad.PV i).ψ.prodMap (Y.PW i).ψ)

def Om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    Submodule ℂ ((R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) :=
  OmSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(Om Ad i hc) :=
  omSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def lamV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (φ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y : ↥X.C) : ℂ :=
  GlobalTheory.ThetaTri.lamV (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) φ Fm y

def lamL (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥(Om Ad i hc) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ :=
  lam (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) R.ψ
    (omStd Ad i (t0 Y))

variable (Y) in

def phi0 (i : Fin D.R.m) : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A3.A))) (R.BV i)
    (onb (R.MW i (sg0 D A3.A))) (R.vP i (t0 Y)) ∘ₗ R.ioP i (kUnit (R.MW i (sg0 D A3.A)))

end GlobalTheory.RefTheta

end
