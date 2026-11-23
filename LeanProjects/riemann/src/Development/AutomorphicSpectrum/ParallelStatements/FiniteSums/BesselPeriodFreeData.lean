import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.UnfDefs
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi
  Formalism.IndefR.Mult MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData

def IsCut {G : Type} [Group G] [MeasurableSpace G] (H : Subgroup G) (μH : Measure H) (β : G → ℝ) : Prop :=
  (∀ g, 0 ≤ β g) ∧ Measurable β ∧
    ∀ g, Integrable (fun r : H => β ((r : G) * g)) μH ∧ ∫ r : H, β ((r : G) * g) ∂μH = 1

def cutMeas {G : Type} [MeasurableSpace G] (ν : Measure G) (β : G → ℝ) : Measure G :=
  ν.withDensity fun g => ENNReal.ofReal (β g)

def partInt {X : ℕ → Type} [∀ j, MeasurableSpace (X j)] (α : ∀ j, Measure (X j)) (n : ℕ) (f : (∀ j, X j) → ℂ) :
    ℕ → (∀ j, X j) → ℂ :=
  fun d => Nat.rec (motive := fun _ => (∀ j, X j) → ℂ) f
    (fun d g x => ∫ t, g (Function.update x (n - d) t) ∂(α (n - d))) d

def level {X : ℕ → Type} [∀ j, MeasurableSpace (X j)] (α : ∀ j, Measure (X j)) (n : ℕ) (f : (∀ j, X j) → ℂ) (j : ℕ) :
    (∀ j, X j) → ℂ :=
  partInt α n f (n - j)

theorem level_top {X : ℕ → Type} [∀ j, MeasurableSpace (X j)] (α : ∀ j, Measure (X j)) (n : ℕ)
    (f : (∀ j, X j) → ℂ) : level α n f n = f := by
  simp [level, partInt]

theorem level_pred {X : ℕ → Type} [∀ j, MeasurableSpace (X j)] (α : ∀ j, Measure (X j)) (n : ℕ)
    (f : (∀ j, X j) → ℂ) (j : ℕ) (hj : j + 1 ≤ n) (x : ∀ j, X j) :
    level α n f j x = ∫ t, level α n f (j + 1) (Function.update x (j + 1) t) ∂(α (j + 1)) := by
  have key : ∀ d k, n - d = k → partInt α n f (d + 1) x = ∫ t, partInt α n f d (Function.update x k t) ∂(α k) := by
    intro d k h; subst h; rfl
  have h1 : n - j = (n - (j + 1)) + 1 := by omega
  unfold level
  rw [h1]
  exact key _ _ (by omega)

def IsFiniteSum {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (H : Subgroup G) (α : Measure G)
    (f : G → ℂ) : Prop :=
  ∃ (J : Subgroup G) (S : Finset G), IsOpen (J : Set G) ∧ IsCompact (J : Set G) ∧
    (∀ r ∈ H, ∀ k ∈ J, ∀ t, f (r * t * k) = f t) ∧
    (∀ s ∈ S, ∀ s' ∈ S, (∃ r ∈ H, ∃ k ∈ J, s' = r * s * k) → s' = s) ∧
    (∀ t, f t ≠ 0 → ∃ s ∈ S, ∃ r ∈ H, ∃ k ∈ J, t = r * s * k) ∧
    (∀ s ∈ S, α {t | ∃ r ∈ H, ∃ k ∈ J, t = r * s * k} < ⊤) ∧ Integrable f α ∧
    ∫ t, f t ∂α = ∑ s ∈ S, ((α {t | ∃ r ∈ H, ∃ k ∈ J, t = r * s * k}).toReal : ℂ) * f s

variable {D : D7}

def rho (D : D7) (j : ℕ) : ℕ := (D.R.m - 1 - j) / 2

def HasZ (D : D7) (j : ℕ) : Prop := (D.R.m - 1 - j) % 2 = 1

def hF (V : HSp D) (x y : Fin V.rank → D.host.E) : D.host.E := ∑ i, ∑ l, star (x i) * V.gram i l * y l

structure SlopeTestRemainingChoices (V : HSp D) where
  e : ℕ → Fin V.rank → D.host.E
  ev : ℕ → Fin V.rank → D.host.E
  z : Fin V.rank → D.host.E

example (V : HSp D) : SlopeTestRemainingChoices V := ⟨fun _ _ => 1, fun _ _ => 1, fun _ => 1⟩

def IsAuxiliaryHeckeCharacter (V : HSp D) (j T : ℕ) (A : SlopeTestRemainingChoices V) : Prop :=
  (∀ i < rho D j, ∀ l < rho D j, hF V (A.e i) (A.ev l) = (if i = l then 1 else 0) ∧ hF V (A.e i) (A.e l) = 0 ∧
    hF V (A.ev i) (A.ev l) = 0) ∧
  (HasZ D j → hF V A.z A.z = -(T : D.host.E) ∧ ∀ i < rho D j, hF V A.z (A.e i) = 0 ∧ hF V A.z (A.ev i) = 0)

def cols (V : HSp D) (x : ℕ → Fin V.rank → D.host.E) (n : ℕ) : Matrix (Fin V.rank) (Fin n) D.host.E :=
  fun r i => x i r

def Rgrp (V : HSp D) (j : ℕ) (A : SlopeTestRemainingChoices V) : Subgroup (GA D V) :=
  Subgroup.closure {g | (∀ i < rho D j, ∃ a : ℕ → AE D,
      subOne V g *ᵥ ratV (A.e i) = ∑ l ∈ Finset.range i, a l • ratV (A.e l)) ∧
    (HasZ D j → ∃ a : ℕ → AE D, subOne V g *ᵥ ratV A.z = ∑ l ∈ Finset.range (rho D j), a l • ratV (A.e l))}

def rationalFixingSubgroup (V : HSp D) (j : ℕ) (A : SlopeTestRemainingChoices V) : Subgroup (GA D V) :=
  GQ V ⊓ Rgrp V j A ⊓ Subgroup.closure {g | ∀ i < rho D j, subOne V g *ᵥ ratV (A.e i) = 0}

def xZero (V : HSp D) (j : ℕ) (A : SlopeTestRemainingChoices V) : Mx D V.rank (rho D j) :=
  fun r i => incA D (if Odd (j + 1) then D.host.xi0⁻¹ * A.e i r else if i.1 < rho D (j + 1) then A.e i r else A.z r)

def WeightGaps (D : D7) : Prop :=
  1800 < D.R.r + D.R.m * D.R.t ∧ ∀ τ (i : Fin D.R.m) (h : i.1 + 1 < D.R.m),
    2 * ((D.R.r + D.R.m * D.R.t : ℕ) : ℚ) ^ 3 + D.R.t + 3 ≤ (D.hc τ).b ⟨i.1 + 1, h⟩ - (D.hc τ).b i

def parPi (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : SPar :=
  Finset.univ.image fun i : Fin D.R.k => ((D.hcW u τ).u i, true)

abbrev Ginf (D : D7) (j : ℕ) : Type := GinfC (D.sp.Y j)

structure RealData (D : D7) (u : D.what₂.Word) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  η : (AE D)ˣ →* Circle
  aux : ∀ j, SlopeTestRemainingChoices (D.sp.Y j)
  s : ∀ j, D.what₂.Tau → Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) ℂ
  B : ∀ j, D.what₂.Tau → Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) ℂ
  npos : ℕ → D.what₂.Tau → ℕ
  Mπ : DSModel (D.sp.X 0) (parPi D u)
  Mσ : DSModel (D.sp.Y D.R.m) (parB (tparRec D) D.R.m)
  ν : ∀ j, Measure (Ginf D j)
  μR : ∀ j, Measure ((Rgrp (D.sp.Y j) j (aux j)).subgroupOf (GinfC (D.sp.Y j)))
  β : ∀ j, Ginf D j → ℝ

variable {u : D.what₂.Word}

def RealData.OK (R : RealData D u) : Prop :=
  IsInfFam R.θ ∧ IsStdChar D R.ψ (-1) ∧
  (∀ j < D.R.m, IsAuxiliaryHeckeCharacter (D.sp.Y j) j (D.mem u).A.T (R.aux j) ∧
    ∀ l, (∀ i < rho D j, hF (D.sp.Y j) (fun r => frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) r l) ((R.aux j).e i) = 0 ∧
        hF (D.sp.Y j) (fun r => frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) r l) ((R.aux j).ev i) = 0) ∧
      (HasZ D j → hF (D.sp.Y j) (fun r => frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) r l) (R.aux j).z = 0)) ∧
  (∀ j ≤ D.R.m, ∀ τ, IsCartanInv (gramAt D (D.sp.Y j) τ) (R.s j τ) ∧
    IsONBasis (gramAt D (D.sp.Y j) τ) (R.s j τ) (R.B j τ) (R.npos j τ)) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m → (R.ν j).IsHaarMeasure) ∧
  ∀ j, 1 ≤ j → j ≤ D.R.m - 2 → (R.μR j).IsHaarMeasure ∧ IsCut _ (R.μR j) (R.β j)

def RealData.α (R : RealData D u) (j : ℕ) : Measure (Ginf D j) := cutMeas (R.ν j) (R.β j)

structure RealVec (R : RealData D u) where
  v : ⨂[ℂ] τ, R.Mπ.H τ
  P : ∀ j, MvPolynomial (FVar D (D.sp.Y (j + 1)).rank (D.sp.Y j).rank) ℂ
  vt : ⨂[ℂ] τ, R.Mσ.H τ

example (R : RealData D u) : RealVec R := ⟨0, fun _ => 1, 0⟩

def IsRealIso (V V' : HSp D) (κ : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V.rank) ℂ)
    (κ' : D.what₂.Tau → Matrix (Fin V.rank) (Fin V'.rank) ℂ) : Prop :=
  ∀ τ, κ τ * κ' τ = 1 ∧ κ' τ * κ τ = 1 ∧ (κ τ)ᴴ * gramAt D V' τ * κ τ = gramAt D V τ

open Classical in

def IsTypeMap (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (V' : HSp D)
    (κ : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V.rank) ℂ) (κ' : D.what₂.Tau → Matrix (Fin V.rank) (Fin V'.rank) ℂ)
    (Φ : MultilinearMap ℂ (fun τ => M.H τ) (GA D V' → ℂ)) : Prop :=
  (∀ v, IsAutFun V' (Φ v)) ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ v : ∀ τ, M.H τ,
    Φ (Function.update v τ (M.rep τ g (v τ))) = rTr V' (atTau θ V' τ (κ τ * g * κ' τ)) (Φ v)

structure FreeData (R : RealData D u) where
  Y : ℕ → HSp D
  X0 : HSp D
  ι : X0.V →ₗ[D.host.E] (Y 0).V
  aux : ∀ j, SlopeTestRemainingChoices (Y j)
  κ : ∀ j, D.what₂.Tau → Matrix (Fin (Y j).rank) (Fin (D.sp.Y j).rank) ℂ
  κ' : ∀ j, D.what₂.Tau → Matrix (Fin (D.sp.Y j).rank) (Fin (Y j).rank) ℂ
  κX : D.what₂.Tau → Matrix (Fin X0.rank) (Fin (D.sp.X 0).rank) ℂ
  κX' : D.what₂.Tau → Matrix (Fin (D.sp.X 0).rank) (Fin X0.rank) ℂ
  tr : ∀ j, Ginf D j →* GinfC (Y j)
  μ : ℕ → (AE D)ˣ →* Circle
  om : ∀ j, GA D (Y j) × GA D (Y (j + 1)) →* Module.End ℂ (WO (Y j) (Y (j + 1)) → ℂ)
  vac : ∀ j, WO (Y j) (Y (j + 1)) → ℂ
  ph : MultilinearMap ℂ (fun τ => R.Mπ.H τ) (GA D X0 → ℂ)
  Ft : MultilinearMap ℂ (fun τ => R.Mσ.H τ) (GA D (Y D.R.m) → ℂ)
  bes : BesDat X0 (Y 0) ι
  emb : GA D X0 →* GA D (Y 0)
  μ0 : Measure (GA D X0)
  𝓕0 : Set (GA D X0)
  μN : Measure (NFlag (Y 0) bes.e)
  𝓕N : Set (NFlag (Y 0) bes.e)
  νf : ∀ j, Measure (GfC (Y j))
  μRf : ∀ j, Measure ((Rgrp (Y j) j (aux j)).subgroupOf (GfC (Y j)))
  βf : ∀ j, GfC (Y j) → ℝ
  𝓕Y : ∀ j, Set (GA D (Y j))
  𝓕R : ∀ j, Set (GA D (Y j))
  μL : ∀ j, Measure (Mx D (Y (j + 1)).rank (rho D j))
  𝓕L : ∀ j, Set (Mx D (Y (j + 1)).rank (rho D j))

namespace FreeData

variable {R : RealData D u} (fd : FreeData R)

def pt (j : ℕ) (x : Ginf D j) (y : GfC (fd.Y j)) : GA D (fd.Y j) := (fd.tr j x : GA D (fd.Y j)) * (y : GA D (fd.Y j))

def ν (j : ℕ) : Measure (GA D (fd.Y j)) :=
  Measure.map (fun q : Ginf D j × GfC (fd.Y j) => fd.pt j q.1 q.2) ((R.ν j).prod (fd.νf j))

def μR : ∀ j, Measure (GA D (fd.Y j))
  | 0 => Measure.map (fun q : NFlag (fd.Y 0) fd.bes.e × GA D fd.X0 => (q.1 : GA D (fd.Y 0)) * fd.emb q.2)
      (fd.μN.prod fd.μ0)
  | j + 1 => Measure.map (fun q : (Rgrp (D.sp.Y (j + 1)) (j + 1) (R.aux (j + 1))).subgroupOf (GinfC (D.sp.Y (j + 1))) ×
        (Rgrp (fd.Y (j + 1)) (j + 1) (fd.aux (j + 1))).subgroupOf (GfC (fd.Y (j + 1))) =>
      fd.pt (j + 1) q.1 q.2) ((R.μR (j + 1)).prod (fd.μRf (j + 1)))

def αf (j : ℕ) : Measure (GfC (fd.Y j)) := cutMeas (fd.νf j) (fd.βf j)

def sT (j : ℕ) (τ : D.what₂.Tau) : Matrix (Fin (fd.Y j).rank) (Fin (fd.Y j).rank) ℂ := fd.κ j τ * R.s j τ * fd.κ' j τ

def OK : Prop :=
  (∀ j ≤ D.R.m, IsRealIso (D.sp.Y j) (fd.Y j) (fd.κ j) (fd.κ' j) ∧
    ∀ (g : Ginf D j) τ, infMat D.sp.cm.sig (fd.Y j).gram (R.θ τ) (fd.tr j g : GA D (fd.Y j)) =
      fd.κ j τ * infMat D.sp.cm.sig (D.sp.Y j).gram (R.θ τ) (g : GA D (D.sp.Y j)) * fd.κ' j τ) ∧
  (∀ j < D.R.m, IsAuxiliaryHeckeCharacter (fd.Y j) j (D.mem u).A.T (fd.aux j) ∧ ∀ τ,
    (∀ i < rho D j, fd.κ j τ *ᵥ (fun r => tauE D τ ((R.aux j).e i r)) = (fun r => tauE D τ ((fd.aux j).e i r)) ∧
      fd.κ j τ *ᵥ (fun r => tauE D τ ((R.aux j).ev i r)) = (fun r => tauE D τ ((fd.aux j).ev i r))) ∧
    (HasZ D j → fd.κ j τ *ᵥ (fun r => tauE D τ ((R.aux j).z r)) = fun r => tauE D τ ((fd.aux j).z r))) ∧
  (IsRealIso (D.sp.X 0) fd.X0 fd.κX fd.κX' ∧ ∀ τ,
    fd.κ 0 τ * (frameMat (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0)).map (tauE D τ) =
      (frameMat (fd.Y 0) fd.X0 fd.ι).map (tauE D τ) * fd.κX τ) ∧
  (Formalism.IndefR.Lift.CharsOK fd.μ R.η D.R.m ∧
    ∀ (i : Fin D.R.m) τ, HasInfExp D (fd.μ (i.1 + 1)) τ (-(D.hc τ).e i)) ∧
  (∀ j < D.R.m, IsWeilDatumO R.ψ (fd.Y j) (fd.Y (j + 1)) (Formalism.IndefR.Lift.chrStep fd.μ R.η (j + 1)).1
      (Formalism.IndefR.Lift.chrStep fd.μ R.η (j + 1)).2 (fd.om j) ∧
    IsThetaFunO R.ψ (fd.Y j) (fd.Y (j + 1)) (fd.vac j) ∧
    ∀ τ, IsFockVacAt (heisO R.ψ (fd.Y j) (fd.Y (j + 1))) R.θ τ (cplxO (fd.sT j τ) (fd.sT (j + 1) τ)) (fd.vac j)) ∧
  IsTypeMap R.θ R.Mπ fd.X0 fd.κX fd.κX' fd.ph ∧
  IsTypeMap R.θ R.Mσ (fd.Y D.R.m) (fd.κ D.R.m) (fd.κ' D.R.m) fd.Ft ∧
  (fd.bes.ρ = rho D 0 ∧ (∀ r i, fd.bes.e r i = (fd.aux 0).e i r) ∧ fd.bes.z = (fd.aux 0).z ∧ (∀ i, fd.bes.c i = 1) ∧
    fd.bes.y = 1 ∧ BesStd R.ψ fd.bes fd.emb fd.μ0 fd.𝓕0 fd.μN fd.𝓕N) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m → (fd.νf j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (fd.Y j)) (fd.𝓕Y j) (fd.ν j)) ∧
  (∀ j, 1 ≤ j → j ≤ D.R.m - 2 → (fd.μRf j).IsHaarMeasure ∧ IsCut _ (fd.μRf j) (fd.βf j)) ∧
  (∀ j ≤ D.R.m - 2, IsFundamentalDomain (rationalFixingSubgroup (fd.Y j) j (fd.aux j)) (fd.𝓕R j) (fd.μR j)) ∧
  ∀ j < D.R.m - 2, IsCovolOne (ratMx D (fd.Y (j + 1)).rank (rho D j)) (fd.μL j) (fd.𝓕L j)

variable (da : RealVec R)

def phv : GA D fd.X0 → ℂ := PiTensorProduct.lift fd.ph da.v

def Phi (j : ℕ) : WO (fd.Y j) (fd.Y (j + 1)) → ℂ :=
  pureTensorL (fun k : FVar D (D.sp.Y (j + 1)).rank (D.sp.Y j).rank =>
    aPlus (heisO R.ψ (fd.Y j) (fd.Y (j + 1))) R.θ k.1 (cplxO (fd.sT j k.1) (fd.sT (j + 1) k.1))
      (fd.κ (j + 1) k.1 * unitMap (R.B j k.1) (R.B (j + 1) k.1) k.2.1 k.2.2 * fd.κ' j k.1)) (fd.vac j) (da.P j)

def row (j : ℕ) (hj : j ≤ D.R.m) : GA D (fd.Y j) → ℂ :=
  Nat.decreasingInduction (motive := fun j _ => GA D (fd.Y j) → ℂ)
    (fun k _ F g => ∫ h in fd.𝓕Y (k + 1), thetaKO (fd.om k) g h (fd.Phi da k) * F h ∂(fd.ν (k + 1)))
    (PiTensorProduct.lift fd.Ft da.vt) hj

def IsBesselPeriod (b : ℂ) : Prop :=
  IsBesPer R.ψ fd.bes fd.emb fd.μ0 fd.𝓕0 fd.μN fd.𝓕N (fd.phv da) (fd.row da 0 (Nat.zero_le _)) b

open Classical in

def theta0 (r : GA D (fd.Y 0)) : ℂ :=
  if h : ∃ q : NFlag (fd.Y 0) fd.bes.e × GA D fd.X0, r = (q.1 : GA D (fd.Y 0)) * fd.emb q.2 then
    fd.phv da h.choose.2 * star (besChar R.ψ fd.bes (h.choose.1 : GA D (fd.Y 0)))
  else 0

def kern (j : ℕ) (g : GA D (fd.Y j)) (g' : GA D (fd.Y (j + 1))) : ℂ :=
  RedS R.ψ (fd.Y j) (fd.Y (j + 1)) (cols (fd.Y j) (fd.aux j).e (rho D j)) (fd.μL j) (fd.𝓕L j)
    (fd.om j (g, g') (fd.Phi da j))
    (embP (fd.Y j) (fd.Y (j + 1)) (cols (fd.Y j) (fd.aux j).ev (rho D j)) (xZero (fd.Y (j + 1)) j (fd.aux (j + 1))))

def theta (h : ∀ j, GA D (fd.Y j)) : ∀ j, GA D (fd.Y j) → ℂ :=
  fun j => Nat.rec (motive := fun j => GA D (fd.Y j) → ℂ) (fd.theta0 da)
    (fun j Θ r' => ∫ r in fd.𝓕R j, Θ r * fd.kern da j (r * h j) (r' * h (j + 1)) ∂(fd.μR j)) j

def Q (x : ∀ j, Ginf D j) (y : ∀ j, GfC (fd.Y j)) : ℂ :=
  let h : ∀ j, GA D (fd.Y j) := fun j => if j = 0 then 1 else fd.pt j (x j) (y j)
  ∫ r in fd.𝓕R (D.R.m - 2), fd.theta da h (D.R.m - 2) r *
    fd.row da (D.R.m - 2) (Nat.sub_le _ _) (r * h (D.R.m - 2)) ∂(fd.μR (D.R.m - 2))

end FreeData

section Sep

variable {R : RealData D u} (a : RealVec R → (∀ j, Ginf D j) → ℂ) (p : ∀ fd : FreeData R, (∀ j, GfC (fd.Y j)) → ℂ)

def IsSep : Prop :=
  (∃ da x, a da x ≠ 0) ∧ ∀ fd : FreeData R, fd.OK → ∀ da x y, fd.Q da x y = a da x * p fd y

def Aj (da : RealVec R) (j : ℕ) : (∀ j, Ginf D j) → ℂ := level R.α (D.R.m - 2) (a da) j

def Pj (fd : FreeData R) (j : ℕ) : (∀ j, GfC (fd.Y j)) → ℂ := level fd.αf (D.R.m - 2) (p fd) j

def Live (j : ℕ) : Prop := ∃ fd : FreeData R, fd.OK ∧ ∃ y, Pj p fd j y ≠ 0

def AllLive : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m - 2 → Live p j

open Classical in

def Au (da : RealVec R) : ℂ := if AllLive p then Aj a da 0 1 else 0

def PartI : Prop :=
  ∀ fd : FreeData R, fd.OK → ∀ j, 1 ≤ j → j ≤ D.R.m - 2 → ∀ y,
    IsFiniteSum ((Rgrp (fd.Y j) j (fd.aux j)).subgroupOf (GfC (fd.Y j))) (fd.αf j)
      fun t => Pj p fd j (Function.update y j t)

def PartII : Prop :=
  AllLive p →
    (∀ da j, 1 ≤ j → j ≤ D.R.m - 2 → ∀ x, Integrable (fun t => Aj a da j (Function.update x j t)) (R.α j)) ∧
    ∀ fd : FreeData R, fd.OK → ∀ da, fd.IsBesselPeriod da (Aj a da 0 1 * Pj p fd 0 1)

def PartIII : Prop :=
  ¬ AllLive p → ∀ fd : FreeData R, fd.OK → Pj p fd 0 1 = 0 ∧ ∀ da, fd.IsBesselPeriod da 0

theorem sep_unique {a' : RealVec R → (∀ j, Ginf D j) → ℂ} {p' : ∀ fd : FreeData R, (∀ j, GfC (fd.Y j)) → ℂ}
    (h : IsSep a p) (h' : IsSep a' p') (hQ : ∃ fd : FreeData R, fd.OK ∧ ∃ da x y, fd.Q da x y ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ da x, a' da x = c * a da x := by
  obtain ⟨fd, hfd, da, x, y, hne⟩ := hQ
  have h1 : p fd y ≠ 0 := fun h0 => hne (by rw [h.2 fd hfd, h0, mul_zero])
  have h2 : p' fd y ≠ 0 := fun h0 => hne (by rw [h'.2 fd hfd, h0, mul_zero])
  refine ⟨p fd y / p' fd y, div_ne_zero h1 h2, fun da' x' => ?_⟩
  have := (h.2 fd hfd da' x' y).symm.trans (h'.2 fd hfd da' x' y)
  field_simp
  linear_combination -this

theorem besselPeriod_eq_Au_mul_projection (h2 : PartII a p) (h3 : PartIII p) (fd : FreeData R) (hfd : fd.OK) (da : RealVec R) :
    fd.IsBesselPeriod da (Au a p da * Pj p fd 0 1) := by
  unfold Au
  split_ifs with hl
  · exact (h2 hl).2 fd hfd da
  · simpa using (h3 hl fd hfd).2 da

end Sep

def Separation (D : D7) : Prop :=
  WeightGaps D → ∀ (u : D.what₂.Word) (R : RealData D u), R.OK →
    (∃ a p, IsSep (R := R) a p) ∧
    ∀ a p, IsSep (R := R) a p → PartI p ∧ PartII a p ∧ PartIII p

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData

end
