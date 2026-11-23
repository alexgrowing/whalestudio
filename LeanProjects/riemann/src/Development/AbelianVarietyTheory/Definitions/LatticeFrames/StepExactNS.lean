import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def trivAt (Pg P : Finset (Pl D.host.E)) (r : ℕ) : Subgroup (G0 P r) where
  carrier := {g | ∀ PP : P, PP.1 ∈ Pg → g PP = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb PP h => by rw [Pi.mul_apply, ha PP h, hb PP h, mul_one]
  inv_mem' := fun {a} ha PP h => by rw [Pi.inv_apply, ha PP h, inv_one]

open Classical in

def comR (t : T) : Com D :=
  ⟨R.θ, R.ψ, R.toLevCh.mu t, R.eta, R.Pg ∪ R.Q t, ⟨trivAt R.Pg (R.Pg ∪ R.Q t) D.R.r, 1⟩,
    fun j PP => if PP ∈ R.Q t then (R.xiR t PP)⁻¹ else R.chi j PP⟩

def twR (t : T) : Twist D := ⟨R.Pg, R.Q t, R.chi, R.xiR t⟩

def stY (t : T) (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), R.MY j, R.ΛY j, R.βY j, R.datYt t j R.triv, R.νY t j, R.fdY t j⟩

def stX (t : T) : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, R.MX, R.ΛX, R.βX, R.datXt t, R.νX t, R.fdX t⟩

def RangeX : Prop := ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
  MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (Lev.levChi _ R.βX (R.datXt t))

def stepY (t : T) (k : ℕ) : Step (comR R t) (stY R t k) (stY R t (k + 1)) := ⟨R.ωY t k, R.vY t k, R.ItY k, R.ioY t k⟩

def stepX (h : RangeX R) (t : T) : Step (comR R t) (stY R t (D.R.m - 1)) (stX R t) :=
  ⟨R.ωX t, R.vX t, R.ItX, (R.ioX t ∘ₗ (LinearEquiv.ofEq _ _ (h t).symm).toLinearMap :
    MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (Lev.levChi _ R.βX (R.datXt t)) →ₗ[ℂ] R.CC t (D.R.m - 1))⟩

def toCC (h : RangeX R) (t : T) (x : (R.HX t).H) : (stX R t).CC (comR R t) :=
  LinearEquiv.ofEq _ _ (h t) ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x)

def RChain (h : RangeX R) : Prop := ∀ t, (twR R t).Is (comR R t) ∧ (∀ j < D.R.m, IsStage (comR R t) (twR R t) j (stY R t j)) ∧
  IsStage (comR R t) (twR R t) D.R.m (stX R t) ∧ (∀ k, k + 1 < D.R.m → IsStep (twR R t) (k + 1) (stepY R t k)) ∧
  IsStep (twR R t) D.R.m (stepX R h t)

def NormX (h : RangeX R) : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ t, Function.Bijective (toCC R h t) ∧
  ∀ ipD ip, IsMet (comR R t) (stX R t) ipD ip → ∀ x y : (R.HX t).H, ⟪x, y⟫_ℂ = (δ : ℂ) * ip (toCC R h t y) (toCC R h t x)

def RMeas : Prop := ∀ j < D.R.m, ∃ mR : Measure (GinfC (Yc D j)), ∀ t, IsLevMeas (stY R t j) mR

def RVol : Prop := ∀ t, (∀ j < D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY t j) =
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY A.μ0 j) * ∏ PP ∈ R.Q t, idxQ PP j ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY t j)) ∧
  GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX A.μ0) * ∏ PP ∈ R.Q t, idxQ PP D.R.m ∧
  0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t)

def RNrm : Prop := ∀ t, (∀ k, k + 1 < D.R.m → ∀ m X, IsCovolOne (ratL (Yc D (k + 1)) (Yc D k)) m X →
    nrm2 m X (R.vY t k) = nrm2 m X (R.vY A.μ0 k) * ∏ PP ∈ R.Q t, volOne PP (k + 1)) ∧
  ∀ m X, IsCovolOne (ratL D.sp.X' (Yc D (D.R.m - 1))) m X → nrm2 m X (R.vX t) = nrm2 m X (R.vX A.μ0) * ∏ PP ∈ R.Q t, volOne PP D.R.m

def IsUnif (k : ℕ) (s s' : T → PiLocalization₂ D) (p : ∀ t, Step (comR R t) (s t) (s' t)) (K : ℂ)
    (P : ∀ t, PolF D (s' t).V.rank (s t).V.rank) (v : ∀ t, (s t).M.Vec) : Prop :=
  K ≠ 0 ∧ ∀ t, ∃ m X mR H₀, IsCovolOne (ratL (s' t).V (s t).V) m X ∧ IsLevMeas (s t) mR ∧
    RealConv (p t) m X (P t) (v t) mR ∧ IsHval (comR R t) (twR R t).S₀ k H₀ ∧ kapOf (twR R t) k (p t) m X mR (P t) (v t) H₀ = K

def RUnif (h : RangeX R) : Prop :=
  (∀ k, k + 1 < D.R.m → ∃ (K : ℂ) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec),
    IsUnif R k (fun t => stY R t k) (fun t => stY R t (k + 1)) (fun t => stepY R t k) K (fun _ => φ) fun _ => v) ∧
  ∃ (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec),
    IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K (fun _ => φ) fun _ => v

def RowPar : Prop := ∀ (t : T) (c : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.EigSys D),
  (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥ → ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B) ∧
  ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, ∃ hu : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t),
    u ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B →
      IsPar (c := comR R t) (s := stY R t 0) ⟨_, hu⟩ B

def IPDict : Prop := ∀ t, ∀ k < D.R.m, ∀ ipD ip, IsMet (comR R t) (stY R t k) ipD ip → ∀ (x y : (stY R t k).CC (comR R t)) (a : ℂ),
  GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) a ↔ a = ip y x

def StepExactNS (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ ipD ip, IsMet c s ipD ip → ∀ m X, IsCovolOne (ratL s'.V s.V) m X →
  ∀ mR, IsLevMeas s mR → ∀ φ v, RealConv p m X φ v mR → ∀ (u₁ u₂ : s.CC c) B, IsPar u₁ B → IsQ w k u₁ →
    (∃ q ∉ c.S, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧ GlobalTheory.Core.Rk.SW.NSAt B (c.chT (k + 1)) D.R.t q) →
    ∀ l, GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B (c.chT (k + 1)) (z + 1 / 2)) ((D.R.t : ℂ) / 2) l →
      s'.pet (p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (p.up φ (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))) =
        conj ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (l / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR) * ip u₁ u₂

example (t : T) : (comR R t).μ = R.toLevCh.mu t := rfl

end GlobalTheory.ChainTw

end
