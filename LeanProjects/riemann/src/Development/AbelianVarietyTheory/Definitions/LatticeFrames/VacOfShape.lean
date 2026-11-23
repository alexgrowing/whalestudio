import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure TDat (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) where

  p : ι → SplitPt D k
  I : List ι

  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)
  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  ζ₀ : Fin c.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def TDat.Ram (o : TDat c k ι) (j : ℕ) : Set (GA D (c.X j) → ℂ) := {φ | IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ}

def TDat.S (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (φ : GA D (c.X j) → ℂ) : GA D (c.X j) → ℂ :=
  o.I.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i) φ') φ

def TDat.mono (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (μ : (AE D)ˣ →* Circle) : ℂ :=
  (o.I.map fun i => (r i : ℂ) * chrPow μ ((o.p i).idele o.q.unit) (e i)).prod

@[reducible] def VCom.withT (v : VCom c) (Sad : ∀ j, (GA D (c.X j) → ℂ) → GA D (c.X j) → ℂ)
    (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) : VCom c := { v with Sad := Sad, op := op }

variable (v : VCom c) (o : TDat c k ι)

structure GoodAt (x : Pl D) : Prop where
  bf : ∀ j ρ h, GoodBF c.ψ (c.B j ρ h) (c.J j ρ h) (v.N j) (o.M j ρ h) (v.N (j + 1)) (c.x (j + 1)).L x
  fb : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), AdaptFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (v.N (j + 1))
    (c.x (j + 1)).L (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) x

structure SplitAt (x : Pl D) : Prop where
  core : ∀ j ρ h, ∃ LL, IsSelfDualC (c.bes j ρ h).L LL ∧ OrthAt (c.bes j ρ h).o (o.M j ρ h) (c.x j).L LL x
  top : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (LL : Lat (c.bes j 0 h).L) (LZ : Lat c.Lz),
    IsSelfDualC _ LL ∧ IsSelfDualC _ LZ ∧ OrthAt (c.bes j 0 h).o (o.M j 0 h) (c.x j).L LL x ∧
    OrthAt (c.oT (j + 1 + 1) h) (c.x (j + 1 + 1)).L v.NT LZ x ∧
    ∀ w ∈ latO (c.X (j + 1)) c.Lz ((c.x (j + 1)).L : Set _) (LZ : Set _) (· = x),
      kap (v.τ j h) (c.X (j + 1)) w ∈ latO (c.bes j 0 h).L (c.X (j + 1)) (LL : Set _) ((c.x (j + 1)).L : Set _) (· = x)

structure PreT : Prop where
  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  inj : Function.Injective fun i => (o.p i).v
  tP : ∀ x, x ∈ v.tP ↔ ∃ i, x = (o.p i).v
  char : ∀ i, (o.p i).IsChar c.ψ (o.χ i) ∧ (o.p i).UnitAA
  latT : ∀ j, j ≤ D.R.m → ∀ i, (o.β j i).IsLat (c.x j).L (o.Q j i).lat
  line : IsLineVec c.Lz o.ζ₀
  tau : ∀ j h, (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram

  lam : ∀ j h, ∃ lam : D.host.E, v.τ j h *ᵥ o.ζ₀ = lam • (c.bes j 0 h).ζ ∧
    ∀ i, valuation k ((o.p i).pr (incA D lam)) = 1 ∧ valuation k ((o.p i).pr (incA D (star lam))) = 1
  normT : ∀ i, valuation k ((o.p i).pr (incA D (star o.ζ₀ ⬝ᵥ c.Lz.gram *ᵥ o.ζ₀))) = valuation k ((o.q.1 : 𝒪[k]) : k)

  topT : ∀ n (h : n = D.R.m) i, IsSumFrame (c.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i) ∧
    ∃ (Λ : Submodule 𝒪[k] (Fin c.T.rank → k)) (s : 𝓀[k]ˣ), (o.γ i).IsLat v.NT Λ ∧
      (∀ y, y ∈ (o.Q n i).ker ↔ ((o.γ₀ n h i).b' * (o.β n i).b) *ᵥ y ∈ lastKer Λ) ∧
      (o.Q n i).HasVal (((o.β n i).b' * (o.γ₀ n h i).b) *ᵥ (o.q.inv • avec k (Fin c.T.rank) 1 1)) s

structure ShapeOff : Prop where
  pre : PreT v o
  good : ∀ x, GoodAt v o x
  split : ∀ x, x ∉ v.tP → SplitAt v o x
  glued : ∀ j ρ h i, GluedCore (c.B j ρ h) (o.M j ρ h) o.q (o.β j i) (o.β₀ j ρ h i) (o.Q j i)
  rep : ∀ j, j < D.R.m → ∀ f, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L (· ∈ v.tP) f →
    OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb c.ψ _ _ (v.dT j) f)
  ram : ∀ j, v.RamAd j = o.Ram j

structure Tup.UnrOn (t : Tup c) (P : Pl D → Prop) : Prop where
  bf : ∀ j ρ h x, P x → UnrAt (t.sBF j ρ h) x
  fb : ∀ j σ h x, P x → UnrAt (t.sFB j σ h) x
  top : ∀ j h, ∃ χS χT, IsWeilDatumO c.ψ _ _ χS χT (t.omT j h) ∧ ∀ x, P x → CharUnramAt D χS x ∧ CharUnramAt D χT x

def Tup.UnrK (t : Tup c) (P : Pl D → Prop) : Prop :=
  ∀ j, j < D.R.m → ∃ χS χT, IsWeilDatumO c.ψ _ _ χS χT (t.kom j) ∧ ∀ x, P x → CharUnramAt D χS x ∧ CharUnramAt D χT x

def OffOfShape (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → v.Is → ShapeOff v o → ∀ (t : Tup c) (w : VTup t), t.Is → Disjoint w.Q v.tP → t.UnrOn (offP v w) → OffLaw v w

def VacOfShape (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → v.Is → ShapeOff v o → ∀ t : Tup c, VacLaw (t := t) v

def TOfShape (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → v.Is → ShapeOff v o →
    ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ),
      (∀ j i, 0 < r j i) ∧ (v.withT (o.S ε) op).Is ∧
      ∀ (t : Tup c) (w : VTup t), t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) →
        (∀ j ρ h, w.cT j = o.mono (r j) (e j) (t.sBF j ρ h).χW) → TLaw (v.withT (o.S ε) op) w

def ShapeEx (D : D7) : Prop :=
  ∀ (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
    c.Is → Disjoint v.gP v.tP → IsSelfDualC c.T v.NT → PreT v o → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j)) →
    (∀ x ∈ v.gP, GoodAt v o x ∧ SplitAt v o x) →
    (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) →
    ∃ (N : ∀ j, Lat (c.V j)) (dT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
      (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)),
      (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j) ∧ ∀ x ∈ v.gP, latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
      (∀ j ρ h, ∀ x ∈ v.gP, latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
      (∀ j, CombAt (· ∈ v.tP) (dT j)) ∧
      ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ }

end GlobalTheory.SeeSaw

end
