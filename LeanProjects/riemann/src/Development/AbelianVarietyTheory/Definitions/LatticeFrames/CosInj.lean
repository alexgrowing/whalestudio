import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl

variable {D : D7} {c : Comm D}

def SameOrb {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n] (J : Subgroup (GL (n ⊕ Fin 0) k))
    (M : Submodule 𝒪[k] (n → k)) (yb yb' : (n → k) ⧸ M) : Prop :=
  ∃ g ∈ J, ∃ y, Submodule.Quotient.mk y = yb ∧ Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) = yb'

set_option maxHeartbeats 4000000 in

structure QAt (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  ψk : AddChar k Circle
  char : (ofSplit q).IsChar c.ψ ψk
  cond : HasConductor ψk 1

  s : ℕ
  hs : s + 1 + 1 = D.R.m
  X : ℕ → Type
  [fX : ∀ j, Fintype (X j)]
  [dX : ∀ j, DecidableEq (X j)]
  Z : Type
  [fZ : Fintype Z]
  [dZ : DecidableEq Z]

  T : Chain k s X Z
  reg : T.Regular
  laws : T.Laws
  bas : ∀ j d h, T.bas j d h = 1
  le : ∀ j d h, (T.lev j d h).J ≤ KO k _
  leT : T.levTop.J ≤ KO k Z
  openT : IsOpen (T.levTop.J : Set (GL Z k))
  mu : ∀ j, j ≤ s + 1 → (ofSplit q).IsComp (χ j)⁻¹ (T.mu (j + 1)) ∧ IsOpen ((T.mu (j + 1)).ker : Set kˣ)

  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (X j)
  FT : Frame k c.T.rank Z
  FM : Frame k (c.X (s + 1 + 1)).rank (Z ⊕ Unit)
  FY : ∀ j d, j + d = s + 1 → Frame k (c.V j).rank (X j ⊕ Fin d)
  sc : ℕ → k
  sc_ne : ∀ j, sc j ≠ 0
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  bes : ∀ j ρ h d (hd : j + d = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j d hd)
  jac : ∀ j ρ h d (hd : j + 1 + d = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j) ((ofSplit q).hz (c.B j ρ h))
    (FX (j + 1) (by omega)) (FY (j + 1) d hd)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latY : ∀ j d hd (y : X j ⊕ Fin d → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FY j d hd).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (c.V j) (v.N j) (· = q.v)
  latT : ∀ y : Z → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV c.T v.NT (· = q.v)

  gl : ∀ j d, j + d = s + 1 → GL (X j ⊕ Fin d) k →* GA D (c.V j)
  gl_loc : ∀ j d hd g, (ofSplit q).IsLoc (FY j d hd) (gl j d hd g) g

  A : RepFam k s X
  reps : T.IsRepSystem A ψk ν
  Ch : ℕ → Type
  [fC : ∀ j, Fintype (Ch j)]
  rep : ∀ j d, j + d = s → Ch j → GL (X j ⊕ Fin (d + 1)) k
  rep_bij : ∀ j d h, Set.BijOn (rep j d h) Set.univ (A j d h)
  c₁ : kˣ
  c₂ : kˣ
  adapt : T.Adapted A (box _ c₁) (box _ c₂)
  cos : Ch (s + 1) → (X (s + 1) → k) ⧸ box (X (s + 1)) c₂
  cos_inj : ∀ y y', SameOrb (T.lev (s + 1) 0 rfl).J (box _ c₂) (cos y) (cos y') → y = y'
  cos_cov : ∀ yb ∈ T.coupIdx A (box _ c₁) (box _ c₂), ∃ y, SameOrb (T.lev (s + 1) 0 rfl).J (box _ c₂) (cos y) yb
  one : Fintype.card (Ch (s + 1 + 1)) = 1

  eL : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eLT : WO (c.V (s + 1)) c.T →₀ ℂ
  eL_at : ∀ j d (h : j + d = s), (ofSplit q).IsCombAt c.ψ (FY j (d + 1) (by omega)) (FY (j + 1) d (by omega)) (eL j) (T.Phi j d h)
  eLT_at : (ofSplit q).IsCombAt c.ψ (FY (s + 1) 0 rfl) FT eLT T.PhiTop

  dL : ∀ j, Ch j → Ch (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ
  dL_mid : ∀ j d (H : j + 1 + d = s) α γ, (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (dL j α γ)
    (T.entry ψk ν j d H (rep j (d + 1) (by omega) α) (rep (j + 1) d H γ))
  dL_pen : ∀ α y, (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (dL s α y)
    (T.xiPen (box _ c₂) (rep s 0 rfl α) (cos y))
  dL_top : ∀ y u, (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (dL (s + 1) y u) (T.xiTop (box _ c₂) ψk ν (-1) (cos y))

  εL : ∀ j, Ch j → GA D (c.V j) →₀ ℂ
  εL_at : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∀ d (h : j + d = s) α, ∃ e,
    IsOneComb ψk ν (ρ + 1) (T.lev j (d + 1) (by omega)) (rep j d h α) e ∧ εL j α = e.mapDomain (gl j (d + 1) (by omega))

  idx : ℕ → ℕ
  idx_mid : ∀ j d h, idx j = (T.lev j d h).J.relIndex (KO k _)
  idx_top : idx (s + 1 + 1) = T.levTop.J.relIndex (KO k Z)

  m : ∀ j, Measure (GL (X j) k)
  haar : ∀ j, (m j).IsHaarMeasure ∧ m j (KO k (X j)) = 1
  wt : ∀ j, Ch j → ℂ
  wt_mid : ∀ j d (h : j + d = s) α,
    wt j α = (((m j (prX (Cgrp (T.lev j (d + 1) (by omega)).J (rep j d h α)))).toReal⁻¹ : ℝ) : ℂ)
  wt_pen : ∀ y, wt (s + 1) y = idx (s + 1) * Nat.card {yb | SameOrb (T.lev (s + 1) 0 rfl).J (box _ c₂) (cos y) yb}
  wt_top : ∀ u, wt (s + 1 + 1) u = idx (s + 1 + 1)

attribute [instance] QAt.fld QAt.val QAt.top QAt.loc QAt.mea QAt.bor QAt.fX QAt.dX QAt.fZ QAt.dZ QAt.fC

def QAt.Typed {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j : ℕ) (f : GA D (c.V j) → ℂ) : Prop :=
  ∀ d (h : j + d = Q.s + 1) (x : (Q.T.lev j d h).J), rTrans (Q.gl j d h x.1) f = ((Q.T.lev j d h).lam x : ℂ) • f

def QAt.eT {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    WO (c.V (j + 1)) c.T →₀ ℂ :=
  (show Q.s = j by have := Q.hs; omega) ▸ Q.eLT

structure QFam (v : VCom c) (t : Tup c) where
  χ : ℕ → (AE D)ˣ →* Circle
  r : ℕ
  Q : Fin r → QAt v χ
  eqv : ∀ j, t.Ch j ≃ ∀ i, (Q i).Ch j

structure QFam.Pins {v : VCom c} {t : Tup c} (F : QFam v t) (w : VTup t) : Prop where
  inj : Function.Injective fun i => (F.Q i).q.v
  places : ∀ p, p ∈ w.Q ↔ ∃ i, (F.Q i).q.v = p
  kom : ∀ j, j < D.R.m → IsWeilDatumO c.ψ _ _ (F.χ j) (F.χ j) (t.kom j)
  mid : ∀ j σ h, ∃ χz : (AE D)ˣ →* Circle, (t.sBF j (σ + 1) h).χV = F.χ j * χz ∧ (t.sBF j (σ + 1) h).χW = F.χ j ∧
    (t.sFB j σ h).χV = F.χ (j + 1) ∧ (t.sFB j σ h).χW = F.χ (j + 1) * χz
  lastc : ∀ j h, (t.sBF j 0 h).χW = F.χ j
  eQ : ∀ j, j + 1 < D.R.m → w.eQ j = aconv (List.ofFn fun i => (F.Q i).eL j)
  eQT : ∀ j h, w.eQT j h = aconv (List.ofFn fun i => (F.Q i).eT j h)
  dQ : ∀ j, j < D.R.m → ∀ α γ, w.dQ j α γ =
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i))
  ε : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∀ α, w.ε j α =
    (∏ i, (F.Q i).wt j (F.eqv j α i)) • conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i))
  εT : ∀ n h β, w.εT n h β = Finsupp.single 1 (∏ i, (F.Q i).wt n (F.eqv n β i))
  FY : ∀ j, j < D.R.m → ∀ f ∈ w.FY j, ∀ i, (F.Q i).Typed j f
  cQ : ∀ j, j + 2 ≤ D.R.m → w.cQ j = ∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹

def QPin (v : VCom c) {t : Tup c} (w : VTup t) : Prop := ∃ F : QFam v t, F.Pins w

end GlobalTheory.QPl
end
