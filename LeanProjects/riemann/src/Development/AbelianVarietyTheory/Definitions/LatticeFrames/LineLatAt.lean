import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

def idV (𝔞 : FI D) (v : Pl D) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ w, w ≠ v → evalV D.host.F w α = 0) ∧ ∃ a ∈ 𝔞,
    y = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a}

def dI (D : D7) : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar

def cI (D : D7) (j : ℕ) : FI D :=
  FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (j / 2)) * (D.host.AA * D.host.AAbar⁻¹) ^ ((D.R.m - j) / 2)

def bI (D : D7) (j ρ i : ℕ) : FI D := dI D ^ (ρ - i) * cI D j

def MonoId {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) : Prop :=
  MonoAt d L L₀ v ∧ ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a ∈ idV (𝔟 i) v

def LineId {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a ∈ idV 𝔠 v

def LineLatAt (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (LL : Lat L) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV ζ ∈ latV L LL (· = v) ↔ a ∈ idV 𝔠 v

variable {a : XPart D u}

structure YPart.Sk (b : YPart a) (ζ₀ : Fin a.Lz.rank → D.host.E)
    (τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (b.bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E) : Prop where
  base : (a.dat b).Base
  chBF : ∀ j ρ h, (b.sBF j ρ h).χV = a.c.chS (j + 1) ∧ (b.sBF j ρ h).χW = a.c.chT (j + 1)
  chFB : ∀ j σ h, (b.sFB j σ h).χV = a.c.chS (j + 1 + 1) ∧ (b.sFB j σ h).χW = a.c.chT (j + 1 + 1)
  norm : ∀ j ρ h, (star (b.bes j ρ h).ζ ⬝ᵥ (b.bes j ρ h).L.gram *ᵥ (b.bes j ρ h).ζ) *
    (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)
  tau : ∀ j h, τ j h *ᵥ ζ₀ = D.host.xi0 ^ (D.R.m / 2) • (b.bes j 0 h).ζ

@[reducible] def YPart.withT (b : YPart a) (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V) : YPart a := { b with t := t }

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {o : OffX a k ι} {b : YPart a}

structure CoreLat (o : OffX a k ι) (b : YPart a)
    (β₀ : ∀ j ρ h i, Frame (o.p i) (b.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)) (M : ∀ j ρ h, Lat (b.bes j ρ h).V₀) : Prop where
  sd : ∀ j ρ h, IsSelfDualC _ (M j ρ h)
  glued : ∀ j ρ h i, GluedCore ((a.dat b).B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i)
  split : ∀ j ρ h, ∃ LL, IsSelfDualC (b.bes j ρ h).L LL ∧ ∀ v, ¬ o.atT v →
    LineLatAt _ (b.bes j ρ h).ζ (cI D j) LL v ∧ OrthAt (b.bes j ρ h).o (M j ρ h) (a.x j).L LL v
  line : ∀ j ρ h v, LineId (b.bes j ρ h).o (b.bes j ρ h).ζ (M j ρ h) (cI D j) v

structure BigLat (y : OffY o b) : Prop where
  core : CoreLat o b y.β₀ y.M
  moves : ∀ j, j < D.R.m → IsSelfDualC ((a.dat b).st j).V (y.L j) ∧
    ∀ P, Moves ((a.dat b).st j).V (b.t j) ((a.dat b).st j).Λ (y.L j) P
  even : ∀ j ρ h v, v ∉ a.c.S → MonoId (b.bes j ρ h).d (y.L j) (y.M j ρ h) (bI D j ρ) v
  odd : ∀ j ρ h v, v ∉ a.c.S →
    MonoId (b.jac j ρ h).d (y.L (j + 1)) (a.x (j + 1)).L (fun i => D.host.AA⁻¹ * bI D j ρ i) v

open GlobalTheory.LocMod in

structure GY {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GX a ζ₀ PP) (b : YPart a)
    (τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (b.bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E) where
  FY : ∀ j c, j + c = G.s + 1 → GlobalTheory.LocMod.Frame G.k ((a.dat b).st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)
  sc : ℕ → G.k
  sc_unit : ∀ j, valuation G.k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit G.q).xi
  hz_unit : ∀ j ρ h, valuation G.k ((ofSplit G.q).hz ((a.dat b).B j ρ h)) = 1
  bes : ∀ j ρ h c (hc : j + c = G.s + 1),
    (ofSplit G.q).IsBesFrame ((a.dat b).B j ρ h) (sc j) (G.FX j (by omega)) (FY j c hc)
  jac : ∀ j ρ h c (hc : j + 1 + c = G.s + 1), (ofSplit G.q).IsJacFrame ((b.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit G.q).hz ((a.dat b).B j ρ h)) (G.FX (j + 1) (by omega)) (FY (j + 1) c hc)
  tau : ∀ h, (τ G.s h).map (ofSplit G.q).pr *ᵥ G.z₀ =
    (-((ofSplit G.q).xi * sc G.s)) • fun i => (ofSplit G.q).pr ((b.bes G.s 0 h).ζ i)

open GlobalTheory.LocMod in

def GY.Framed {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} {G : GX a ζ₀ PP} {τ} (H : GY G b τ)
    (t : ∀ j, GA D ((a.dat b).st j).V) : Prop :=
  ∀ j c (hc : j + c = G.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin ((a.dat b).st j).V.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit G.q) ((a.dat b).st j).V (t j) ((a.dat b).st j).β
      (((H.FY j c hc).β * ((G.S.T (Fin D.R.t)).bas j c hc).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i))

structure YGood (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1) (b : YPart a) (y : OffY o b)
    (H : ∀ PP, GY (G PP) b y.τ) : Prop where
  sk : b.Sk o.ζ₀ y.τ
  lat : BigLat y
  framed : ∀ PP, (H PP).Framed b.t

theorem cI_step (D : D7) {j : ℕ} (h : j + 1 + 1 ≤ D.R.m) :
    FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j = D.host.AA * D.host.AAbar⁻¹ * cI D (j + 1 + 1) := by

  have h1 : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
  have h2 : (D.R.m - j) / 2 = (D.R.m - (j + 1 + 1)) / 2 + 1 := by omega
  rw [cI, cI, h1, h2, pow_succ, pow_succ, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
  ring

theorem idV_mono {𝔞 𝔟 : FI D} (h : 𝔞 ≤ 𝔟) (v : Pl D) : idV 𝔞 v ≤ idV 𝔟 v := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, hv, x, hx, rfl⟩
  exact ⟨α, hα, hv, x, h hx, rfl⟩

theorem idV_zero (v : Pl D) : idV (0 : FI D) v = ⊥ := by

  rw [idV, AddSubgroup.closure_eq_bot_iff]
  rintro y ⟨α, -, -, x, hx, rfl⟩
  obtain rfl : x = 0 := by simpa using hx
  simp

theorem YPart.Sk.withT {ζ₀ : Fin a.Lz.rank → D.host.E} {τ} (h : b.Sk ζ₀ τ) (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V)
    (ht : ∀ j, t j ∈ GfC _) : (b.withT t).Sk ζ₀ τ where
  base := by

    have hb := h.base
    exact { hb with t := ht }
  chBF := h.chBF
  chFB := h.chFB
  norm := h.norm
  tau := h.tau

theorem CoreLat.withT {β₀ M} (h : CoreLat o b β₀ M) (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V) :
    CoreLat o (b.withT t) β₀ M := by
  refine ⟨h.sd, ?_, h.split, h.line⟩
  exact h.glued

def GY.withT {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} {G : GX a ζ₀ PP} {τ} (H : GY G b τ)
    (t : ∀ j, GA D ((a.geo b.bot b.mid).st j).V) : GY G (b.withT t) τ :=
  ⟨H.FY, H.sc, H.sc_unit, H.sc_step, H.hz_unit, H.bes, H.jac, H.tau⟩

example (h : FactPrincipalDatum) : dI D * ((D.host.ddE : Ideal (𝓞 D.host.E)) : FI D) = 1 := h _ D.host

example (b : YPart a) : b.withT b.t = b := rfl

example (j : ℕ) : bI D j 1 0 = dI D * cI D j := by simp [bI]

example {S S₀ : HSp D} (d : HypDec S S₀ 0) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) :
    MonoId d L L₀ 𝔟 v ↔ MonoAt d L L₀ v :=
  ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩

end GlobalTheory.SeeSaw

end
