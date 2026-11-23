import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc

variable {D : D7}

set_option genSizeOfSpec false in
set_option genInjectivity false in

structure Gen (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [MeasurableSpace Y] where
  d : HypDec V V₀ ρ
  χV : (AE D)ˣ →* Circle
  χW : (AE D)ˣ →* Circle
  om : Om V W
  vS : VolM D W.rank ρ
  vN : VolN d
  vb : VolM D ρ V₀.rank
  vU : VolU D ρ
  vW : GlobalTheory.Unf.Vol W
  x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E
  m : Measure Y
  g : Y → GA D V₀
  Th : Y → GA D V → ℂ

namespace Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]
  (a : Gen ψ V V₀ W ρ Y)

structure Is : Prop where
  weil : IsWeilDatumO ψ V W a.χV a.χW a.om
  base : IsBase W a.x₀
  sfin : SFinite a.m
  g : Continuous a.g
  th : ∀ y, IsTh ψ a.d W a.x₀ (a.Th y)
  cont : Continuous fun p : Y × flagN a.d => a.Th p.1 p.2.1
  small : ∃ M : Y → ℝ, Measurable M ∧ (∀ y, ∀ n ∈ flagN a.d, ‖a.Th y n‖ ≤ M y) ∧
    ∀ k : ℕ, Integrable (fun y => M y * quotHeight V₀ (a.g y) ^ k) a.m

def lhs (G : GA D W → ℂ) (Φ : WO V W → ℂ) : ℂ :=
  ∫ y, (∫ n in a.vN.𝓝, a.Th y n.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (n.1 * a.d.emb0 (a.g y)) ∂a.vN.ν) ∂a.m

def ker (G : GA D W → ℂ) (Φ : WO V W → ℂ) (h : GA D W) : ℂ :=
  G h * ∫ y, fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.m

def tot (G : GA D W → ℂ) (Φ : WO V W → ℂ) (p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) : ℂ :=
  G p.1.1 * flFun ψ a.d W a.vS (a.Th p.1.2) (rat a.x₀) (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) p.2.1 p.2.2

def totMeas (𝓑 : Set (GA D W)) : Measure ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) :=
  ((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))

end Gen

def strip (W : HSp D) (R : Subgroup (GA D W)) (C : Set (GA D W)) : Set (GA D W) := {h | ∃ r ∈ R, ∃ c ∈ C, ∃ b ∈ GfC W, h = r * c * b}

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (v : CoreVol G) (F : Frames G)
  (Ψ : ∀ i, Fn G (.core i)) (u : GA D (Yc D 0) → ℂ)

def NZJ (ΓL : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))) (k : ℕ) (h : 2 * k + 2 ≤ D.R.m) : Prop :=
  ∃ (χ' : (AE D)ˣ →* Circle) (omz : Om (G.V (.core (2 * k + 1))) (negSp F.Lz)), IsWeilDatumO W.ψ _ _ χ' L.eta omz ∧
    ∃ ρ Φ Φ₀, VacG W.ψ _ _ (ΓL k) Φ₀ ∧
      (F.jac v k h).per W.ψ (F.ζ k) omz (star (Ψ (2 * k + 1))) (star (part W M ρ Φ u (2 * k + 1) (by omega))) Φ₀ ≠ 0

def NZB (k : ℕ) (h : 2 * k + 2 ≤ D.R.m) : Prop :=
  ∃ ρ Φ, (F.bes v k h).per W.ψ (star (Ψ (2 * k + 2))) (star (part W M ρ Φ u (2 * k + 2) h)) ≠ 0

def OnTower (Q : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (_ : G.Weil) (_ : GlobalTheory.FunObj.Vol G) (_ : CoreVol G)
    (F : Frames G) (_ : ∀ i, Fn G (.core i)) (_ : GA D (Yc D 0) → ℂ) (_ : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))), Prop) :
    Prop :=
  All fun {_} _ _ _ {G} W M => ∀ (v : CoreVol G) (F : Frames G) ΓL, F.Ends v W M → F.Good v W ΓL → ∀ Ψ, IsColChain W v Ψ →
    ∀ u, RapidRow W M u → Q W M v F Ψ u ΓL

def Rung0 : Prop := OnTower fun {_} _ _ _ {G} W M v F Ψ u ΓL => per0 G M (Ψ 0) u ≠ 0 → ∀ h, NZJ W M v F Ψ u ΓL 0 h

def RungB : Prop := OnTower fun {_} _ _ _ _ W M v F Ψ u ΓL => ∀ k h, NZJ W M v F Ψ u ΓL k h → NZB W M v F Ψ u k h

def RungJ : Prop := OnTower fun {_} _ _ _ _ W M v F Ψ u ΓL => ∀ k h h', NZB W M v F Ψ u k h' → NZJ W M v F Ψ u ΓL (k + 1) h

def ConjRead : Prop := All fun {D} _ {L} _ {G} W M => ∀ i, ∀ hi : i < D.R.m,
  IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧
  IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - i))⁻¹ (G.ch.chi (D.R.m - i))⁻¹ (omCore W i) ∧
  (Odd i → (G.chrS (.chi i 0))⁻¹ = (G.ch.chi (D.R.m - i))⁻¹ * L.eta ∧ G.chrT (.chi i 0) = G.ch.chi (D.R.m - i)) ∧
  (Even i → (G.chrT (.chi i 0))⁻¹ = (G.ch.chi (D.R.m - i))⁻¹ * L.eta ∧ G.chrS (.chi i 0) = G.ch.chi (D.R.m - i)) ∧
  (∀ f, Dep W (.core i) f ↔ VacG W.ψ _ _ (latCore G i) (star f)) ∧
  (∀ (v : CoreVol G) f Ψ, star (dn W v i f Ψ) = liftT (omCore W i) (v (i + 1)).μ (v (i + 1)).𝓕 (star Ψ) (star f)) ∧
  (∀ ρ Φ u, star (part W M ρ Φ u (i + 1) hi) =
    liftS (omRow W i) (M.ν (.grid i 0)) (M.fd (.grid i 0)) (star (part W M ρ Φ u i hi.le)) (star (W.datum ρ Φ ⟨i, hi⟩))) ∧
  (∀ ρ Φ ρ' Φ' u, (∀ j : Fin D.R.m, j.1 < i → ρ j = ρ' j ∧ Φ j = Φ' j) → part W M ρ Φ u i hi.le = part W M ρ' Φ' u i hi.le) ∧
  (M.ν (.grid i 0)).IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V (.grid i 0))) (M.fd (.grid i 0)) (M.ν (.grid i 0))

def PartFixed : Prop := All fun {_} _ _ _ {G} W M => ∀ ρ Φ u i h, ∀ k ∈ lev G (.grid (i + 1) 0), ∀ g,
  part W M ρ Φ u (i + 1) h (g * k) = part W M ρ Φ u (i + 1) h g

example (W : HSp D) (R : Subgroup (GA D W)) : (1 : GA D W) ∈ strip W R {1} := ⟨1, one_mem _, 1, rfl, 1, one_mem _, by simp⟩

end GlobalTheory.Asc

end
