import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WAddLeMax
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

theorem w_pow_succ_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (α β : AlgebraicClosure F) {E : ℝ} (hE : 0 ≤ E) (hα : e.w α * E ≤ 1) (hβ : e.w β * E ≤ 1) (k : ℕ) :
    e.w (α ^ (k + 1) - β ^ (k + 1)) * E ^ (k + 1) ≤ e.w (α - β) * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : α ^ (k + 1 + 1) - β ^ (k + 1 + 1) = α ^ (k + 1) * (α - β) + (α ^ (k + 1) - β ^ (k + 1)) * β := by ring
    rw [h]
    have hmax := TrueGeo.Ext.w_add_le_max F v e (α ^ (k + 1) * (α - β)) ((α ^ (k + 1) - β ^ (k + 1)) * β)
    have hEk : 0 ≤ E ^ (k + 1 + 1) := pow_nonneg hE _
    refine (mul_le_mul_of_nonneg_right hmax hEk).trans ?_
    rw [max_mul_of_nonneg _ _ hEk]
    refine max_le ?_ ?_
    · rw [map_mul, map_pow]
      have e1 : e.w α ^ (k + 1) * e.w (α - β) * E ^ (k + 1 + 1) = (e.w α * E) ^ (k + 1) * (e.w (α - β) * E) := by ring
      rw [e1]
      exact mul_le_of_le_one_left (mul_nonneg (e.w.nonneg _) hE) (pow_le_one₀ (mul_nonneg (e.w.nonneg _) hE) hα)
    · rw [map_mul]
      have e1 : e.w (α ^ (k + 1) - β ^ (k + 1)) * e.w β * E ^ (k + 1 + 1) =
          (e.w (α ^ (k + 1) - β ^ (k + 1)) * E ^ (k + 1)) * (e.w β * E) := by ring
      rw [e1]
      exact (mul_le_of_le_one_right (mul_nonneg (e.w.nonneg _) (pow_nonneg hE _)) hβ).trans ih

theorem w_pow_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (α β : AlgebraicClosure F) {E : ℝ} (hE : 0 ≤ E) (hα : e.w α * E ≤ 1) (hβ : e.w β * E ≤ 1) {m : ℕ} (hm : 0 < m) :
    e.w (α ^ m - β ^ m) * E ^ m ≤ e.w (α - β) * E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact w_pow_succ_sub_le e α β hE hα hβ k

theorem unitAt_zpow' {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) (a : ℤ) :
    UnitAt x (f ^ a) := by
  obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := h
  refine ⟨((u ^ a : _ˣ) : X.presheaf.stalk x), Units.isUnit _, ?_⟩
  exact (congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u a)).trans
    (Units.val_zpow_eq_zpow_val _ _)

theorem regAt_sub' {X : Scheme.{0}} [IsIntegral X] {x : X} {f g : X.functionField} (hf : RegAt x f) (hg : RegAt x g) :
    RegAt x (f - g) :=
  have ⟨a, ha⟩ := hf; have ⟨b, hb⟩ := hg; ⟨a - b, by rw [map_sub, ha, hb]⟩

theorem valAt_sub' {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] {y : Sp K ⟶ X} {f g : X.functionField}
    (hf : RegAt (below y) f) (hg : RegAt (below y) g) : TrueGeo.valAt y (f - g) = TrueGeo.valAt y f - TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_sub, TrueGeo.Res.valAt_algebraMap, TrueGeo.Res.valAt_algebraMap, TrueGeo.Res.valAt_algebraMap, map_sub]

theorem genOver_pow_div : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (f : Y.X → Y.Fn)
    (ψ φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l m : ℕ) (a : ℤ), l ≠ 0 → 0 < m →
    (∀ v e y, (l : 𝓞 F) ∈ v.asIdeal → φ v e y = m * ψ v e y + a * Real.log (e.w (l : AlgebraicClosure F))) →
    GenOver V f ψ l → GenOver V (fun y => f y ^ m) φ l := by
  intro F _ _ Y V f ψ φ l m a hl hm hφ ⟨n, U, s, hU, hreg, hnorm⟩
  have hlF : (l : F) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hl1 : ∀ z : V.G, UnitAt z (l : V.G.functionField) := fun z => by
    have := TrueGeo.IndScale.unitAt_constFn (V.π ≫ Y.str) z hlF
    rwa [map_natCast] at this
  have hlu : ∀ z : V.G, UnitAt z ((l : V.G.functionField) ^ (-a)) := fun z => unitAt_zpow' (hl1 z) (-a)
  have key : ∀ (p : Y.X) (x : V.X) (J : Fin n), (s x J ^ m * (l : V.G.functionField) ^ (-a)) / V.φ (f p ^ m) =
      (s x J / V.φ (f p)) ^ m * (l : V.G.functionField) ^ (-a) := by
    intro p x J
    rw [map_pow, div_pow, div_mul_eq_mul_div]
  have keyd : ∀ (p : Y.X) (x x' : V.X) (J : Fin n),
      (s x J ^ m * (l : V.G.functionField) ^ (-a) - s x' J ^ m * (l : V.G.functionField) ^ (-a)) / V.φ (f p ^ m) =
      ((s x J / V.φ (f p)) ^ m - (s x' J / V.φ (f p)) ^ m) * (l : V.G.functionField) ^ (-a) := by
    intro p x x' J
    rw [map_pow, div_pow, div_pow, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, sub_div]
  refine ⟨n, U, fun x J => s x J ^ m * (l : V.G.functionField) ^ (-a), hU, fun x J z hz => ?_, ?_⟩
  · beta_reduce
    rw [key]
    exact (TrueGeo.Res.regAt_pow (hreg x J z hz) m).mul (hlu z).regAt
  · intro v e y z yt hlv hzy hyt x hx
    beta_reduce
    have hπ : V.π (below z) = below y.1 := by rw [← hzy]; rfl
    have hmem : ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → V.j (below z) ∈ U x' := fun x' h => by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x' := by rw [← hyt]; exact h (Set.mem_univ _)
      exact h1
    have hα : ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → ∀ J, RegAt (below z) (s x' J / V.φ (f (below y.1))) := fun x' h J => by
      have := hreg x' J (below z) (hmem x' h)
      rwa [hπ] at this
    have hl0 : (l : AlgebraicClosure F) ≠ 0 := by
      have := (algebraMap F (AlgebraicClosure F)).injective.ne hlF
      rwa [map_natCast, map_zero] at this
    have hwl : 0 < e.w (l : AlgebraicClosure F) := e.w.pos hl0
    have hvl : TrueGeo.valAt z ((l : V.G.functionField) ^ (-a)) = (l : AlgebraicClosure F) ^ (-a) := by
      rw [(TrueGeo.Base.valAt_zpow z (hl1 (below z))).2 (-a)]
      congr 1
      rw [← map_natCast (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField), TrueGeo.Res.valAt_algebraMap,
        map_natCast]
    have hE : Real.exp (φ v e y) = Real.exp (ψ v e y) ^ m * e.w (l : AlgebraicClosure F) ^ a := by
      rw [hφ v e y hlv, Real.exp_add, Real.exp_nat_mul, mul_comm (a : ℝ), ← Real.rpow_def_of_pos hwl, Real.rpow_intCast]
    have hscale : ∀ β, RegAt (below z) β → e.w (TrueGeo.valAt z (β * (l : V.G.functionField) ^ (-a))) *
        Real.exp (φ v e y) = e.w (TrueGeo.valAt z β) * Real.exp (ψ v e y) ^ m := by
      intro β hβ
      rw [TrueGeo.Res.valAt_mul hβ (hlu _).regAt, hvl, map_mul, map_zpow₀, hE]
      have h1 : e.w (l : AlgebraicClosure F) ^ (-a) * e.w (l : AlgebraicClosure F) ^ a = 1 := by
        rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hwl.ne')]
      linear_combination (e.w (TrueGeo.valAt z β) * Real.exp (ψ v e y) ^ m) * h1
    obtain ⟨h1, ⟨J₀, h2⟩, h3⟩ := hnorm v e y z yt hlv hzy hyt x hx
    have hE0 : 0 ≤ Real.exp (ψ v e y) := (Real.exp_pos _).le
    refine ⟨fun J => ?_, ⟨J₀, ?_⟩, fun x' hx' J => ?_⟩
    · rw [key, hscale _ (TrueGeo.Res.regAt_pow (hα x hx J) m), TrueGeo.Res.valAt_pow (hα x hx J), map_pow, ← mul_pow]
      exact pow_le_one₀ (mul_nonneg (e.w.nonneg _) hE0) (h1 J)
    · rw [key, hscale _ (TrueGeo.Res.regAt_pow (hα x hx J₀) m), TrueGeo.Res.valAt_pow (hα x hx J₀), map_pow,
        ← mul_pow, h2, one_pow]
    · have h1' := (hnorm v e y z yt hlv hzy hyt x' hx').1 J
      have h3' := h3 x' hx' J
      rw [sub_div, valAt_sub' (hα x hx J) (hα x' hx' J)] at h3'
      rw [keyd, hscale _ (regAt_sub' (TrueGeo.Res.regAt_pow (hα x hx J) m) (TrueGeo.Res.regAt_pow (hα x' hx' J) m)),
        valAt_sub' (TrueGeo.Res.regAt_pow (hα x hx J) m) (TrueGeo.Res.regAt_pow (hα x' hx' J) m),
        TrueGeo.Res.valAt_pow (hα x hx J), TrueGeo.Res.valAt_pow (hα x' hx' J)]
      exact (w_pow_sub_le e _ _ hE0 (h1 J) h1' hm).trans_lt h3'

end GlobalTheory.HtGen
