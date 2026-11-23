import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalAddGeneralMemberLinearSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerateStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.GeneralLift

theorem unitAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0) (x : X) :
    GlobalTheory.Cartier.UnitAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.unitAt_fnOf (U := ⊤) trivial trivial
    (Units.map (algX p ⊤ : ℂ →+* Γ(X, ⊤)).toMonoidHom (Units.mk0 a ha))

theorem regAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (a : ℂ) (x : X) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial (algX p ⊤ a)

theorem principal_const {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0)
    (w : X.functionFieldˣ) (hw : (w : X.functionField) = GlobalTheory.Cartier.constFn p a) :
    GlobalTheory.Cartier.CartierDiv.principal w = 0 :=
  GlobalTheory.Cartier.CartierDiv.ext_of_isEqn fun x =>
    ⟨1, (GlobalTheory.Cartier.CartierDiv.isEqn_principal w x).iff_unitAt.2 (by
      rw [Units.val_one, one_div, hw]; exact (unitAt_constFn p ha x).inv),
      GlobalTheory.Cartier.CartierDiv.isEqn_zero x⟩

end GlobalTheory.GeneralLift

open GlobalTheory.GeneralLift in

theorem GlobalTheory.GeneralLift.exists_lift_klt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (z : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∀ f₀ ∈ (l • A).sections, ∃ u : X.functionField, u ∈ (l • A).sections ∧ (l • A).VanishesAt z u ∧ ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ y, ¬ z ⤳ y → ∀ a t : ℚ, 0 ≤ a → t < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + t • qWeil (GlobalTheory.Cartier.CartierDiv.principal g + l • A) 1) y := by
  intro hP X _ _ _ p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate X p hp A z hA
  refine ⟨l₁, fun l hl f₀ hf₀ => ?_⟩
  obtain ⟨r, κ, hκs, hκv, hκg⟩ := hl₁ l hl
  let s : Option (Fin r) → X.functionField := fun i => Option.elim i f₀ κ
  have hs : ∀ i, s i ∈ (l • A).sections := by
    rintro (_ | i)
    exacts [hf₀, hκs i]
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem hP X p n hp hn Δ D m G (l • A) (Option (Fin r)) s hm hG hD hs
  obtain ⟨v, hv⟩ : ∃ v : Option (Fin r) → ℂ, MvPolynomial.eval v (Q * MvPolynomial.X none) ≠ 0 := by
    by_contra h
    push_neg at h
    exact mul_ne_zero hQ (MvPolynomial.X_ne_zero _) (MvPolynomial.funext fun v => by rw [h v, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at hv
  have hv0 : v none ≠ 0 := right_ne_zero_of_mul hv
  have hvQ : MvPolynomial.eval v Q ≠ 0 := left_ne_zero_of_mul hv
  refine ⟨∑ i : Fin r, GlobalTheory.Cartier.constFn p (v (some i) / v none) * κ i, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    exact GlobalTheory.Cartier.CartierDiv.mem_sections.2 fun x =>
      (GlobalTheory.Cartier.CartierDiv.mem_sections.1 (hκs i) x).regAt_mul (regAt_constFn p _ x)
  · refine Finset.sum_induction _ (fun f => (l • A).VanishesAt z f)
      (fun _ _ h h' => h.add h') ((l • A).vanishesAt_zero z) fun i _ => ?_
    obtain ⟨g, hg, hz⟩ := hκv i
    exact ⟨g, hg, by convert hz.mul (regAt_constFn p (v (some i) / v none) z) using 1; ring⟩
  · intro g hg y hy a t ha ht hk
    have hc : GlobalTheory.Cartier.constFn p (v none) ≠ 0 := (map_ne_zero _).2 hv0
    have key := hQe v hvQ (Units.mk0 _ hc * g) (by
      rw [Units.val_mul, Units.val_mk0, hg, Fintype.sum_option, mul_add, Finset.mul_sum]
      refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hv0]
      rfl) y (have ⟨i, hi⟩ := hκg y hy; ⟨some i, hi⟩) a t ha ht hk
    rwa [GlobalTheory.Cartier.CartierDiv.principal_mul, principal_const p hv0 _ (Units.val_mk0 hc),
      zero_add] at key
