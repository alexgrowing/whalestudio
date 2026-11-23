import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

namespace GlobalTheory.RootEqn

theorem divOf_single {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
    (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : ℕ) (hk : k = i) (n : ℤ) :
    divOf Y (expo Dw (Finsupp.single (a, R, .inl (τ, k)) n)) = n • Y.gr τ i := by
  subst hk
  have h : ∀ x, expo Dw (Finsupp.single (a, R, .inl (τ, (i : ℕ))) n) x = if x = ⟨τ, i⟩ then n else 0 := by
    intro x
    rw [expo, Finsupp.sum_single_index (by simp)]
    simp only [letterOf, dif_pos i.2, Option.some.injEq, eq_comm]
  rw [divOf]
  simp_rw [h, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp

theorem unitAt_genAt_root : ∀ (D : D7) (O : Setup D) (B R : ℝ) (c : O.s.Comp) (G : Scheme.{0}) [IsIntegral G] (πG : G ⟶ (O.var c).X)
    (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a))
    (x : G) (ρ : G.functionFieldˣ),
    (∀ t : (O.var c).Fnˣ, ((O.Φ.C c).gr (embB D a) (Fin.cast hr (cond a.2 i i.rev))).IsEqn (πG x) t →
      UnitAt x (φ (t : (O.var c).Fn) ^ (cond a.2 (-1 : ℤ) 1) * (ρ : G.functionField))) →
    UnitAt x (φ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D a.1)
      (cond a.2 0 O.j + i))).D (πG x)) ^ 1 * (ρ : G.functionField)) := by
  intro D O B R c G _ πG φ _ a i hr x ρ h
  obtain ⟨τ, b⟩ := a
  have hp := O.S.p_eq
  have hN := O.S.rank_eq
  have hi := i.2
  cases b
  · have hi' : (i : ℕ) < O.N - O.j := hi
    have hD : (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D τ)
        (O.j + i))).D = -(O.Φ.C c).gr (embB D (τ, false)) (Fin.cast hr i.rev) := by
      change divOf _ (expo _ _) = _
      rw [rootSym, if_neg (by omega)]
      refine (divOf_single (O.Φ.C c) _ _ (conjEmb (DV.tauEmb D τ)) (Fin.cast hr i.rev) _ ?_ _).trans (neg_one_smul _ _)
      change _ = O.N - O.j - (i + 1)
      omega
    have he := (Base.isEqn_eqn (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R)
      (DV.tauEmb D τ) (O.j + i))).D (πG x)).neg
    have := h _ (by
      have e := congrArg Neg.neg hD
      rw [neg_neg] at e
      exact e ▸ he)
    simpa only [cond_false, zpow_one, pow_one] using this
  · have hi' : (i : ℕ) < O.j := hi
    have hD : (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D τ)
        (0 + i))).D = (O.Φ.C c).gr (embB D (τ, true)) (Fin.cast hr i) := by
      change divOf _ (expo _ _) = _
      rw [rootSym, if_pos (by omega)]
      exact (divOf_single (O.Φ.C c) _ _ (DV.tauEmb D τ) (Fin.cast hr i) _ (Nat.zero_add _) _).trans (one_smul _ _)
    have he := Base.isEqn_eqn (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R)
      (DV.tauEmb D τ) (0 + i))).D (πG x)
    have := h (eqn (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R)
      (DV.tauEmb D τ) (0 + i))).D (πG x)) (by
      change CartierDiv.IsEqn ((O.Φ.C c).gr (embB D (τ, true)) (Fin.cast hr i)) _ _
      rw [← hD]
      exact he)
    simpa only [cond_true, zpow_neg_one, pow_one, genAt, Units.val_inv_eq_inv_val, map_inv₀] using this

end GlobalTheory.RootEqn
