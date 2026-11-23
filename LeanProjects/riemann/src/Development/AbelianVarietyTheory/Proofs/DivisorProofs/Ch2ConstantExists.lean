import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaChernClassBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaChernClassBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeRegularCoverPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverDegreeOmegaStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.ThetaRegularityConstant

def ThetaReg (g : ℕ) (r : ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p →
    ∀ P : PPAS S, P.g = g → P.HasTheta → P.IsCh2Omega p (r / 2 * (P.degOmega p : ℝ))

def Active (g : ℕ) : Prop :=
  ∃ (k : Type) (_ : CommRing k) (S : Scheme.{0}) (p : S ⟶ Sp k) (_ : IsIntegral S) (P : PPAS S),
    IsRegSurf p ∧ P.g = g ∧ P.HasTheta ∧ P.degOmega p ≠ 0

theorem thetaReg_of_not_active {g : ℕ} {r : ℝ} (h : ThetaReg g r) (ha : ¬ Active g) (r' : ℝ) :
    ThetaReg g r' := by
  intro k _ S p _ hS P hg hT
  have h0 : P.degOmega p = 0 := by
    by_contra hne
    exact ha ⟨k, inferInstance, S, p, inferInstance, P, hS, hg, hT, hne⟩
  have := h k S p hS P hg hT
  simpa [h0] using this

theorem uniform (hT : ∀ g : ℕ, ∃ r : ℝ, ThetaReg g r)
    (hP : ∀ g₁ g : ℕ, g₁ ≤ g → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S],
      IsRegSurf p → ∀ P : PPAS S, P.g = g₁ → P.HasTheta → ∃ (k' : Type) (_ : CommRing k') (S' : Scheme.{0})
        (p' : S' ⟶ Sp k') (_ : IsIntegral S') (P' : PPAS S') (n : ℕ), IsRegSurf p' ∧ P'.g = g ∧ P'.HasTheta ∧
          0 < n ∧ P'.degOmega p' = n * P.degOmega p ∧ ∀ a : ℝ, P.IsCh2Omega p a → P'.IsCh2Omega p' (n * a)) :
    ∃ r : ℝ, ∀ g, ThetaReg g r := by
  classical
  choose rr hrr using hT
  by_cases hA : ∃ g, Active g
  · obtain ⟨k, _, S, p, _, P, hS, hg, hth, hne⟩ := Nat.find_spec hA
    refine ⟨rr (Nat.find hA), fun g => ?_⟩
    by_cases hg' : Active g
    · obtain ⟨k', _, S', p', _, P', n, hS', hg'', hth', hn, hdeg, hch⟩ :=
        hP _ g (Nat.find_min' hA hg') k S p hS P hg hth
      have e := (hch _ (hrr _ k S p hS P hg hth)).unique (hrr g k' S' p' hS' P' hg'' hth')
      rw [hdeg] at e
      push_cast at e
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hd : (P.degOmega p : ℝ) ≠ 0 := Int.cast_ne_zero.2 hne
      have e' : ((n : ℝ) * (P.degOmega p : ℝ)) * (rr (Nat.find hA) - rr g) = 0 := by
        linear_combination 2 * e
      have hr : rr (Nat.find hA) = rr g :=
        sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_left (mul_ne_zero hn' hd))
      rw [hr]
      exact hrr g
    · exact thetaReg_of_not_active (hrr g) hg' _
  · push_neg at hA
    exact ⟨0, fun g => thetaReg_of_not_active (hrr g) (hA g) 0⟩

theorem exists_ch2Const : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch →
    ∃ r, GlobalTheory.CovTest.Ch2Const r := by
  intro h2 hRA hARR
  obtain ⟨r, hr⟩ := uniform ((GlobalTheory.T.theta_chern_class_bound · hRA) h2 hARR) (GlobalTheory.T.theta_chern_class_base_change h2 hRA)
  refine ⟨r, fun k _ X p _ hX P => ?_⟩
  obtain ⟨C, P', φ, hpull, hg, hth⟩ := GlobalTheory.T.abelian_scheme_regular_cover_pullback h2 hRA k X p hX P
  have e := hr P'.g k C.Y (C.ρ ≫ p) C.reg P' rfl hth
  obtain ⟨hdeg, hdesc⟩ := GlobalTheory.T.regular_cover_degree_omega h2 hRA k X p hX P C P' φ hpull
  have h := hdesc _ e
  have hd : (C.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 C.deg_pos.ne'
  convert h using 1
  rw [hdeg]
  push_cast
  field_simp

end GlobalTheory.ThetaRegularityConstant

end
