import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHomStatement

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ch

theorem unitAt_div {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, Λ.IsGenAt p s → Λ.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := by
      rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    have ha' : (a : Ω) * t = s := ha
    rw [← ha', mul_div_cancel_right₀ _ ht.1]
    exact a.2
  exact ⟨div_ne_zero hs.1 ht.1, key hs ht, by rw [inv_div]; exact key ht hs⟩

theorem isdeg_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  intro X Ω _ ξ K _ C z Y Λ n n' hξ ⟨h₀, h, s₀, s, r, g₀, g, hr, hf, e⟩
    ⟨h₀', h', s₀', s', r', g₀', g', hr', hf', e'⟩
  obtain ⟨φ, hφ, hu⟩ := ValHom.exists_valAt_hom X Ω ξ K z h₀ hξ
  have u₀ := unitAt_div g₀' g₀
  let c : K := φ ⟨s₀' / s₀, u₀.2.1⟩
  have hc : c ≠ 0 := ((hu ⟨_, u₀.2.1⟩).2 u₀).ne_zero
  have key : ∀ i, C.v i (r i) = C.v i (r' i) * C.v i c := by
    intro i
    obtain ⟨ψ, hψ, hv⟩ := ValHom.exists_valAt_hom X Ω ξ _ (Y.x i) (h i) hξ
    have u := unitAt_div (g i) (g' i)
    have hun : IsUnit (ψ ⟨_, u.2.1⟩) := (hv ⟨_, u.2.1⟩).2 u
    have hval := GlobalTheory.T.valAt_comp_local_hom X Ω ξ _ K (C.v i).valuationSubring.subtype (Y.x i) _ _
      ((hψ _ _).2 ⟨u.2.1, rfl⟩) (by rw [Y.gen i]; exact h₀)
    rw [Y.gen i] at hval
    obtain ⟨m1, e1⟩ := (hφ _ _).1 hval
    obtain ⟨m2, e2⟩ := (hφ _ _).1 (hr i).2
    obtain ⟨m3, e3⟩ := (hφ _ _).1 (hr' i).2
    have hone : C.v i ((C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩)) = 1 := by
      obtain ⟨w, hw⟩ := hun.exists_right_inv
      have h1 : C.v i ((ψ ⟨_, u.2.1⟩ : (C.v i).valuationSubring) : K) * C.v i (w : K) = 1 := by
        rw [← map_mul, ← MulMemClass.coe_mul, hw]; simp
      exact le_antisymm (ψ ⟨_, u.2.1⟩).2 (h1 ▸ mul_le_of_le_one_right' w.2)
    have : r i = (C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩) * (r' i * c) := by
      rw [← e1, ← e2, ← e3, ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      have := (g' i).1
      have := g₀'.1
      have := g₀.1
      simp only [MulMemClass.coe_mul]
      field_simp
    rw [this, map_mul, hone, one_mul, map_mul]
  have h2 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (r i)) =
      (C.w i : ℤ) * WithZero.log (C.v i (r' i)) + (C.w i : ℤ) * WithZero.log (C.v i c) := by
    intro i
    rw [key, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (hr' i).1)
      ((Valuation.ne_zero_iff _).2 hc), mul_add]
  rw [e, e']
  simp only [h2]
  rw [finsum_add_distrib (hf'.subset fun i hi h1 => hi (by simp [h1]))
    ((C.fin c hc).subset fun i hi h1 => hi (by simp [h1])), C.prod c hc, add_zero]

end PositivityTheory.HtPt.Ch
