import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem unitAt_natCast_of_overZp (𝔐 : HodgeCpt Y S y) (p : ℕ) (q : Cpt 𝔐.ξ) (hq : OverZp 𝔐 p q) (b : ℕ)
    (hb : ¬ p ∣ b) : unitAt 𝔐.ξ q (b : Ω) := by
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one =>
    rw [Nat.cast_one]
    exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
  | prime r hr =>
    by_contra h
    exact hb (by rw [hq r hr h])
  | mul a b iha ihb =>
    have ha := iha fun h => hb (h.mul_right b)
    have hb' := ihb fun h => hb (h.mul_left a)
    rw [Nat.cast_mul]
    exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
      rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩

theorem isLocIn_regAt_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (s : ∀ k, J k) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s q → OverZp 𝔐 p q → HTL.IsLocIn (chartRing o (mseg y) s) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho s q hs hq
  have hu := unitAt_natCast_of_overZp 𝔐 p q hq
  refine ⟨fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a, ha⟩ := a
    show a ∈ regAt 𝔐.ξ q
    refine Algebra.adjoin_induction (p := fun x _ => x ∈ regAt 𝔐.ξ q) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩
      exact hs.2 j
    · intro r
      obtain ⟨m, n, hn, e⟩ := (ho _).1 ⟨r, rfl⟩
      rw [e, div_eq_mul_inv]
      exact mul_mem (intCast_mem _ m) (hu n hn).2.2
    · intro x z _ _ hx hz
      exact add_mem hx hz
    · intro x z _ _ hx hz
      exact mul_mem hx hz
  · obtain ⟨t, ht, hut, htb⟩ := (GlobalTheory.T.regAt_iff_chart_localization 𝔐.X Ω 𝔐.ξ ℤ _ (mseg y) 𝔐.tie s q hs b).1 hb
    have hle : ∀ x ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y s),
        x ∈ chartRing o (mseg y) s := by
      intro x hx
      refine Algebra.adjoin_induction (p := fun x _ => x ∈ chartRing o (mseg y) s) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        exact div_mem_chartRing _ _ _
      · intro n
        simp
      · intro x z _ _ hx hz
        exact add_mem hx hz
      · intro x z _ _ hx hz
        exact mul_mem hx hz
    exact ⟨⟨t, hle t ht⟩, ⟨t * b, hle _ htb⟩, hut.1, hut.2.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
