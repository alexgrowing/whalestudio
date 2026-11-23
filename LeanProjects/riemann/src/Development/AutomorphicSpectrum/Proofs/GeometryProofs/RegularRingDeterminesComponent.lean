import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_regAt_eq_of_coordTie :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω),
      CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  intro X Ω _ ξ o _ _ κ x h p q e
  obtain ⟨c, hc⟩ := h.cover p
  have hq : InChart ξ x c q := ⟨hc.1, fun c' => e ▸ hc.2 c'⟩
  haveI hloc : IsLocalRing (regAt ξ p) :=
    (regAt_isLocalRing_isFractionRing_stalk X Ω ξ h.gen p).1
  have hmem : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), (s : Ω) ∈ regAt ξ p :=
    fun s => (h.ring c hc.1 s).1 s.2 p hc
  let f : Algebra.adjoin o (Set.range fun j => x j / x c) →+* regAt ξ p :=
    ((Algebra.adjoin o (Set.range fun j => x j / x c)).val :
      Algebra.adjoin o (Set.range fun j => x j / x c) →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hp' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ q (s : Ω) := by
    intro s
    rw [hp' s]
    simp only [unitAt, e]
  exact (GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ x h c hc.1 _ hI).unique ⟨hc, hp'⟩ ⟨hq, hq'⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
