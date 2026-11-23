import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac

theorem exists_frac_field {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {W : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ W} {κ : Type} {x : κ → Ω} (h : CoordTie F ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ r ∈ Algebra.adjoin F (Set.range fun j => x j / x c),
      ∃ s ∈ Algebra.adjoin F (Set.range fun j => x j / x c), s ≠ 0 ∧ a * s = r := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover p₀
  obtain ⟨U, hU, hq⟩ := h.affine c hc.1
  have h0 : genPt ξ ∈ U := (hq _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(W, U), (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.germ U (genPt ξ) h0 r) ∈
      Algebra.adjoin F (Set.range fun j => x j / x c) := fun r => by
    rw [h.ring c hc.1]
    intro q hqc
    have hqU : q.1 ∈ U := (hq _).2 ⟨q.2, hqc⟩
    refine ⟨W.presheaf.germ U q.1 hqU r, ?_⟩
    show (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.stalkSpecializes q.2 (W.presheaf.germ U q.1 hqU r)) = _
    congr 1
    exact W.presheaf.germ_stalkSpecializes_apply hqU q.2 r
  refine ⟨c, hc.1, fun a => ?_⟩
  obtain ⟨s, rfl⟩ := h.gen.bij.2 a
  letI := W.presheaf.algebra_section_stalk (⟨genPt ξ, h0⟩ : U)
  have hl := hU.isLocalization_stalk ⟨genPt ξ, h0⟩
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, h0⟩).asIdeal.primeCompl
    (S := W.presheaf.stalk (genPt ξ)) s
  refine ⟨_, key r, _, key t, ?_, ?_⟩
  · have := IsLocalization.map_units (W.presheaf.stalk (genPt ξ)) t
    exact (this.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · exact (map_mul (Scheme.stalkClosedPointTo ξ).hom _ _).symm.trans (congrArg _ e)

theorem exists_clear {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {S : Set Ω} {b : Ω}
    (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ ∃ g ∈ Algebra.adjoin o S, algebraMap o Ω d * b = g := by
  induction hb using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_ne_zero, y, Algebra.subset_adjoin hy, by simp⟩
  | algebraMap f =>
    obtain ⟨⟨n, d⟩, e⟩ := IsLocalization.surj (nonZeroDivisors o) f
    refine ⟨d, nonZeroDivisors.ne_zero d.2, algebraMap o Ω n, Subalgebra.algebraMap_mem _ n, ?_⟩
    rw [IsScalarTower.algebraMap_apply o F Ω n, IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, ← e, mul_comm]
  | add u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, algebraMap o Ω d₂ * g₁ + algebraMap o Ω d₁ * g₂,
      add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) m₁) (mul_mem (Subalgebra.algebraMap_mem _ _) m₂), ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, g₁ * g₂, mul_mem m₁ m₂, ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring

theorem algebraMap_ne_zero {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω d]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem chartRing_frac : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type)
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω),
    CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀),
      ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  intro o F _ _ _ _ _ Ω _ _ _ _ W ξ' κ t hT
  obtain ⟨c, hc, hf⟩ := exists_frac_field hT
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨r, hr, s, hs, hs0, e⟩ := hf a
  obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := exists_clear (o := o) hr
  obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := exists_clear (o := o) hs
  have n₁ := algebraMap_ne_zero (F := F) (Ω := Ω) h₁
  have n₂ := algebraMap_ne_zero (F := F) (Ω := Ω) h₂
  have hg₂ : g₂ ≠ 0 := e₂ ▸ mul_ne_zero n₂ hs0
  refine ⟨algebraMap o Ω d₂ * g₁, mul_mem (Subalgebra.algebraMap_mem _ _) m₁,
    algebraMap o Ω d₁ * g₂, mul_mem (Subalgebra.algebraMap_mem _ _) m₂, mul_ne_zero n₁ hg₂, ?_⟩
  rw [eq_div_iff (mul_ne_zero n₁ hg₂), ← e₁, ← e₂, ← e]
  ring

end GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac
