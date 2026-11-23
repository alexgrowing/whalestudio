import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Poinc

theorem prime_eq_nonunits_at_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ P : Ideal (M.ringOn (U : Set M.Z)), P.IsPrime →
      ∃ z ∈ U, ∀ a : M.ringOn (U : Set M.Z), a ∈ P ↔ ((a : Ω) = 0 ∨ (a : Ω)⁻¹ ∉ M.O z) := by
  intro o Ω _ _ _ M U hU hne P hP
  let e := M.sectionsEquiv U hne
  let P' : Ideal Γ(M.Z, U) := P.comap (e : Γ(M.Z, U) →+* M.ringOn (U : Set M.Z))
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  let x : Spec Γ(M.Z, U) := (⟨P', hP'⟩ : PrimeSpectrum Γ(M.Z, U))
  have hz : hU.fromSpec x ∈ U := by
    have h := hU.range_fromSpec
    exact h.subset ⟨x, rfl⟩
  refine ⟨hU.fromSpec x, hz, fun a => ?_⟩
  obtain ⟨f, rfl⟩ := e.surjective a
  have key : hU.fromSpec x ∈ M.Z.basicOpen f ↔ f ∉ P' := by
    have h := hU.fromSpec_preimage_basicOpen f
    have h2 : x ∈ hU.fromSpec ⁻¹ᵁ M.Z.basicOpen f ↔ hU.fromSpec x ∈ M.Z.basicOpen f := Iff.rfl
    rw [← h2, h]
    exact PrimeSpectrum.mem_basicOpen f (⟨P', hP'⟩ : PrimeSpectrum Γ(M.Z, U))
  have hu := isUnit_valF_iff hz f
  rw [isUnit_O_iff] at hu
  have hmem : e f ∈ P ↔ f ∈ P' := Iff.rfl
  rw [hmem, coe_sectionsEquiv, ← not_iff_not, ← key, ← hu]
  simp only [not_or, not_not]

end GlobalTheory.Poinc
