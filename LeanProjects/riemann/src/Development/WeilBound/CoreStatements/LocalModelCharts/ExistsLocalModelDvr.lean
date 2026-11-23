import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingValuationSubringStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PartIHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliSchemesExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Ar2.LocalDVRModel

theorem frac_of_val {K : Type} [Field K] (V : ValuationSubring K) (x : K) :
    ∃ a b : V, V.subtype b ≠ 0 ∧ x * V.subtype b = V.subtype a := by
  rcases V.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, by simp, by simp [hx]⟩
    · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simp [hx]⟩

end PositivityTheory.Ar2.LocalDVRModel

theorem PositivityTheory.Ar2.exists_local_model_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), 1 ≤ D.p + D.q → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (β : O →+* c.F) (Y : Model Xo c β), FracBase β ∧ (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) ∧ Y.SplitFibres ∧ Y.N3 := by
  intro E _ _ _ H D l Xo c p κ hpq hgood
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨W, hWp, hW⟩ := GlobalTheory.T.padic_embedding_valuation_subring c.F p κ
  obtain ⟨V, hDVR, hVn, -, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p κ
  have hVeq : c.V W = V := by
    ext x
    rw [← hVn x, hW x]
    rfl
  haveI : IsDiscreteValuationRing (c.V W) := hVeq ▸ hDVR
  let Xf : (l' : Level H) → Moduli D l' := fun l' =>
    if h : l = l' then h ▸ Xo else Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H D l' hpq)
  have hX : Xf l = Xo := dif_pos rfl
  obtain ⟨Y, hY, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.partI_holds.2 E H D hpq Xf
  have key : ∀ X' : Moduli D l, X' = Xo →
      (∃ Y' : Model X' c (c.V W).subtype, Y'.SplitFibres ∧ Y'.N3) →
      ∃ Y' : Model Xo c (c.V W).subtype, Y'.SplitFibres ∧ Y'.N3 := by
    rintro X' rfl h
    exact h
  let i : Idx H p := ⟨l, c, hgood⟩
  have hi := (hY p W p.2 hWp).2 i
  obtain ⟨Y', hS, hN⟩ := key (Xf l) hX ⟨Y p W p.2 hWp i, hi.1, hi.2.1⟩
  refine ⟨c.V W, inferInstance, inferInstance, inferInstance, (c.V W).subtype, Y', ?_, ?_, hS, hN⟩
  · exact ⟨Subtype.val_injective, inferInstance, fun x => LocalDVRModel.frac_of_val (c.V W) x⟩
  · intro x
    constructor
    · intro h
      exact ⟨⟨x, (hW x).mp h⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact (hW _).mpr y.2
