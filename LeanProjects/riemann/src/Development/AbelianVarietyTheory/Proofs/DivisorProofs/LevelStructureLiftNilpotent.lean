import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTorsionPointNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDescendsStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.LevelLift

theorem exists_factor_of_nil {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ)
    (hπ : ∀ x ∈ RingHom.ker π, IsNilpotent x) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) :
    ∃ t₀ : Sp Ω ⟶ Sp ℂ, t₀ ≫ spMap (π : R →+* ℂ) = t := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* Ω, spMap φ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
  refine ⟨spMap (φ.comp (algebraMap ℂ R)), ?_⟩
  have e : φ = (φ.comp (algebraMap ℂ R)).comp (π : R →+* ℂ) := by
    ext r
    have hk : r - algebraMap ℂ R (π r) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    obtain ⟨n, hn⟩ := hπ _ hk
    have h0 : φ (r - algebraMap ℂ R (π r)) = 0 := by
      have : φ (r - algebraMap ℂ R (π r)) ^ n = 0 := by rw [← map_pow, hn, map_zero]
      exact pow_eq_zero_iff'.mp this |>.1
    rw [map_sub, sub_eq_zero] at h0
    simpa using h0
  conv_rhs => rw [e]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem level_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (X' : Obj F 𝔠 (Sp R)) (X₀ : Obj F 𝔠 (Sp ℂ)) (i : X₀.A.left ⟶ X'.A.left),
      X₀.IsPullBy X' (spMap (π : R →+* ℂ)) i → X₀.Level N → Nonempty (X'.Level N) := by
  intro F _ _ _ 𝔠 N hN R _ _ π hπ X' X₀ i h α₀
  have := X'.ab.smooth
  have hy : ∀ k, ∃ q : 𝟙_ (Over (Sp R)) ⟶ X'.A, q ^ N = 1 ∧ (α₀.pt k).left ≫ i = spMap (π : R →+* ℂ) ≫ q.left :=
    fun k => GlobalTheory.T.lift_torsion_point_nilpotent π hπ X'.A X₀.A i h.grp N hN (α₀.pt k) (α₀.tors k)
  choose q hq1 hq2 using hy
  exact GlobalTheory.T.level_structure_descends h (fun Ω _ _ t => exists_factor_of_nil π hπ Ω t) α₀ q hq1 hq2

end GlobalTheory.RealMult.LevelLift
