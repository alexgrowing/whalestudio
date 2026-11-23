import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AHWeil

theorem eq_top_of_add_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ z : Fin g → ℂ, ∃ l : Λ, z - (l : Fin g → ℂ) ∈ W) : W = ⊤ := by
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hW : IsClosed (W : Set (Fin g → ℂ)) := W.closed_of_finiteDimensional
  obtain ⟨l, hl⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun l : Λ => (Homeomorph.subRight (l : Fin g → ℂ)) ⁻¹' (W : Set (Fin g → ℂ)))
    (fun l => hW.preimage (Homeomorph.continuous _))
    (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 (h z))
  rw [← Homeomorph.preimage_interior] at hl
  obtain ⟨z, hz⟩ := hl
  exact W.eq_top_of_nonempty_interior' ⟨_, hz⟩

theorem dim_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g g' : ℕ} (u : HolUnif A L g) (u' : HolUnif A L g')
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

theorem tangent_and_weil_of_isAH : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ g = P.g ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
  ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  intro hT P g u Hm χ hu
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  obtain rfl := dim_eq u u₀ F hF
  obtain ⟨⟨Ef, hEf, hB⟩, h1, h2⟩ := unimodular_and_tangent_of_isAH hT P rig hrig u Hm χ hu
  refine ⟨Ef, hEf, hB, rfl, h1, h2, fun k a b c hk hc => ?_⟩
  have ha := (UnifCompare.mem_iff u u₀ F hF a).2 a.2
  have hb := (UnifCompare.mem_iff u u₀ F hF b).2 b.2
  have e : Ef a b = E₀ ⟨F a, ha⟩ ⟨F b, hb⟩ := by
    have h := hE ⟨F a, ha⟩ ⟨F b, hb⟩
    rw [UnifCompare.hermForm_eq P.isLB u u₀ hu hu₀ F hF, ← hEf] at h
    exact_mod_cast h.symm
  have h := hW k ⟨F a, ha⟩ ⟨F b, hb⟩ c hk (e ▸ hc)
  rwa [← map_smul, ← map_smul, hF, hF] at h

end GlobalTheory.AHWeil
