import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EEContainsStableWeightZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuadraticMapNonnegOfTendstoCofinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAtTestOfCen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem ThetaSys.proj_column_mem_of_stable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (A : Subalgebra o Ω) (E : Submodule A (S.J → Ω)) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (h1 : ∀ i, Pi.single i (1 : Ω) ∈ E)
    (h2 : ∀ h ∈ T, ∀ v ∈ E, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ E) (i : S.J) :
    (fun j => algebraMap o Ω (S.proj T c j i)) ∈ E := by
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  haveI : Fintype T := Fintype.ofFinite _
  have e : (fun j => algebraMap o Ω (S.proj T c j i)) =
      ∑ t : T, (algebraMap o A (Ring.inverse (Nat.card T : o) * S.ζN ^ (-(c t)).val)) •
        ((S.ρ t).map (algebraMap o Ω)).mulVec (Pi.single i 1) := by
    funext j
    simp only [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum, map_sum, Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.map_apply, algebraMap_smul, map_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Algebra.smul_def, map_mul, _root_.mul_assoc]
    rfl
  rw [e]
  exact E.sum_mem fun t _ => E.smul_mem _ (h2 t t.2 _ (h1 i))

theorem basis_origin_values_regular_and_unit :
    GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ (z : M.Z) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), x₀ ∈ S.supI M z → EE.E z = Submodule.span (M.O z) (Set.range b) → (∀ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ∈ M.O z) ∧ ∃ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ≠ 0 ∧ ((b i ⬝ᵥ S.ev 0) / S.th x₀)⁻¹ ∈ M.O z := by
  intro h₁ h₂ h₃ h₄ h₅ o Ω _ _ _ _ S ρ M U₀ EE hO hEE z x₀ b hx₀ hb
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft Ω
  haveI : CharZero Ω := ArithBase.char o
  have hL := classical_points_and_local_regularity o Ω M U₀ hO.normal
  have hT := exists_at_test_of_cen o Ω S M U₀ (GlobalTheory.T.thetaSystem_hasTests_of_real_point h₁ h₂ h₃ h₄ h₅ o Ω S ρ).1 hO
  have hS := ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ hO
  have hI := isoFree_TT_and_supI_specializes o Ω S M U₀ hO hL hT hS
  obtain ⟨hreg, i, hne, hinv⟩ :=
    coord_regular_and_unit o Ω S M U₀ EE hO hL hT hS hI hEE z x₀ hx₀ 0 (zero_mem _)
  obtain ⟨e1, e2, -⟩ := EE_contains_stable_weightZero o Ω S M U₀ EE hO hL hT hS hI hEE z
  have hA : ∀ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ∈ M.O z := fun i =>
    hreg _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨hA, ?_⟩
  have hv := S.proj_column_mem_of_stable (M.O z) (EE.E z) (S.TT M z) 0 e1
    (fun h hh => e2 h ((hI.1 z).2 ▸ (hI.1 z).1.1 hh)) i
  have hu : IsUnit (⟨_, hreg _ hv⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero hne hx₀.1, by simpa only [inv_div] using hinv⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ hv)
  have e : (⟨_, hreg _ hv⟩ : M.O z) = ∑ k, a k * ⟨_, hA k⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [← ha, sum_dotProduct, Finset.sum_div, MulMemClass.coe_mul, Subalgebra.smul_def, smul_dotProduct,
      smul_eq_mul, mul_div_assoc]
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum (e ▸ hu)
  exact ⟨k, (RatModel.isUnit_O_iff _).1 (isUnit_of_mul_isUnit_right hk)⟩

end GlobalTheory.ZH
