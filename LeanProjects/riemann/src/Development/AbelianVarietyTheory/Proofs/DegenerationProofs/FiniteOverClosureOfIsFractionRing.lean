import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatementsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRealDimOneIsFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSumDivThetaConstDotProductMem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ZH

theorem finite_over_closure_of_isFractionRing (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω]
    [IsFractionRing o Ω] (s : Set Ω) : Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ s)) Ω := by
  refine Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := o) x
  exact ⟨⟨_, div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))⟩, rfl⟩

theorem exists_zhOut_dim_one : GlobalTheory.Published.SemistableReductionSt → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.g = 1 ∧ S.Big ∧ S.HasTests ∧ ρ.HasU ∧ ρ.HasGeo ∧ S.admitted M U₀ ∧ S.IsEE M U₀ EE ∧ (∃ (n a : ℕ) (GG : Fin n → S.J → Ω), ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) ∧ Nonempty (ZHOut ρ M U₀ EE) ∧ ∃ (p : ℕ) (_ : Fact p.Prime) (y₀ : S.R →+* PadicAlgCl p), ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := by
  intro hN
  have hLL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨hU, hTo⟩ := GlobalTheory.T.uniformisationExistence_and_torsion_statements
  obtain ⟨o, Ω, _, _, _, hb, S, ρ, hg, hB, hfr⟩ := GlobalTheory.RealInhabitant.exists_real_dim_one_isFractionRing hLL.1 hLL.2.1
  have := hb.ft
  have := hb.char
  have := hb.ded
  obtain ⟨hT, hU'⟩ := GlobalTheory.T.thetaSystem_hasTests_of_real_point hN hU hLL.1 hLL.2.1 hTo o Ω S ρ
  have hasU : ρ.HasU := fun p _ y₀ hy Fs => hU' p y₀ Fs hy
  have hGeo : ρ.HasGeo := GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest hLL hTo o Ω S ρ hB hasU
  obtain ⟨M, U₀, hA, -, -⟩ := GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S Unit (fun _ => 1) ⟨(), one_ne_zero⟩
    (finite_over_closure_of_isFractionRing o Ω _)
  have hO : S.Over₀ M U₀ := hA.1
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  obtain ⟨EE, hE, hE₁⟩ := GlobalTheory.ZH.exists_isEE_of_adm o Ω S M U₀ hT hA
  have hsec := @GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω _ _ _ _ S M U₀ EE hA hll hte h0a h0b hwt h11 h12
    hne hE₁
  obtain ⟨n, a, GG, hGG⟩ := @GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω _ _ _ _ S M U₀ EE hA hll.2 h0b hne hE₁ hsec
  have hgen : ∃ (n a : ℕ) (GG : Fin n → S.J → Ω), ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω,
      w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z :=
    ⟨n, a, fun k j => GG k j, hGG⟩
  obtain ⟨ξ, -⟩ := hO.ne
  obtain ⟨x, -, hx, -⟩ := h0b.2.2.2 ξ ⊤ trivial
  obtain ⟨p, hp, y, hy⟩ := (hll.1 U₀ le_rfl hO.ne x hx).1
  obtain ⟨y₀, -, hy₀, -⟩ := hte x p y hy
  exact ⟨o, Ω, _, _, _, hb, S, ρ, M, U₀, EE, hg, hB, hT, hasU, hGeo, hA, hE, hgen,
    GlobalTheory.T.zarhinGeometric_of_semistableReduction hN o Ω S ρ hB M U₀ EE hO hE hgen, p, hp, y₀, hy₀⟩

end GlobalTheory.ZH
