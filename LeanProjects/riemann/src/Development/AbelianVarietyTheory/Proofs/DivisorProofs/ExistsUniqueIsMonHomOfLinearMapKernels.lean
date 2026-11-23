import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HomAlgAny

open MeasureTheory

theorem surjective_of_forall_sub_mem {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : DiscreteTopology Λ) (h : ∀ x, ∃ z, x - T z ∈ Λ) : Function.Surjective T := by
  by_contra hT
  have hV : (LinearMap.range T).restrictScalars ℝ ≠ ⊤ := by
    intro h'
    apply hT
    intro x
    have hx : x ∈ (LinearMap.range T).restrictScalars ℝ := h' ▸ Submodule.mem_top
    exact LinearMap.mem_range.1 ((Submodule.restrictScalars_mem ℝ _ x).1 hx)
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcov : (Set.univ : Set (Fin g → ℂ)) ⊆ ⋃ l : Λ,
      (fun y => y + -(l : Fin g → ℂ)) ⁻¹' (((LinearMap.range T).restrictScalars ℝ : Submodule ℝ (Fin g → ℂ)) : Set (Fin g → ℂ)) := by
    intro x _
    obtain ⟨z, hz⟩ := h x
    refine Set.mem_iUnion.2 ⟨⟨x - T z, hz⟩, ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact ⟨z, by abel⟩
  have h0 : volume (Set.univ : Set (Fin g → ℂ)) = 0 :=
    measure_mono_null hcov (measure_iUnion_null fun l => by
      rw [measure_preimage_add_right]
      exact Measure.addHaar_submodule volume _ hV)
  exact (isOpen_univ.measure_ne_zero volume Set.univ_nonempty) h0

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a b : Fin g → ℂ)
    (h : u.ex a = u.ex b) : a - b ∈ u.Λ := by
  rw [← u.ker]
  have e := u.ex_add (a - b) b
  rw [sub_add_cancel, h] at e
  have e2 := congrArg (· * (u.ex b)⁻¹) e
  simpa using e2.symm

theorem exists_of_polAV (P P' : Out.PolAV (Sp ℂ)) (n n' : ℕ) (v : HolUnif P.A P.L n) (v' : HolUnif P'.A P'.L n')
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin n' → ℂ)) (hn : P.g = n) (hn' : P'.g = n') (hF : ∀ z ∈ v.Λ, F z ∈ v'.Λ) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, v'.ex (F z) = v.ex z ≫ f := by
  subst hn hn'
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := existsUnique_isMonHom_of_map_lattice hL hL2 AbLaw.CubeAssembly.cube_gen
    thetaUnifAV_all P P' P.L P'.L v v' F hF
  exact ⟨f, hf, hfe⟩

open GlobalTheory.HolUnifEnd GlobalTheory.HolUnifHom in

theorem exists_isMonHom_of_map_lattice (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g g' : ℕ)
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A') (hgA : SmoothOfRelativeDimension g A.hom)
    (hgA' : SmoothOfRelativeDimension g' A'.hom) (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hM : ∀ x ∈ u.Λ, M x ∈ u'.Λ) :
    ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g' hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := exists_of_polAV Q Q' (8 * g) (8 * g') v v' (J' ∘ₗ M ∘ₗ R) hQ hQ'
    (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

theorem existsUnique_isMonHom_of_map_ker : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  intro A A' _ _ _ _ g g' hA hA' hg hg' e e' M he he' hM
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨L', ⟨u'⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A' g' hA' hg'
  obtain ⟨t1, t2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨t1', t2'⟩ := GlobalTheory.TorusTransfer.tangent_bijective u' hg'
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u t1 t2 e he.1 he.2.2.1
  obtain ⟨T', hT', -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A' hA' L' g' g' u' t1' t2' e' he'.1 he'.2.2.1
  have hTs : Function.Surjective T := surjective_of_forall_sub_mem T u.Λ u.discrete fun x => by
    obtain ⟨z, hz⟩ := he.2.1 (u.ex x)
    exact ⟨z, sub_mem_of_ex_eq u _ _ (by rw [hT]; exact hz.symm)⟩
  have hTi : Function.Injective T := LinearMap.injective_iff_surjective.2 hTs
  let Te : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective T ⟨hTi, hTs⟩
  have hTe : ∀ z, Te.symm (T z) = z := fun z => Te.symm_apply_apply z
  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := T' ∘ₗ M ∘ₗ Te.symm.toLinearMap
  have hFT : ∀ z, F (T z) = T' (M z) := fun z => by simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, hTe]
  have hF : ∀ x ∈ u.Λ, F x ∈ u'.Λ := fun x hx => by
    obtain ⟨z, rfl⟩ := hTs x
    rw [hFT, ← u'.ker, hT']
    refine hM z ?_
    rw [← hT, u.ker]
    exact hx
  obtain ⟨α, hα, hαe⟩ := exists_isMonHom_of_map_lattice A A' g g' hA hA' hg hg' L L' u u' F hF
  have hex : ∀ z, e' (M z) = e z ≫ α := fun z => by
    rw [← hT', ← hFT, hαe, hT]
  refine ⟨α, ⟨hα, hex⟩, fun f hf => ?_⟩
  haveI := hA.smooth
  haveI := hA'.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
  obtain ⟨z, rfl⟩ := he.2.1 x
  rw [← hf.2, hex]

end GlobalTheory.HomAlgAny
