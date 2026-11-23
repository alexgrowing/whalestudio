import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CrysFree

theorem isLocalRing_of_sq {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k) (hπ : Function.Surjective π)
    (hI : RingHom.ker π ^ 2 = 0) : IsLocalRing Λ := by
  have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
  haveI := hmax.isPrime
  have hle : RingHom.ker π ≤ nilradical Λ := fun x hx ↦ ⟨2, by
    have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
    rw [hI] at this; simpa [pow_two] using this⟩
  have heq : nilradical Λ = RingHom.ker π := le_antisymm (nilradical_le_prime _) hle
  haveI : (nilradical Λ).IsMaximal := heq ▸ hmax
  exact IsLocalRing.of_isMaximal_nilradical Λ

theorem isDPMorphism_red {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k)
    (hI : RingHom.ker π ^ 2 = 0) : DividedPowers.IsDPMorphism (divided₂ hI) (dp0 k) π := by
  refine (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨?_, fun n hn a ha ↦ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]; intro x hx
    simpa using (RingHom.mem_ker.1 hx)
  · rw [RingHom.mem_ker.1 ha]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, (divided₂ hI).dpow_one ha, RingHom.mem_ker.1 ha, (dp0 k).dpow_one (Ideal.zero_mem _)]
    · rw [squareZeroDividedPowers_dpow hI (by omega), map_zero, DividedPowers.dpow_eval_zero _ hn]

theorem mem_smul_top_of_forall {Λ : Type} [CommRing Λ] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module.Finite Λ P] [Module.Free Λ P] (J : Ideal Λ) (h : Module.Dual Λ P) (hh : ∀ c, h c ∈ J) :
    h ∈ J • (⊤ : Submodule Λ (Module.Dual Λ P)) := by
  classical
  let b := Module.Free.chooseBasis Λ P
  rw [← b.sum_dual_apply_smul_coord h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hh _) Submodule.mem_top

end GlobalTheory.CrysFree

namespace GlobalTheory.CrysFree

theorem crys_free_and_red : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  intro F _ _ Λ _ k _ π hπ hI A₀ _ _ hA₀ a
  haveI := isLocalRing_of_sq π hπ hI
  letI : Algebra Λ k := π.toAlgebra
  obtain ⟨A, _, i, h, hA⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine Λ (RingHom.ker π) hI k π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Λ A hA
  obtain ⟨HFree, -, HBC, HRigid, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hrig := HRigid Λ A g hA hg (RingHom.ker π) (divided₂ hI) (isDPNilpotent_squareZero hI) k π hπ rfl A₀ i h
  let e : primDR A ≃ₗ[Λ] prim (divided₂ hI) (spMap π) A₀ :=
    LinearEquiv.ofBijective (liftMor (divided₂ hI) h).pull hrig
  obtain ⟨hfin, hproj, -⟩ := HFree.prim hA hg
  haveI : Module.Finite Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Finite.equiv e
  haveI : Module.Projective Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Projective.of_equiv e
  haveI := Module.finitePresentation_of_projective Λ (prim (divided₂ hI) (spMap π) A₀)
  haveI : Module.Free Λ (prim (divided₂ hI) (spMap π) A₀) := Module.free_of_flat_of_isLocalRing
  have m : GrpMor (divided₂ hI) (spMap π) A₀ (dp0 k) (𝟙 _) A₀ (algebraMap Λ k) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
    GrpMor.of_hom (isDPMorphism_red π hI) (Category.id_comp _).symm (𝟙 A₀)
  have hm : m.IsBC := by
    have hb := (HBC Λ A g hA hg k A₀ i h).1
    let E := LinearEquiv.baseChange Λ k _ _ e
    have key : liftSemi m.pull ∘ₗ E.toLinearMap =
        liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.baseChange_tmul,
          liftSemi_tmul]
        congr 1
        exact GrpMor.pull_pull (liftMor (divided₂ hI) h) m (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h)
          (fun _ ↦ rfl) (by simp) c
      | add x y hx hy => rw [map_add, hx, hy, map_add]
    have : liftSemi m.pull = liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull ∘ₗ
        E.symm.toLinearMap := by
      rw [← key, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]; rfl
    unfold GrpMor.IsBC
    rw [this]
    exact hb.comp E.symm.bijective
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hact : ∀ (o : 𝓞 F) (x : Crys (divided₂ hI) (spMap π) A₀),
      hm.bcMap (act (divided₂ hI) (spMap π) a o x) = act (dp0 k) (𝟙 _) a o (hm.bcMap x) := by
    intro o x
    haveI := a.hom o
    rw [act_apply, act_apply]
    exact hm.corr_iff.1 (GrpMor.Corr.push (m := m) m (a.act o) (a.act o) (by simp) (hm.corr_iff.2 rfl))
  letI := tensorModule (divided₂ hI) (spMap π) a
  letI := tensorModule (dp0 k) (𝟙 _) a
  refine ⟨{ toFun := hm.bcMap, map_add' := hm.bcMap.map_add, map_smul' := ?_ }, ?_, ?_⟩
  · intro r x
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul l o =>
      have e1 : (l ⊗ₜ[ℤ] o) • x = l • act (divided₂ hI) (spMap π) a o x := rfl
      have e2 : ∀ y : HdR A₀, ((Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom
          (l ⊗ₜ[ℤ] o)) • y = π l • act (dp0 k) (𝟙 _) a o y := fun y ↦ rfl
      rw [e1, e2, hm.bcMap.map_smulₛₗ, hact]
      rfl
    | add r s hr hs =>
      rw [add_smul, hm.bcMap.map_add, hr, hs, map_add, add_smul]
  · intro h'
    let l : prim (divided₂ hI) (spMap π) A₀ →ₗ[Λ] k :=
      { toFun c := h' (m.pull c)
        map_add' c d := by rw [map_add, map_add]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh, hhl⟩ := Module.projective_lifting_property (Algebra.linearMap Λ k) l hπ
    exact ⟨hh, hm.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc : m.Corr x 0 := hm.corr_iff.2 hx
    exact mem_smul_top_of_forall _ x fun c ↦ RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))

end GlobalTheory.CrysFree
