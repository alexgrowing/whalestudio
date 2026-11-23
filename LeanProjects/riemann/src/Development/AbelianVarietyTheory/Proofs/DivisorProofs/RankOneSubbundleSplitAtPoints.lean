import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.QCoh

namespace GlobalTheory.VB

theorem exists_forall_isUnit_sum_mul {κ : Type} [Field κ] [Infinite κ] {T : Type} [Finite T]
    (R : T → Type) [∀ t, CommRing (R t)] [∀ t, IsLocalRing (R t)] (σ : ∀ t, κ →+* R t) {k : ℕ}
    (u : ∀ t, Fin k → R t) (hu : ∀ t, ∃ i, IsUnit (u t i)) :
    ∃ c : Fin k → κ, ∀ t, IsUnit (∑ i, σ t (c i) * u t i) := by
  let p : T → Submodule κ (Fin k → κ) := fun t =>
    { carrier := {c | ∑ i, σ t (c i) * u t i ∈ IsLocalRing.maximalIdeal (R t)}
      add_mem' := fun {a b} ha hb => by
        simpa [add_mul, Finset.sum_add_distrib] using Ideal.add_mem _ (Set.mem_setOf.1 ha) (Set.mem_setOf.1 hb)
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simpa [Finset.mul_sum, mul_assoc] using Ideal.mul_mem_left _ (σ t a) (Set.mem_setOf.1 hc) }
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p fun t ht => by
    obtain ⟨i, hi⟩ := hu t
    have h : ∑ j, σ t ((Pi.single i 1 : Fin k → κ) j) * u t j ∈ IsLocalRing.maximalIdeal (R t) :=
      ht.ge (Submodule.mem_top (x := Pi.single i 1))
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
      one_mul] at h
    exact h hi
  exact ⟨c, fun t => not_not.1 (hc t)⟩

theorem exists_retraction_of_isUnit {R P M : Type} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] (g : Module.Basis (Fin 1) R P) (f : P →ₗ[R] M) (l : M →ₗ[R] R)
    (h : IsUnit (l (f (g 0)))) : ∃ ρ : M →ₗ[R] P, ρ ∘ₗ f = LinearMap.id := by
  obtain ⟨v, hv⟩ := h.exists_left_inv
  refine ⟨(v • l).smulRight (g 0), g.ext fun i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [hv]

variable {X : Scheme.{0}} {F G : X.Modules}

theorem stalkLinear_finset_sum {ι : Type} (s : Finset ι) (φ : ι → (G ⟶ F)) (x : X) :
    stalkLinear (∑ i ∈ s, φ i) x = ∑ i ∈ s, stalkLinear (φ i) x :=
  map_sum (AddMonoidHom.mk' (fun ψ : G ⟶ F => stalkLinear ψ x) fun a b => stalkLinear_add a b x) φ s

theorem stalkLinear_smulHom_apply (a : Γ(X, ⊤)) (x : X) (t : (F.presheaf.stalk x :)) :
    stalkLinear (smulHom F a) x t = X.presheaf.germ ⊤ x trivial a • t := by
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ, smulHom_app_apply, germ_smul]
  exact congrArg (· • _) (X.presheaf.germ_res_apply _ x hV a)

theorem eq_top_of_epi_sigma {k : ℕ} (φ : (∐ fun _ : Fin k => G) ⟶ F) [Epi φ] (x : X)
    (N : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))
    (h : ∀ i t, stalkLinear (Sigma.ι (fun _ : Fin k => G) i ≫ φ) x t ∈ N) : N = ⊤ := by
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  let e := biproduct.isoCoproduct fun _ : Fin k => G
  have he : e.hom ≫ φ = ∑ i, biproduct.π (fun _ : Fin k => G) i ≫
      Sigma.ι (fun _ : Fin k => G) i ≫ φ := by
    rw [biproduct.isoCoproduct_hom, biproduct.desc_eq, Preadditive.sum_comp]
    simp only [Category.assoc]
  refine top_le_iff.1 fun t _ => ?_
  obtain ⟨t, rfl⟩ := stalkLinear_surjective (e.hom ≫ φ) x t
  rw [he, stalkLinear_finset_sum, LinearMap.sum_apply]
  refine sum_mem fun i _ => ?_
  rw [stalkLinear_comp]
  exact h i _

theorem IsTorsionFree.mono_of_injective_generic [IsIntegral X] (h : IsTorsionFree G) (φ : G ⟶ F)
    (hφ : Function.Injective (stalkLinear φ (genericPoint X))) : Mono φ := by
  refine mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  refine sub_eq_zero.1 (h W hη _ (hφ ?_))
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, map_zero, sub_eq_zero]
  exact congrArg _ e

theorem exists_line_subsheaf_split_at_finite : ∀ (κ : Type) [Field κ] [Infinite κ] (C : Scheme.{0})
    [Algebra κ Γ(C, ⊤)] [IsIntegral C], IsProjOver (strHom κ C) → ∀ (F : C.Modules) (r : ℕ),
    IsVB F (r + 1) → ∀ S : Set C, S.Finite → ∃ (G : C.Modules) (φ : G ⟶ F), IsVB G 1 ∧ Mono φ ∧
      ∀ x ∈ S, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :),
        ρ ∘ₗ GlobalTheory.QCoh.stalkLinear φ x = LinearMap.id := by
  intro κ _ _ C _ _ hp F r hF S hS
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have := hF.isFiniteQC
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma F).exists
  have hG := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize GlobalTheory.LB.toMod (lbZPow A (-n)) = G at φ hφ hG
  let ψ : Fin k → (G ⟶ F) := fun i => Sigma.ι (fun _ : Fin k => G) i ≫ φ
  have b := fun x => (hF.nonempty_basis_stalk x).some
  have g := fun x => (hG.nonempty_basis_stalk x).some
  let T : Set C := insert (genericPoint C) S
  have : Finite T := (hS.insert _).to_subtype
  obtain ⟨c, hc⟩ := exists_forall_isUnit_sum_mul (fun x : T => C.presheaf.stalk x.1)
    (fun x => (C.presheaf.germ ⊤ x.1 trivial).hom.comp (algebraMap κ Γ(C, ⊤)))
    (fun x i => (b x.1).coord 0 (stalkLinear (ψ i) x.1 (g x.1 0))) fun x => by
      by_contra! H
      have h := eq_top_of_epi_sigma φ x.1
        (Submodule.comap ((b x.1).coord 0) (IsLocalRing.maximalIdeal (C.presheaf.stalk x.1)))
        fun i t => by
          rw [Submodule.mem_comap, ← (g x.1).sum_repr t, Fin.sum_univ_one, map_smul, map_smul]
          exact Ideal.mul_mem_left _ _ (H i)
      have h1 := h.ge (Submodule.mem_top (x := b x.1 0))
      rw [Submodule.mem_comap, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same] at h1
      exact h1 isUnit_one
  let α : G ⟶ F := ∑ i, ψ i ≫ smulHom F (algebraMap κ Γ(C, ⊤) (c i))
  have key : ∀ x ∈ T, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :),
      ρ ∘ₗ stalkLinear α x = LinearMap.id := fun x hx => by
    refine exists_retraction_of_isUnit (g x) _ ((b x).coord 0) ?_
    convert hc ⟨x, hx⟩ using 1
    rw [stalkLinear_finset_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stalkLinear_comp, LinearMap.comp_apply, stalkLinear_smulHom_apply, map_smul]
    rfl
  refine ⟨G, α, hG, hG.isTorsionFree.mono_of_injective_generic α ?_,
    fun x hx => key x (Set.mem_insert_of_mem _ hx)⟩
  obtain ⟨ρ, hρ⟩ := key _ (Set.mem_insert _ _)
  exact LinearMap.injective_of_comp_eq_id _ _ hρ

end GlobalTheory.VB
