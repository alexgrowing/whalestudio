import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open scoped TensorProduct

theorem nonempty_equiv_prod_of_exact_of_projective {A : Type*} [CommRing A] {K F M : Type*}
    [AddCommGroup K] [Module A K] [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M]
    [Module.Projective A M] (g : K →ₗ[A] F) (f : F →ₗ[A] M) (hg : Function.Injective g)
    (hf : Function.Surjective f) (h : Function.Exact g f) : Nonempty (F ≃ₗ[A] K × M) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨(h.splitSurjectiveEquiv hg ⟨s, hs⟩).1⟩

theorem isStablyFree_baseChange_of_hasProjectiveDimensionLE (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Projective A (A ⊗[R] M) →
        Module.IsStablyFree A (A ⊗[R] M) := by
  induction n with
  | zero =>
    intro M _ _ _ h _
    have h1 : Projective (ModuleCat.of R M) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).2 h
    have h2 : Module.Projective R M := (IsProjective.iff_projective M).2 h1
    have h3 : Module.Free R M := Module.free_of_flat_of_isLocalRing
    infer_instance
  | succ n ih =>
    intro M _ _ _ h hp
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
      have hP : Projective (ModuleCat.of R (Fin m → R)) := inferInstance
      exact (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A) :=
      lTensor_exact A f.exact_subtype_ker_map hf
    have hinj : Function.Injective ((LinearMap.ker f).subtype.baseChange A) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
    have hsurj : Function.Surjective (f.baseChange A) := LinearMap.lTensor_surjective A hf
    obtain ⟨e⟩ := nonempty_equiv_prod_of_exact_of_projective _ _ hinj hsurj hex
    have hfree : Module.Free A ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) := Module.Free.of_equiv e
    have hKp : Module.Projective A (A ⊗[R] LinearMap.ker f) :=
      Module.Projective.of_split (LinearMap.inl A _ (A ⊗[R] M)) (LinearMap.fst A _ _)
        (LinearMap.ext fun _ ↦ rfl)
    have hKs := ih (LinearMap.ker f) hK hKp
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A (A ⊗[R] LinearMap.ker f)
    have : Module.Free A ((A ⊗[R] M) × ((A ⊗[R] LinearMap.ker f) × N)) :=
      Module.Free.of_equiv (M := ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) × N)
        (((LinearEquiv.prodComm A _ _).prodCongr (LinearEquiv.refl A N)).trans
          (LinearEquiv.prodAssoc A _ _ _))
    exact Module.IsStablyFree.of_free_prod A _ ((A ⊗[R] LinearMap.ker f) × N)

section cofactor

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] {n : ℕ}

theorem exists_surjective_exteriorPower_prod (bN : Module.Basis (Fin n) A N) :
    ∃ φ : ⋀[A]^(n + 1) (M × N) →ₗ[A] M, Function.Surjective φ := by
  let c : M × N →ₗ[A] (M × N) [⋀^Fin n]→ₗ[A] M :=
    { toFun := fun x ↦ (bN.det.compLinearMap (LinearMap.snd A M N)).smulRight x.1
      map_add' := fun x y ↦ AlternatingMap.ext fun _ ↦ by simp
      map_smul' := fun c x ↦ AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm] }
  refine ⟨exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin c),
    fun m ↦ ⟨exteriorPower.ιMulti A (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i)), ?_⟩⟩
  simp [c, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, Module.Basis.det_self]

end cofactor

theorem isPrincipal_of_isStablyFree {A : Type} [CommRing A] (J : Ideal A) [Module.Finite A J]
    [Module.IsStablyFree A J] : J.IsPrincipal := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim J ⊥]
    exact bot_isPrincipal
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A J
  let n := Module.finrank A N
  have hp : Module.finrank A (J × N) ≤ n + 1 := by
    have := LinearMap.finrank_le_finrank_of_injective
      (f := J.subtype.prodMap (LinearMap.id : N →ₗ[A] N))
      (Function.Injective.prodMap J.injective_subtype Function.injective_id)
    rwa [Module.finrank_prod (M := A), Module.finrank_self, add_comm] at this
  have h1 : Module.finrank A (⋀[A]^(n + 1) (J × N)) ≤ 1 := by
    rw [exteriorPower.finrank_eq]
    simpa using Nat.choose_le_choose (n + 1) hp
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
  obtain ⟨φ, hφ⟩ := exists_surjective_exteriorPower_prod (M := J) (Module.finBasis A N)
  refine ⟨(φ v : A), le_antisymm (fun y hy ↦ ?_) ?_⟩
  · obtain ⟨w, hw⟩ := hφ ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := hv w
    rw [map_smul] at hw
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hw⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (φ v).2

theorem isPrincipal_map_away_of_hasProjectiveDimensionLE :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R) (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ), HasProjectiveDimensionLE (ModuleCat.of R I) n → Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal := by
  intro R _ _ _ _ x R' _ _ _ I n h hp
  have hflat : Module.Flat R R' := IsLocalization.flat R' (Submonoid.powers x)
  have hb : IsBaseChange R' (Algebra.idealMap R' I) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers x) R' _
  have hp' : Module.Projective R' (R' ⊗[R] I) := Module.Projective.of_equiv hb.equiv.symm
  have hs := isStablyFree_baseChange_of_hasProjectiveDimensionLE R R' n I h hp'
  have := Module.IsStablyFree.equiv hb.equiv
  have := Module.Finite.equiv hb.equiv
  exact isPrincipal_of_isStablyFree _

end GlobalTheory
