import Mathlib
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.ProjModFinIso

variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem finrank_prod_eq (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by
  have h1 := (TensorProduct.isBaseChange R (M × N) (FractionRing R)).finrank_eq
  have h2 := (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq
  have h2' := (TensorProduct.isBaseChange R N (FractionRing R)).finrank_eq
  have h3 := (TensorProduct.prodRight R (FractionRing R) (FractionRing R) M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

theorem projective_of_isTorsionFree (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

theorem finrank_ideal (I : Ideal R) (h : I ≠ ⊥) : Module.finrank R I = 1 := by
  have h1 : Module.finrank R I ≤ 1 := by simpa using Submodule.finrank_le I
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr h
  have h2 := Module.finrank_pos (R := R) (M := I)
  omega

theorem nonempty_equiv_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have key : ∀ (z : R), z ≠ 0 → ∀ K : Ideal R, Nonempty (K ≃ₗ[R] ↥(Ideal.span {z} * K)) := by
    intro z hz K
    have hinj : Function.Injective (LinearMap.mulLeft R z) := fun a b hab => mul_left_cancel₀ hz hab
    refine ⟨(Submodule.equivMapOfInjective _ hinj K).trans (LinearEquiv.ofEq _ _ ?_)⟩
    ext w
    rw [Submodule.mem_map, Ideal.mem_span_singleton_mul]
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  exact ⟨(key x hx I).some.trans ((LinearEquiv.ofEq _ _ hxy).trans (key y hy J).some.symm)⟩

theorem exists_split (X : Type) [AddCommGroup X] [Module R X] [Module.Projective R X]
    [Nontrivial X] :
    ∃ (I : (Ideal R)⁰) (K : Submodule R X), Nonempty (X ≃ₗ[R] K × (I : Ideal R)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R X)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hsx : s x ≠ 0 := by
    intro h
    apply hx
    have := LinearMap.congr_fun hs x
    simp only [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm
  obtain ⟨a, ha⟩ : ∃ a, s x a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsx (Finsupp.ext h)
  let f : X →ₗ[R] R := Finsupp.lapply a ∘ₗ s
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h
    have hm : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [h, Submodule.mem_bot] at hm
    exact ha hm
  let I : (Ideal R)⁰ := ⟨LinearMap.range f, mem_nonZeroDivisors_of_ne_zero hI⟩
  let g := f.rangeRestrict
  haveI := projective_of_isTorsionFree (R := R) (LinearMap.range f)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id f.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype ⟨l, hl⟩
  exact ⟨I, LinearMap.ker g, ⟨e⟩⟩

theorem exists_equiv_pi (r : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.IsTorsionFree R X], Module.finrank R X = r →
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → (Ideal R)⁰), Fintype.card ι = r ∧
      Nonempty (X ≃ₗ[R] ((i : ι) → ((I i : Ideal R)))) := by
  induction r with
  | zero =>
    intro X _ _ _ _ h
    have : Subsingleton X := by
      by_contra hne
      rw [not_subsingleton_iff_nontrivial] at hne
      have := Module.finrank_pos (R := R) (M := X)
      omega
    exact ⟨Empty, inferInstance, Empty.elim, by simp, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ r ih =>
    intro X _ _ _ _ h
    have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := R) (by omega)
    haveI := projective_of_isTorsionFree (R := R) X
    obtain ⟨I, K, ⟨e⟩⟩ := exists_split (R := R) X
    have hK : Module.finrank R K = r := by
      have h1 := e.finrank_eq
      rw [finrank_prod_eq, finrank_ideal _ (by simpa using nonZeroDivisors.ne_zero I.2)] at h1
      omega
    obtain ⟨ι, _, J, hcard, ⟨eK⟩⟩ := ih K hK
    refine ⟨Option ι, inferInstance, fun o => o.elim I J, by simp [hcard], ⟨?_⟩⟩
    exact e ≪≫ₗ LinearEquiv.prodComm R _ _ ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _) eK ≪≫ₗ
      (LinearEquiv.piOptionEquivProd R (M := fun o => ((o.elim I J : (Ideal R)⁰) : Ideal R))).symm

theorem exists_finite_reps [Finite (ClassGroup R)] (q : ℕ) :
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} R), ∀ (X : Type) [AddCommGroup X] [Module R X]
      [Module.Finite R X] [Module.Projective R X], Module.finrank R X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[R] Y k) := by
  let rep : ClassGroup R → Ideal R := fun c => ((ClassGroup.mk0_surjective c).choose : Ideal R)
  have hrep : ∀ c : ClassGroup R, ClassGroup.mk0 (ClassGroup.mk0_surjective c).choose = c :=
    fun c => (ClassGroup.mk0_surjective c).choose_spec
  let S := Σ r : Fin (q + 1), (Fin r → ClassGroup R)
  let Y' : S → ModuleCat.{0} R := fun s => ModuleCat.of R ((b : Fin s.1) → rep (s.2 b))
  obtain ⟨n, ⟨eS⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨n, fun k => Y' (eS.symm k), ?_⟩
  intro X _ _ _ _ hX
  obtain ⟨ι, _, I, hcard, ⟨e⟩⟩ := exists_equiv_pi (R := R) (Module.finrank R X) X rfl
  let eι := Fintype.equivFin ι
  let s : S := ⟨⟨Fintype.card ι, by omega⟩, fun b => ClassGroup.mk0 (I (eι.symm b))⟩
  refine ⟨eS s, ?_⟩
  show Nonempty (X ≃ₗ[R] Y' (eS.symm (eS s)))
  rw [Equiv.symm_apply_apply]
  have hI : ∀ i, Nonempty ((I i : Ideal R) ≃ₗ[R] rep (ClassGroup.mk0 (I i))) := fun i =>
    nonempty_equiv_of_mk0_eq (hrep _).symm
  exact ⟨e ≪≫ₗ LinearEquiv.piCongrRight (fun i => (hI i).some) ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun i => ↥(rep (ClassGroup.mk0 (I i)))) eι⟩

theorem finitely_many_iso_classes : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ),
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  intro E _ _ q
  exact exists_finite_reps q

end GlobalTheory.ProjModFinIso
