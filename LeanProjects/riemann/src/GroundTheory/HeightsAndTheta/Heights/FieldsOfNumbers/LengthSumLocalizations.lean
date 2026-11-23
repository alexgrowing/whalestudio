import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module TensorProduct

noncomputable section

namespace LengthSumLocalizations

variable {B : Type*} [CommRing B]

theorem algebraMap_quot_maximalIdeal_surjective (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*)
    [CommRing C] [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    Function.Surjective (algebraMap B (C ⧸ IsLocalRing.maximalIdeal C)) := by
  intro _ y
  obtain ⟨x, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 C).surjective y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨b, by rw [← hx]; rfl⟩

theorem isSimpleModule_quot_maximalIdeal (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    IsSimpleModule B (C ⧸ IsLocalRing.maximalIdeal C) := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  let : Field (C ⧸ IsLocalRing.maximalIdeal C) := Ideal.Quotient.field _
  rw [← Module.length_eq_one_iff,
    Module.length_eq_of_surjective (algebraMap_quot_maximalIdeal_surjective 𝔪 C)]
  exact Module.length_eq_one _ _

theorem isFiniteLength_of_atPrime (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] (M : Type*) [AddCommGroup M] [Module C M]
    [instB : Module B M] [instT : IsScalarTower B C M] (hM : IsFiniteLength C M) :
    IsFiniteLength B M := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  revert instB instT
  induction hM with
  | of_subsingleton => intro _ _; exact .of_subsingleton
  | @of_simple_quotient M _ _ N hs hN ih =>
    intro _ _
    have hN' : IsFiniteLength B (N.restrictScalars B) := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    have := isSimpleModule_quot_maximalIdeal 𝔪 C
    have : IsSimpleModule B (M ⧸ N.restrictScalars B) :=
      IsSimpleModule.congr ((Submodule.Quotient.restrictScalarsEquiv B N).trans
        (e.restrictScalars B))
    exact .of_simple_quotient hN'

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal B) [h𝔪 : ∀ i, (𝔪 i).IsMaximal]
  (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsLocalization.AtPrime (C i) (𝔪 i)]

omit [Fintype ι] in

theorem length_tensor_quot (hinj : Function.Injective 𝔪) (i j : ι) :
    Module.length (C i) (C i ⊗[B] (B ⧸ 𝔪 j)) = if i = j then 1 else 0 := by
  have : IsLocalRing (C i) := IsLocalization.AtPrime.isLocalRing (C i) (𝔪 i)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i) (𝔪 j)).toLinearEquiv.length_eq]
  split_ifs with h
  · subst h
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal (𝔪 i) (C i)]
    have : IsSimpleModule (C i) (C i ⧸ IsLocalRing.maximalIdeal (C i)) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  · have hne : ¬ 𝔪 j ≤ 𝔪 i := fun hle =>
      h (hinj ((h𝔪 j).eq_of_le (h𝔪 i).ne_top hle)).symm
    obtain ⟨x, hxj, hxi⟩ := Set.not_subset.mp hne
    have htop : (𝔪 j).map (algebraMap B (C i)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxj)
        (IsLocalization.map_units (C i) (⟨x, hxi⟩ : (𝔪 i).primeCompl))
    rw [htop, Module.length_eq_zero_iff]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl

omit [Fintype ι] [DecidableEq ι] in

theorem pi_mk_injective (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (N : Type*)
    [AddCommGroup N] [Module B N] :
    Function.Injective (LinearMap.pi fun i => TensorProduct.mk B (C i) N 1) := by
  rw [injective_iff_map_eq_zero]
  intro n hn
  by_contra hne
  have hlt : LinearMap.ker (LinearMap.toSpanSingleton B N n) ≠ ⊤ := by
    intro htop
    apply hne
    have h1 : (1 : B) ∈ LinearMap.ker (LinearMap.toSpanSingleton B N n) := htop ▸ Submodule.mem_top
    simpa using h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hlt
  obtain ⟨i, rfl⟩ := hall M hM
  have : IsLocalizedModule (𝔪 i).primeCompl (TensorProduct.mk B (C i) N 1) :=
    (isLocalizedModule_iff_isBaseChange (𝔪 i).primeCompl (C i) _).mpr
      (TensorProduct.isBaseChange B N (C i))
  have h0 : TensorProduct.mk B (C i) N 1 n = 0 := by
    simpa using congrFun hn i
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (𝔪 i).primeCompl _).mp h0
  exact s.2 (hle (by rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hs))

theorem length_eq_sum_of_isFiniteLength (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [instA : Module A N] [instT : IsScalarTower A B N]
    (hN : IsFiniteLength B N) :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  revert instA instT
  induction hN with
  | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
  | @of_simple_quotient M _ _ P hs hP ih =>
    intro _ _
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain ⟨j, rfl⟩ := hall I hI
    let f : P →ₗ[B] M := P.subtype
    let g : M →ₗ[B] B ⧸ 𝔪 j := e.toLinearMap ∘ₗ P.mkQ
    have hf : Function.Injective f := P.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp P.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by
      rw [LinearEquiv.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype])
    have key : ∀ i, Module.length (C i) (C i ⊗[B] M) =
        Module.length (C i) (C i ⊗[B] P) + if i = j then 1 else 0 := by
      intro i
      have : Module.Flat B (C i) := IsLocalization.flat (C i) (𝔪 i).primeCompl
      rw [Module.length_eq_add_of_exact (AlgebraTensorModule.lTensor (C i) (C i) f)
        (AlgebraTensorModule.lTensor (C i) (C i) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (C i) hg) (Module.Flat.lTensor_exact (C i) hfg),
        length_tensor_quot 𝔪 C hinj i j]
    rw [Module.length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg, ih]
    simp only [key, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem length_eq_sum (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  by_cases hN : IsFiniteLength B N
  · exact length_eq_sum_of_isFiniteLength 𝔪 C hinj hall A N hN
  have hA : Module.length A N = ⊤ := by
    by_contra hA
    apply hN
    have hA' := isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hA)
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hA'.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsFiniteLength (C i) (C i ⊗[B] N) := by
    by_contra! h
    apply hN
    have hpi : Module.length B (∀ i, C i ⊗[B] N) ≠ ⊤ := by
      rw [Module.length_pi_of_fintype, ENat.sum_ne_top]
      exact fun i _ => Module.length_ne_top_iff.mpr
        (isFiniteLength_of_atPrime (𝔪 i) (C i) _ (h i))
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top hpi (Module.length_le_of_injective _ (pi_mk_injective 𝔪 C hall N))
  have : Nontrivial (B ⧸ 𝔪 i) := Ideal.Quotient.nontrivial_iff.mpr (h𝔪 i).ne_top
  have hd : Module.length A (B ⧸ 𝔪 i) ≠ 0 := (Module.length_pos (R := A)).ne'
  have hti : Module.length (C i) (C i ⊗[B] N) = ⊤ := by
    by_contra h'
    exact hi (Module.length_ne_top_iff.mp h')
  rw [hA, eq_comm, ← top_le_iff]
  calc (⊤ : ℕ∞) = Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
        rw [hti, ENat.top_mul hd]
    _ ≤ _ := Finset.single_le_sum (f := fun i =>
        Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i))
        (fun _ _ => zero_le) (Finset.mem_univ i)

end LengthSumLocalizations

end

end GroundTheory.Heights₂.Heights.FieldNumbers
