import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w' w₁ w₂ w₃ w₄ w₅ t₁ t₂ t₃ t₄ t₅

section Alg

theorem five_add {A₁ : Type w₁} {A₂ : Type w₂} {A₃ : Type w₃} {A₄ : Type w₄} {A₅ : Type w₅}
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : A₁ →+ A₂) (u₂ : A₂ →+ A₃) (u₃ : A₃ →+ A₄) (u₄ : A₄ →+ A₅)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (g₁ : A₁ →+ L₁) (g₂ : A₂ →+ L₂) (g₃ : A₃ →+ L₃) (g₄ : A₄ →+ L₄) (g₅ : A₅ →+ L₅)
    (c₁ : ∀ x, g₂ (u₁ x) = v₁ (g₁ x)) (c₂ : ∀ x, g₃ (u₂ x) = v₂ (g₂ x))
    (c₃ : ∀ x, g₄ (u₃ x) = v₃ (g₃ x)) (c₄ : ∀ x, g₅ (u₄ x) = v₄ (g₄ x))
    (eA₂ : Function.Exact u₁ u₂) (eA₃ : Function.Exact u₂ u₃) (eA₄ : Function.Exact u₃ u₄)
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (s₁ : Function.Surjective g₁) (b₂ : Function.Bijective g₂) (b₄ : Function.Bijective g₄)
    (i₅ : Function.Injective g₅) : Function.Bijective g₃ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : u₃ x = 0 := b₄.1 (by rw [c₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (eA₃ x).1 h1
    have h2 : v₂ (g₂ y) = 0 := by rw [← c₂, hx]
    obtain ⟨z, hz⟩ := (eL₂ _).1 h2
    obtain ⟨t, rfl⟩ := s₁ z
    have h3 : u₁ t = y := b₂.1 (by rw [c₁, hz])
    exact (eA₂ _).2 ⟨t, h3⟩
  · intro t
    obtain ⟨p, hp⟩ := b₄.2 (v₃ t)
    have h1 : u₄ p = 0 := i₅ (by
      rw [c₄, hp, map_zero]
      exact (eL₄ _).2 ⟨t, rfl⟩)
    obtain ⟨q, rfl⟩ := (eA₄ p).1 h1
    have h2 : v₃ (t - g₃ q) = 0 := by rw [map_sub, ← c₃, hp, sub_self]
    obtain ⟨y', hy'⟩ := (eL₃ _).1 h2
    obtain ⟨y, rfl⟩ := b₂.2 y'
    refine ⟨q + u₂ y, ?_⟩
    rw [map_add, c₂, hy']
    abel

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_ext {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (g h : (∀ i, N i ⊗[R] M i) →+ P) (H : ∀ i n x, g (Pi.single i (n ⊗ₜ x)) = h (Pi.single i (n ⊗ₜ x))) : g = h := by
  refine AddMonoidHom.functions_ext _ g h fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact H i n x
  | add x y hx hy => rw [Pi.single_add, map_add, map_add, hx, hy]

def piT {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) :
    (∀ i, N i ⊗[R] M i) →+ (∀ i, N i ⊗[R] M' i) where
  toFun t i := (u i).lTensor (N i) (t i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem piT_single {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) (i : ι) (n : N i) (x : M i) :
    piT (N := N) u (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ u i x) := by
  funext k
  by_cases h : k = i
  · subst h
    simp [piT]
  · simp [piT, Pi.single_eq_of_ne h]

theorem piT_exact [∀ i, Module.Flat R (N i)] {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (u : ∀ i, M₁ i →ₗ[R] M₂ i) (v : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (u i) (v i)) : Function.Exact (piT (N := N) u) (piT (N := N) v) := by
  intro t
  constructor
  · intro ht
    have h1 : ∀ i, ∃ s, (u i).lTensor (N i) s = t i := fun i =>
      (Module.Flat.lTensor_exact (N i) (h i) (t i)).1 (congrFun ht i)
    choose s hs using h1
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext i
    exact (Module.Flat.lTensor_exact (N i) (h i) _).2 ⟨s i, rfl⟩

theorem tens_zero {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {M' : Type w'} [AddCommGroup M']
    (hM : ∀ i, Subsingleton (M i)) (hM' : Subsingleton M') (f : ∀ i, N i → M i → M') :
    Tens R (N := N) (M := M) (M' := M') f := by
  have h0 : ∀ i, Subsingleton (N i ⊗[R] M i) := fun i => by
    refine ⟨fun x y => ?_⟩
    have : ∀ z : N i ⊗[R] M i, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [this x, this y]
  refine ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩, fun _ _ => by simp⟩,
    fun i n x => Subsingleton.elim _ _⟩

theorem tens_transfer {M : ι → Type w₁} {L : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)] {M' : Type t₁} {L' : Type t₂} [AddCommGroup M'] [AddCommGroup L']
    (u : ∀ i, M i ≃ₗ[R] L i) (u' : M' ≃+ L') (f : ∀ i, N i → M i → M') (h : ∀ i, N i → L i → L')
    (hc : ∀ i n x, h i n (u i x) = u' (f i n x))
    (hf : Tens R (N := N) (M := M) (M' := M') f) : Tens R (N := N) (M := L) (M' := L') h := by
  obtain ⟨g, hg⟩ := hf
  let e : (∀ i, N i ⊗[R] L i) ≃+ (∀ i, N i ⊗[R] M i) :=
    { toFun := piT (N := N) fun i => ((u i).symm : L i →ₗ[R] M i)
      invFun := piT (N := N) fun i => ((u i) : M i →ₗ[R] L i)
      left_inv := fun t => by
        funext i
        change (((u i) : M i →ₗ[R] L i).lTensor (N i)) ((((u i).symm : L i →ₗ[R] M i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      right_inv := fun t => by
        funext i
        change (((u i).symm : L i →ₗ[R] M i).lTensor (N i)) ((((u i) : M i →ₗ[R] L i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      map_add' := map_add _ }
  refine ⟨(e.trans g).trans u', fun i n x => ?_⟩
  obtain ⟨y, rfl⟩ := (u i).surjective x
  have : e (Pi.single i (n ⊗ₜ u i y)) = Pi.single i (n ⊗ₜ y) := by
    change piT (N := N) (fun i => ((u i).symm : L i →ₗ[R] M i)) _ = _
    rw [piT_single]
    simp
  simp only [AddEquiv.trans_apply, this, hg, hc]

theorem tens_five [∀ i, Module.Flat R (N i)]
    {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃} {M₄ : ι → Type w₄} {M₅ : ι → Type w₅}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (u₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (u₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (u₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (f₁ : ∀ i, N i → M₁ i → L₁) (f₂ : ∀ i, N i → M₂ i → L₂) (f₃ : ∀ i, N i → M₃ i → L₃)
    (f₄ : ∀ i, N i → M₄ i → L₄) (f₅ : ∀ i, N i → M₅ i → L₅)
    (c₁ : ∀ i n x, f₂ i n (u₁ i x) = v₁ (f₁ i n x)) (c₂ : ∀ i n x, f₃ i n (u₂ i x) = v₂ (f₂ i n x))
    (c₃ : ∀ i n x, f₄ i n (u₃ i x) = v₃ (f₃ i n x)) (c₄ : ∀ i n x, f₅ i n (u₄ i x) = v₄ (f₄ i n x))
    (eM₂ : ∀ i, Function.Exact (u₁ i) (u₂ i)) (eM₃ : ∀ i, Function.Exact (u₂ i) (u₃ i))
    (eM₄ : ∀ i, Function.Exact (u₃ i) (u₄ i))
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (h₁ : Tens R (N := N) (M := M₁) (M' := L₁) f₁) (h₂ : Tens R (N := N) (M := M₂) (M' := L₂) f₂)
    (h₄ : Tens R (N := N) (M := M₄) (M' := L₄) f₄) (h₅ : Tens R (N := N) (M := M₅) (M' := L₅) f₅)
    (hadd : ∀ i, ∃ F : N i ⊗[R] M₃ i →+ L₃, ∀ n x, F (n ⊗ₜ x) = f₃ i n x) :
    Tens R (N := N) (M := M₃) (M' := L₃) f₃ := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  obtain ⟨g₄, hg₄⟩ := h₄
  obtain ⟨g₅, hg₅⟩ := h₅
  choose F hF using hadd
  let g₃ : (∀ i, N i ⊗[R] M₃ i) →+ L₃ := ∑ i, (F i).comp (Pi.evalAddMonoidHom _ i)
  have hg₃ : ∀ i n x, g₃ (Pi.single i (n ⊗ₜ x)) = f₃ i n x := by
    intro i n x
    simp only [g₃, AddMonoidHom.finset_sum_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    rw [Finset.sum_eq_single i]
    · simp [hF]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  have b := five_add (piT (N := N) u₁) (piT (N := N) u₂) (piT (N := N) u₃) (piT (N := N) u₄) v₁ v₂ v₃ v₄
    g₁.toAddMonoidHom g₂.toAddMonoidHom g₃ g₄.toAddMonoidHom g₅.toAddMonoidHom
    (fun x => DFunLike.congr_fun (tens_ext (g₂.toAddMonoidHom.comp (piT (N := N) u₁)) (v₁.comp g₁.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₁, hg₂, c₁]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₃.comp (piT (N := N) u₂)) (v₂.comp g₂.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₂, hg₃, c₂]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₄.toAddMonoidHom.comp (piT (N := N) u₃)) (v₃.comp g₃)
      fun i n x => by simp [piT_single, hg₃, hg₄, c₃]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₅.toAddMonoidHom.comp (piT (N := N) u₄)) (v₄.comp g₄.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₄, hg₅, c₄]) x)
    (piT_exact u₁ u₂ eM₂) (piT_exact u₂ u₃ eM₃) (piT_exact u₃ u₄ eM₄) eL₂ eL₃ eL₄
    g₁.surjective g₂.bijective g₄.bijective g₅.injective
  exact ⟨AddEquiv.ofBijective g₃ b, hg₃⟩

end Alg

end GlobalTheory.CompanionTheory.LocBC
