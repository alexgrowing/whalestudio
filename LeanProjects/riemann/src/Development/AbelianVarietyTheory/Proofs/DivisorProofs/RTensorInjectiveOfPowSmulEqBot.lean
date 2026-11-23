import Mathlib

open TensorProduct LinearMap Function

namespace GlobalTheory.NilpotentFlat

theorem rTensor_lTensor_apply {R : Type} [CommRing R] {M M' A A' : Type} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup A] [Module R A] [AddCommGroup A']
    [Module R A'] (g : M →ₗ[R] M') (f : A →ₗ[R] A') (x : M ⊗[R] A) :
    rTensor A' g (lTensor M f x) = lTensor M' f (rTensor A g x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

theorem rTensor_injective_of_flat_baseChange {A C M N' N : Type} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup M] [Module A M] [Module.Flat C (C ⊗[A] M)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Injective ι) :
    Injective ((ι.restrictScalars A).rTensor M) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C N' M
  let e := AlgebraTensorModule.cancelBaseChange A C C N M
  have h1 : Injective (ι.rTensor (C ⊗[A] M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have key : ∀ z, (ι.restrictScalars A).rTensor M (e' z) = e (ι.rTensor (C ⊗[A] M) z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul n t =>
      induction t with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

theorem lTensor_injective_of_flat {A C F N' N : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup F] [Module A F] [Module C F] [IsScalarTower A C F] [Module.Flat C F]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Injective (ι.rTensor C)) : Injective (ι.lTensor F) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C F N'
  let e := AlgebraTensorModule.cancelBaseChange A C C F N
  have hι' : Injective (ι.baseChange C) := (LinearMap.lTensor_inj_iff_rTensor_inj (M := C) ι).mpr hι
  have h1 : Injective ((ι.baseChange C).lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have key : ∀ z, ι.lTensor F (e' z) = e ((ι.baseChange C).lTensor F z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul n t =>
      induction t with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

variable {B : Type} [CommRing B]

theorem rTensor_injective_of_extension {K L : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₂] [Module B N₂]
    [AddCommGroup N₃] [Module B N₃] (g₁ : N₁ →ₗ[B] N₂) (g₂ : N₂ →ₗ[B] N₃)
    (hg : Exact g₁ g₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : Injective (i.rTensor N₁)) (h₃ : Injective (i.rTensor N₃)) :
    Injective (i.rTensor N₂) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 : g₂.lTensor K x = 0 := by
    apply (injective_iff_map_eq_zero _).mp h₃
    rw [rTensor_lTensor_apply, hx, map_zero]
  obtain ⟨x₁, rfl⟩ := (lTensor_exact K hg hg₂ x).mp h2
  have h4 : i.rTensor N₁ x₁ = 0 := by
    apply (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := L) g₁ hg₁)
    rw [← rTensor_lTensor_apply, hx]
  simp [(injective_iff_map_eq_zero _).mp h₁ _ h4]

theorem rTensor_injective_quotient (I : Ideal B) {K L M : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L) (π : L →ₗ[B] M)
    (hi : Injective i) (hex : Exact i π) (hπ : Surjective π)
    (hIM : Injective (I.subtype.rTensor M)) : Injective (i.rTensor (B ⧸ I)) := by
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I) hex hπ hIM
    (Module.Flat.lTensor_preserves_injective_linearMap (M := B) i hi)
  exact (lTensor_inj_iff_rTensor_inj (B ⧸ I) i).mp h

theorem rTensor_injective_of_quotient_module (I : Ideal B) {K L M : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L)
    (π : L →ₗ[B] M) (hex : Exact i π) (hπ : Surjective π)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)] (hI : Injective (i.rTensor (B ⧸ I)))
    (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N] [IsScalarTower B (B ⧸ I) N] :
    Injective (i.rTensor N) := by
  let p : (N →₀ (B ⧸ I)) →ₗ[B ⧸ I] N := Finsupp.linearCombination (B ⧸ I) id
  have hp : Surjective p := fun n => ⟨Finsupp.single n 1, by simp [p]⟩
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := (LinearMap.ker p).subtype.restrictScalars B) (f₂ := p.restrictScalars B)
    (LinearMap.exact_subtype_ker_map p) hp hex hπ
    (rTensor_injective_of_flat_baseChange (LinearMap.ker p).subtype (Submodule.injective_subtype _))
    (lTensor_injective_of_flat (C := B ⧸ I) (F := N →₀ (B ⧸ I)) i hI)
  exact (lTensor_inj_iff_rTensor_inj N i).mp h

theorem rTensor_injective_of_pow_smul_eq_bot (I : Ideal B) {K L : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    (hbase : ∀ (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N]
      [IsScalarTower B (B ⧸ I) N], Injective (i.rTensor N)) (n : ℕ) :
    ∀ (N : Type) [AddCommGroup N] [Module B N], (I ^ n • ⊤ : Submodule B N) = ⊥ →
      Injective (i.rTensor N) := by
  induction n with
  | zero =>
    intro N _ _ hN
    have h0 : ∀ x : N, x = 0 := fun x => by
      have hx : x ∈ (I ^ 0 • ⊤ : Submodule B N) := by
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial
      rw [hN] at hx
      simpa using hx
    have hz : ∀ z : K ⊗[B] N, z = 0 := fun z => by
      induction z with
      | zero => rfl
      | tmul k x => rw [h0 x, tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    intro a b _
    rw [hz a, hz b]
  | succ n ih =>
    intro N _ _ hN
    let S : Submodule B N := I • ⊤
    refine rTensor_injective_of_extension i S.subtype S.mkQ (LinearMap.exact_subtype_mkQ S)
      S.injective_subtype (Submodule.mkQ_surjective S) (ih S ?_) (hbase (N ⧸ S))
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_smul'', Submodule.map_bot, Submodule.map_subtype_top, ← Submodule.mul_smul,
      ← pow_succ, hN]

theorem flat_of_isNilpotent : ∀ (B : Type) [CommRing B] (I : Ideal B), IsNilpotent I →
    ∀ (M : Type) [AddCommGroup M] [Module B M],
      Module.Flat (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) →
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype)) →
      Module.Flat B M := by
  intro B _ I hI M _ _ hflat hinj
  obtain ⟨n, hn⟩ := hI
  let π : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  have hπ : Surjective π := fun m => ⟨Finsupp.single m 1, by simp [π]⟩
  let K := LinearMap.ker π
  have hex : Exact K.subtype π := LinearMap.exact_subtype_ker_map π
  have hIM : Injective (I.subtype.rTensor M) := by
    have e : TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype) =
        (TensorProduct.lid B M).toLinearMap ∘ₗ I.subtype.rTensor M := by
      ext a m
      simp
    rw [e, LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  let e : ((B ⧸ I) ⊗[B] M) ≃ₗ[B ⧸ I] (M ⧸ (I • ⊤ : Submodule B M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  haveI : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M) := Module.Flat.of_linearEquiv e
  have hq := rTensor_injective_quotient I K.subtype π K.injective_subtype hex hπ hIM
  have hall := rTensor_injective_of_pow_smul_eq_bot I K.subtype
    (rTensor_injective_of_quotient_module I K.subtype π hex hπ hq) n
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective hex hπ
    (LinearMap.exact_subtype_mkQ J) (Submodule.mkQ_surjective J) (hall (B ⧸ J) ?_)
    (Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype)
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul]

end GlobalTheory.NilpotentFlat
