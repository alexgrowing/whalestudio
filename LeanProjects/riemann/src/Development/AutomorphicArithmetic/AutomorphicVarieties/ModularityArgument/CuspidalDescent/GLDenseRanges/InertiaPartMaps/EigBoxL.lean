import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.Desc.V0

section Lin

variable {W W₂ Z Z₂ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W₂] [Module ℂ W₂]
  [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z₂] [Module ℂ Z₂]

private def sl (l : Z →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W l

private def sr (l : W →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] Z :=
  (TensorProduct.lid ℂ Z).toLinearMap ∘ₗ LinearMap.rTensor Z l

private theorem sl_tmul (l : Z →ₗ[ℂ] ℂ) (w : W) (z : Z) : sl l (w ⊗ₜ[ℂ] z) = l z • w := by
  simp [sl]

private theorem sr_tmul (l : W →ₗ[ℂ] ℂ) (w : W) (z : Z) : sr l (w ⊗ₜ[ℂ] z) = l w • z := by
  simp [sr]

end Lin

section Rep

variable {G Y X : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]

private theorem fs_intw {Q : Type} (c : Q → G) (τ : Representation ℂ G Y) (τ' : Representation ℂ G X)
    (f : Y →ₗ[ℂ] X) (hf : Function.Injective f) (h : ∀ g y, f (τ g y) = τ' g (f y)) (y : Y) :
    f ((∑ᶠ q, τ (c q)) y) = (∑ᶠ q, τ' (c q)) (f y) := by
  classical
  rcases subsingleton_or_nontrivial Y with hY | hY
  · rw [Subsingleton.elim y 0]
    simp
  · have hX : Nontrivial X := hf.nontrivial
    have ne1 : ∀ g, τ g ≠ 0 := by
      intro g hg
      obtain ⟨v, hv⟩ := exists_ne (0 : Y)
      have e : τ g (τ g⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hg] at e
      exact hv (by simpa using e.symm)
    have ne2 : ∀ g, τ' g ≠ 0 := by
      intro g hg
      obtain ⟨v, hv⟩ := exists_ne (0 : X)
      have e : τ' g (τ' g⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hg] at e
      exact hv (by simpa using e.symm)
    by_cases hQ : Finite Q
    · haveI := Fintype.ofFinite Q
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
      simp [LinearMap.sum_apply, map_sum, h]
    · haveI : Infinite Q := not_finite_iff_infinite.mp hQ
      rw [finsum_of_infinite_support, finsum_of_infinite_support]
      · simp
      · exact Set.infinite_univ.mono fun q _ => ne2 (c q)
      · exact Set.infinite_univ.mono fun q _ => ne1 (c q)

private theorem uOp_intw (I : Iwa G) (τ : Representation ℂ G Y) (τ' : Representation ℂ G X)
    (f : Y →ₗ[ℂ] X) (hf : Function.Injective f) (h : ∀ g y, f (τ g y) = τ' g (f y)) (a : G) (y : Y) :
    f (I.uOp τ a y) = I.uOp τ' a (f y) :=
  fs_intw _ τ τ' f hf h y

end Rep

section Main

variable {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] {S : V → UpperTheory.V.W.Plc L}

end Main

section Inv

variable {G H : Type} [Group G] [Group H] {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ)

private theorem mem_invT {Y : Type} [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ (G × H) Y) (F : Fin m → Y) :
    F ∈ invT K₁ K₂ τ₀ ρ ↔ (∀ (k : K₁) i, ∑ j, τ₀ k i j • ρ ((k : G), 1) (F j) = F i) ∧
      ∀ k ∈ K₂, ∀ i, ρ (1, k) (F i) = F i :=
  Iff.rfl

end Inv

section Box

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Box

section Part

variable {H Y X : Type} [Group H] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]

end Part

section InvE

variable {G H : Type} [Group G] [Group H] {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ)

private abbrev iE {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (G × H) W) (a : H →₀ ℤ) (N : ℕ) :
    Submodule ℂ (Fin m → W) :=
  invT K₁ K₂ τ₀ ρ ⊓ Submodule.pi Set.univ fun _ => ePart (ρ.comp (MonoidHom.inr G H)) a N

end InvE

private theorem eigBoxL_lemma {G Q Y X : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]
    (c : Q → G) (τ : Representation ℂ G Y) (τ' : Representation ℂ G X) (f : Y →ₗ[ℂ] X)
    (h : ∀ g y, f (τ g y) = τ' g (f y)) (y : Y) :
    f ((∑ᶠ q, τ (c q)) y) = (∑ᶠ q, τ' (c q)) (f y) := by
  classical
  rcases subsingleton_or_nontrivial X with hX | hX
  · exact Subsingleton.elim _ _
  rcases subsingleton_or_nontrivial Y with hY | hY
  · rw [Subsingleton.elim y 0]
    simp
  have ne1 : ∀ g, τ g ≠ 0 := by
    intro g hg
    obtain ⟨v, hv⟩ := exists_ne (0 : Y)
    have e : τ g (τ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hg] at e
    exact hv (by simpa using e.symm)
  have ne2 : ∀ g, τ' g ≠ 0 := by
    intro g hg
    obtain ⟨v, hv⟩ := exists_ne (0 : X)
    have e : τ' g (τ' g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hg] at e
    exact hv (by simpa using e.symm)
  by_cases hQ : Finite Q
  · haveI := Fintype.ofFinite Q
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp [LinearMap.sum_apply, map_sum, h]
  · haveI : Infinite Q := not_finite_iff_infinite.mp hQ
    rw [finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · exact Set.infinite_univ.mono fun q _ => ne2 (c q)
    · exact Set.infinite_univ.mono fun q _ => ne1 (c q)

private theorem eigBoxL_lemma_2 {Y X : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]
    (f : Y →ₗ[ℂ] X) (T : Module.End ℂ Y) (T' : Module.End ℂ X) (h : ∀ y, f (T y) = T' (f y)) (c : ℂ) (k : ℕ)
    (y : Y) : f (((T - c • 1) ^ k) y) = ((T' - c • 1) ^ k) (f y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp [h]

private theorem eigBoxL_lemma_3 {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V]
    {S : V → UpperTheory.V.W.Plc L} {Y X : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]
    (ρ₁ : Representation ℂ (GV n S) Y) (ρ₂ : Representation ℂ (GV n S) X) (g : Y →ₗ[ℂ] X)
    (hg : ∀ x y, g (ρ₁ x y) = ρ₂ x (g y)) (b : ℕ) (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ)
    (μ : V → Fin n → ℂ) (y : Y) (hy : y ∈ eigL S ρ₁ b φ μ) : g y ∈ eigL S ρ₂ b φ μ := by
  have hu : ∀ a z, g ((iwS n S).uOp ρ₁ a z) = (iwS n S).uOp ρ₂ a (g z) := by
    intro a z
    simp only [Iwa.uOp]
    exact eigBoxL_lemma _ ρ₁ ρ₂ g hg z
  rw [eigL] at hy ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, fixd, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Module.End.mem_eigenspace_iff,
    Module.End.mem_maxGenEigenspace] at hy ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hy
  refine ⟨⟨⟨fun u hu' => ?_, fun u hu' => ?_⟩, fun v i z => ?_⟩, fun v j => ?_⟩
  · rw [← hg, h1 u hu']
  · rw [← hg, h2 u hu']
  · rw [← hg, h3 v i z, map_smul]
  · obtain ⟨k, hk⟩ := h4 v j
    exact ⟨k, by rw [← eigBoxL_lemma_2 g _ _ (hu _) _ k, hk, map_zero]⟩

private theorem eigBoxL_lemma_4 {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V]
    {S : V → UpperTheory.V.W.Plc L} {Y X : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]
    (ρ₁ : Representation ℂ (GV n S) Y) (ρ₂ : Representation ℂ (GV n S) X) (g : Y →ₗ[ℂ] X)
    (hgi : Function.Injective g)
    (hg : ∀ x y, g (ρ₁ x y) = ρ₂ x (g y)) (b : ℕ) (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ)
    (μ : V → Fin n → ℂ) (y : Y) (hy : g y ∈ eigL S ρ₂ b φ μ) : y ∈ eigL S ρ₁ b φ μ := by
  have hu : ∀ a z, g ((iwS n S).uOp ρ₁ a z) = (iwS n S).uOp ρ₂ a (g z) := by
    intro a z
    simp only [Iwa.uOp]
    exact eigBoxL_lemma _ ρ₁ ρ₂ g hg z
  rw [eigL] at hy ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, fixd, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Module.End.mem_eigenspace_iff,
    Module.End.mem_maxGenEigenspace] at hy ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hy
  refine ⟨⟨⟨fun u hu' => ?_, fun u hu' => ?_⟩, fun v i z => ?_⟩, fun v j => ?_⟩
  · exact hgi (by rw [hg, h1 u hu'])
  · exact hgi (by rw [hg, h2 u hu'])
  · exact hgi (by rw [hg, h3 v i z, map_smul])
  · obtain ⟨k, hk⟩ := h4 v j
    exact ⟨k, hgi (by rw [eigBoxL_lemma_2 g _ _ (hu _) _ k, hk, map_zero])⟩

private theorem eigBoxL_lemma_5 {G H Y X : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup X] [Module ℂ X] {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (σ₁ : Representation ℂ (G × H) Y) (σ₂ : Representation ℂ (G × H) X) (g : Y →ₗ[ℂ] X)
    (hg : ∀ x y, g (σ₁ x y) = σ₂ x (g y)) (a : H →₀ ℤ) (N : ℕ) (F : Fin m → Y)
    (hF : F ∈ invT K₁ K₂ τ₀ σ₁ ⊓ Submodule.pi Set.univ fun _ => ePart (σ₁.comp (MonoidHom.inr G H)) a N) :
    (fun i => g (F i)) ∈ invT K₁ K₂ τ₀ σ₂ ⊓ Submodule.pi Set.univ fun _ => ePart (σ₂.comp (MonoidHom.inr G H)) a N := by
  have hE : ∀ y, g (opE (σ₁.comp (MonoidHom.inr G H)) a y) = opE (σ₂.comp (MonoidHom.inr G H)) a (g y) := by
    intro y
    simp [opE, Finsupp.sum, map_sum, hg]
  rw [Submodule.mem_inf, mem_invT, Submodule.mem_pi] at hF ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  refine ⟨⟨fun k i => ?_, fun k hk i => ?_⟩, fun i _ => ?_⟩
  · conv_rhs => rw [← h1 k i]
    simp [map_sum, hg]
  · rw [← hg, h2 k hk i]
  · have := h3 i (Set.mem_univ _)
    simp only [ePart, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.natCast_apply] at this ⊢
    rw [← hE, ← map_nsmul, ← map_sub, this, map_zero]

private theorem eigBoxL_lemma_6 {G H Y X : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup X] [Module ℂ X] {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (σ₁ : Representation ℂ (G × H) Y) (σ₂ : Representation ℂ (G × H) X) (g : Y →ₗ[ℂ] X)
    (hgi : Function.Injective g)
    (hg : ∀ x y, g (σ₁ x y) = σ₂ x (g y)) (a : H →₀ ℤ) (N : ℕ) (F : Fin m → Y)
    (hF : (fun i => g (F i)) ∈ invT K₁ K₂ τ₀ σ₂ ⊓ Submodule.pi Set.univ fun _ => ePart (σ₂.comp (MonoidHom.inr G H)) a N) :
    F ∈ invT K₁ K₂ τ₀ σ₁ ⊓ Submodule.pi Set.univ fun _ => ePart (σ₁.comp (MonoidHom.inr G H)) a N := by
  have hE : ∀ y, g (opE (σ₁.comp (MonoidHom.inr G H)) a y) = opE (σ₂.comp (MonoidHom.inr G H)) a (g y) := by
    intro y
    simp [opE, Finsupp.sum, map_sum, hg]
  rw [Submodule.mem_inf, mem_invT, Submodule.mem_pi] at hF ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  refine ⟨⟨fun k i => hgi ?_, fun k hk i => hgi ?_⟩, fun i _ => ?_⟩
  · rw [← h1 k i]
    simp [map_sum, hg]
  · rw [hg, h2 k hk i]
  · have := h3 i (Set.mem_univ _)
    simp only [ePart, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.natCast_apply] at this ⊢
    apply hgi
    rw [map_zero, map_sub, map_nsmul, hE, this]

private theorem eigBoxL_lemma_7 {W Z : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (A : Submodule ℂ W) (t : W ⊗[ℂ] Z) (ht : ∀ l : Z →ₗ[ℂ] ℂ, sl l t ∈ A) :
    t ∈ LinearMap.range (LinearMap.rTensor Z A.subtype) := by
  classical
  set b := Module.Free.chooseBasis ℂ Z
  set e := TensorProduct.equivFinsuppOfBasisRight (M := W) b with he_def
  have he : ∀ i, e t i = sl (b.coord i) t := by
    intro i
    have key : (Finsupp.lapply i) ∘ₗ e.toLinearMap = sl (b.coord i) := by
      apply TensorProduct.ext'
      intro w z
      simp [he_def, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, sl_tmul]
    exact LinearMap.congr_fun key t
  have ht' : t = (e t).sum fun i w => w ⊗ₜ[ℂ] b i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [ht', Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨⟨e t i, (he i).symm ▸ ht _⟩ ⊗ₜ b i, by simp⟩

private theorem eigBoxL_lemma_8 {W Z : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (B : Submodule ℂ Z) (t : W ⊗[ℂ] Z) (ht : ∀ l : W →ₗ[ℂ] ℂ, sr l t ∈ B) :
    t ∈ LinearMap.range (LinearMap.lTensor W B.subtype) := by
  classical
  set b := Module.Free.chooseBasis ℂ W
  set e := TensorProduct.equivFinsuppOfBasisLeft (N := Z) b with he_def
  have he : ∀ i, e t i = sr (b.coord i) t := by
    intro i
    have key : (Finsupp.lapply i) ∘ₗ e.toLinearMap = sr (b.coord i) := by
      apply TensorProduct.ext'
      intro w z
      simp [he_def, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, sr_tmul]
    exact LinearMap.congr_fun key t
  have ht' : t = (e t).sum fun i z => b i ⊗ₜ[ℂ] z := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  rw [ht', Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨b i ⊗ₜ ⟨e t i, (he i).symm ▸ ht _⟩, by simp⟩

private theorem eigBoxL_lemma_9 {W Z : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (A : Submodule ℂ W) (B : Submodule ℂ Z) (t : W ⊗[ℂ] Z) (h1 : ∀ l : Z →ₗ[ℂ] ℂ, sl l t ∈ A)
    (h2 : ∀ l : W →ₗ[ℂ] ℂ, sr l t ∈ B) : t ∈ LinearMap.range (TensorProduct.map A.subtype B.subtype) := by
  obtain ⟨u, rfl⟩ := eigBoxL_lemma_7 A t h1
  have hu : u ∈ LinearMap.range (LinearMap.lTensor A B.subtype) := by
    refine eigBoxL_lemma_8 B u fun l' => ?_
    obtain ⟨l, hl⟩ := LinearMap.exists_extend l'
    have key : (sr l' : A ⊗[ℂ] Z →ₗ[ℂ] Z) = sr l ∘ₗ LinearMap.rTensor Z A.subtype := by
      rw [← hl]
      apply TensorProduct.ext'
      intro w z
      simp [sr_tmul]
    rw [key, LinearMap.comp_apply]
    exact h2 l
  obtain ⟨v, rfl⟩ := hu
  exact ⟨v, by rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]⟩

private theorem eigBoxL_lemma_10 {Γ Δ W W' : Type} [Group Γ] [Group Δ] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ Γ W) (κ : Representation ℂ Δ W') (l : W' →ₗ[ℂ] ℂ)
    (x : Γ) (y : W ⊗[ℂ] W') : sl l ((box ρ κ).comp (MonoidHom.inl Γ Δ) x y) = ρ x (sl l y) := by
  have key : sl l ∘ₗ ((box ρ κ).comp (MonoidHom.inl Γ Δ) x) = ρ x ∘ₗ sl l := by
    apply TensorProduct.ext'
    intro w z
    simp [box, Representation.tprod_apply, sl_tmul]
  exact LinearMap.congr_fun key y

private theorem eigBoxL_lemma_11 {Γ Δ W W' : Type} [Group Γ] [Group Δ] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ Γ W) (κ : Representation ℂ Δ W') (l : W →ₗ[ℂ] ℂ)
    (x : Δ) (y : W ⊗[ℂ] W') : sr l ((box ρ κ).comp (MonoidHom.inr Γ Δ) x y) = κ x (sr l y) := by
  have key : sr l ∘ₗ ((box ρ κ).comp (MonoidHom.inr Γ Δ) x) = κ x ∘ₗ sr l := by
    apply TensorProduct.ext'
    intro w z
    simp [box, Representation.tprod_apply, sr_tmul]
  exact LinearMap.congr_fun key y

private theorem eigBoxL_lemma_12 {Γ Δ W W' : Type} [Group Γ] [Group Δ] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ Γ W) (κ : Representation ℂ Δ W')
    (x : Γ) (w : W) (z : W') : (box ρ κ).comp (MonoidHom.inl Γ Δ) x (w ⊗ₜ[ℂ] z) = ρ x w ⊗ₜ[ℂ] z := by
  simp [box, Representation.tprod_apply]

private theorem eigBoxL_lemma_13 {Γ Δ W W' : Type} [Group Γ] [Group Δ] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ Γ W) (κ : Representation ℂ Δ W')
    (x : Δ) (w : W) (z : W') : (box ρ κ).comp (MonoidHom.inr Γ Δ) x (w ⊗ₜ[ℂ] z) = w ⊗ₜ[ℂ] κ x z := by
  simp [box, Representation.tprod_apply]

theorem eigBoxL {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] {S : V → UpperTheory.V.W.Plc L}
    {G H W W' X : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GV n S) W) (κ : Representation ℂ (G × H) W')
    (π : Representation ℂ (GV n S × (G × H)) X) (f : W ⊗[ℂ] W' →ₗ[ℂ] X) (hf : Function.Injective f)
    (hint : Intw (box ρ κ) π f) (m : ℕ) (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (b : ℕ)
    (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ) (μ : V → Fin n → ℂ) (a : H →₀ ℤ) (N : ℕ) :
    Module.rank ℂ ↥((invT K₁ K₂ τ₀ (π.comp (MonoidHom.inr _ _)) ⊓ Submodule.pi Set.univ fun _ =>
        ePart ((π.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr G H)) a N) ⊓ Submodule.pi Set.univ fun _ =>
      LinearMap.range f ⊓ eigL S (π.comp (MonoidHom.inl _ _)) b φ μ) =
      Module.rank ℂ (eigL S ρ b φ μ) * Module.rank ℂ ↥(invT K₁ K₂ τ₀ κ ⊓ Submodule.pi Set.univ fun _ => ePart (κ.comp (MonoidHom.inr G H)) a N) := by
  classical
  unfold Intw at hint
  have hl : ∀ x : GV n S, ∀ y, f ((box ρ κ).comp (MonoidHom.inl _ _) x y) = (π.comp (MonoidHom.inl _ _)) x (f y) :=
    fun x y => hint _ _
  have hr : ∀ x : G × H, ∀ y, f ((box ρ κ).comp (MonoidHom.inr _ _) x y) = (π.comp (MonoidHom.inr _ _)) x (f y) :=
    fun x y => hint _ _
  set A := eigL S ρ b φ μ with hA
  set B := invT K₁ K₂ τ₀ κ ⊓ Submodule.pi Set.univ fun _ => ePart (κ.comp (MonoidHom.inr G H)) a N with hB
  set Φ : W ⊗[ℂ] (Fin m → W') →ₗ[ℂ] (Fin m → X) :=
    LinearMap.pi fun i => f ∘ₗ LinearMap.lTensor W (LinearMap.proj i) with hΦ_def
  set M : A ⊗[ℂ] B →ₗ[ℂ] W ⊗[ℂ] (Fin m → W') := TensorProduct.map A.subtype B.subtype with hM_def
  have hΦ : ∀ t i, Φ t i = f (LinearMap.lTensor W (LinearMap.proj i) t) := fun t i => rfl
  have hpr : ∀ t i, TensorProduct.piRight ℂ ℂ W (fun _ : Fin m => W') t i =
      LinearMap.lTensor W (LinearMap.proj i) t := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul w F => simp
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hΦi : Function.Injective Φ := by
    intro t t' h
    apply (TensorProduct.piRight ℂ ℂ W (fun _ : Fin m => W')).injective
    funext i
    rw [hpr, hpr]
    exact hf (by rw [← hΦ, ← hΦ, h])
  have hMi : Function.Injective M :=
    TensorProduct.map_injective_of_flat_flat _ _ A.injective_subtype B.injective_subtype
  have hP : ((invT K₁ K₂ τ₀ (π.comp (MonoidHom.inr _ _)) ⊓ Submodule.pi Set.univ fun _ =>
        ePart ((π.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr G H)) a N) ⊓ Submodule.pi Set.univ fun _ =>
      LinearMap.range f ⊓ eigL S (π.comp (MonoidHom.inl _ _)) b φ μ) = LinearMap.range (Φ ∘ₗ M) := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_inf, Submodule.mem_pi] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx2' := fun i => Submodule.mem_inf.mp (hx2 i (Set.mem_univ i))
      choose s hs using fun i => (hx2' i).1
      set t := (TensorProduct.piRight ℂ ℂ W (fun _ : Fin m => W')).symm s with ht_def
      have hts : ∀ i, LinearMap.lTensor W (LinearMap.proj i) t = s i := by
        intro i
        rw [← hpr, ht_def, LinearEquiv.apply_symm_apply]
      have hΦt : Φ t = x := by
        funext i
        rw [hΦ, hts, hs]
      have hsE : ∀ i, s i ∈ eigL S ((box ρ κ).comp (MonoidHom.inl _ _)) b φ μ := fun i =>
        eigBoxL_lemma_4 _ _ f hf hl b φ μ (s i) (by rw [hs]; exact (hx2' i).2)
      have hsB : s ∈ invT K₁ K₂ τ₀ ((box ρ κ).comp (MonoidHom.inr _ _)) ⊓ Submodule.pi Set.univ fun _ =>
          ePart (((box ρ κ).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr G H)) a N := by
        refine eigBoxL_lemma_6 K₁ K₂ τ₀ _ _ f hf hr a N s ?_
        have e : (fun i => f (s i)) = x := funext hs
        rw [e]
        exact hx1
      have h1 : ∀ l : (Fin m → W') →ₗ[ℂ] ℂ, sl l t ∈ A := by
        intro l
        have key : ∀ t' : W ⊗[ℂ] (Fin m → W'), sl l t' =
            ∑ i, sl (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => W') i) (LinearMap.lTensor W (LinearMap.proj i) t') := by
          intro t'
          induction t' using TensorProduct.induction_on with
          | zero => simp
          | tmul w F =>
            simp only [sl_tmul, LinearMap.lTensor_tmul, LinearMap.coe_comp, Function.comp_apply,
              LinearMap.coe_proj, Function.eval, LinearMap.coe_single]
            rw [← Finset.sum_smul, ← map_sum, Finset.univ_sum_single]
          | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]
        rw [key]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [hts]
        exact eigBoxL_lemma_3 _ ρ _ (eigBoxL_lemma_10 ρ κ _) b φ μ (s i) (hsE i)
      have h2 : ∀ l : W →ₗ[ℂ] ℂ, sr l t ∈ B := by
        intro l
        have key : ∀ (t' : W ⊗[ℂ] (Fin m → W')) i, sr l t' i = sr l (LinearMap.lTensor W (LinearMap.proj i) t') := by
          intro t' i
          induction t' using TensorProduct.induction_on with
          | zero => simp
          | tmul w F => simp [sr_tmul]
          | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
        have e : sr l t = fun i => sr l (s i) := funext fun i => by rw [key, hts]
        rw [e]
        exact eigBoxL_lemma_5 K₁ K₂ τ₀ _ κ (sr l) (eigBoxL_lemma_11 ρ κ l) a N s hsB
      obtain ⟨u, hu⟩ := eigBoxL_lemma_9 A B t h1 h2
      refine ⟨u, ?_⟩
      show Φ (M u) = x
      rw [show M u = t from hu, hΦt]
    · rintro ⟨u, rfl⟩
      induction u using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        exact zero_mem _
      | add x y hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | tmul p F =>
        have e : (Φ ∘ₗ M) (p ⊗ₜ F) = fun i => f ((p : W) ⊗ₜ ((F : Fin m → W') i)) := by
          funext i
          simp [hΦ_def, hM_def]
        rw [e, Submodule.mem_inf, Submodule.mem_pi]
        refine ⟨?_, fun i _ => Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self f _, ?_⟩⟩
        · refine eigBoxL_lemma_5 K₁ K₂ τ₀ κ _ (f ∘ₗ TensorProduct.mk ℂ W W' p) (fun x z => ?_) a N F F.2
          simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
          rw [← eigBoxL_lemma_13 ρ κ, hr]
        · refine eigBoxL_lemma_3 ρ _ (f ∘ₗ (TensorProduct.mk ℂ W W').flip (F.1 i)) (fun x w => ?_) b φ μ p p.2
          simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
          rw [← eigBoxL_lemma_12 ρ κ, hl]
  rw [hP, rank_range_of_injective _ (by rw [LinearMap.coe_comp]; exact hΦi.comp hMi), rank_tensorProduct']

end UpperTheory.V.Z.Desc.V0
