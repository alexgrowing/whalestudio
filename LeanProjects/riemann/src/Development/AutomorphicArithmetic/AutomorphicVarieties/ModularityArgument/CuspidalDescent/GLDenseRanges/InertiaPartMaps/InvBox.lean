import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.EigBox

noncomputable section

open UpperTheory.V.Hi UpperTheory.V.Z.J.D
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

section Lin

variable {W Z : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

private def sl (l : Z →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W l

private def sr (l : W →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] Z :=
  (TensorProduct.lid ℂ Z).toLinearMap ∘ₗ LinearMap.rTensor Z l

private theorem sl_tmul (l : Z →ₗ[ℂ] ℂ) (w : W) (z : Z) : sl l (w ⊗ₜ[ℂ] z) = l z • w := by
  simp [sl]

private theorem sr_tmul (l : W →ₗ[ℂ] ℂ) (w : W) (z : Z) : sr l (w ⊗ₜ[ℂ] z) = l w • z := by
  simp [sr]

end Lin

section Box

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Box

private theorem sl_rTensor_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (l : B →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] A) (x : A ⊗[ℂ] B) : sl l (LinearMap.rTensor B T x) = T (sl l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u v => rw [LinearMap.rTensor_tmul, sl_tmul, sl_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem sr_lTensor_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (l : A →ₗ[ℂ] ℂ) (T : B →ₗ[ℂ] B) (x : A ⊗[ℂ] B) : sr l (LinearMap.lTensor A T x) = T (sr l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u v => rw [LinearMap.lTensor_tmul, sr_tmul, sr_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mem_range_rTensor_subtype_of_forall_sl_coord_mem {A B ι : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (𝒞 : Module.Basis ι ℂ B) (U : Submodule ℂ A) (x : A ⊗[ℂ] B) (h : ∀ i, sl (𝒞.coord i) x ∈ U) :
    x ∈ LinearMap.range (LinearMap.rTensor B U.subtype) := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right 𝒞 x
  have hc : ∀ i, c i ∈ U := by
    intro i
    have e1 : (TensorProduct.equivFinsuppOfBasisRight 𝒞) (c.sum fun i m => m ⊗ₜ[ℂ] 𝒞 i) = c := by
      rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.apply_symm_apply]
    have e2 := TensorProduct.equivFinsuppOfBasisRight_apply 𝒞 (c.sum fun i m => m ⊗ₜ[ℂ] 𝒞 i) i
    rw [e1] at e2
    rw [e2]
    exact h i
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨⟨c i, hc i⟩ ⊗ₜ 𝒞 i, ?_⟩
  rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]

private theorem memL_lemma_4 {A B ι : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ℬ : Module.Basis ι ℂ A) (V : Submodule ℂ B) (x : A ⊗[ℂ] B) (h : ∀ i, sr (ℬ.coord i) x ∈ V) :
    x ∈ LinearMap.range (LinearMap.lTensor A V.subtype) := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left ℬ x
  have hc : ∀ i, c i ∈ V := by
    intro i
    have e1 : (TensorProduct.equivFinsuppOfBasisLeft ℬ) (c.sum fun i n => ℬ i ⊗ₜ[ℂ] n) = c := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.apply_symm_apply]
    have e2 := TensorProduct.equivFinsuppOfBasisLeft_apply ℬ (c.sum fun i n => ℬ i ⊗ₜ[ℂ] n) i
    rw [e1] at e2
    rw [e2]
    exact h i
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨ℬ i ⊗ₜ ⟨c i, hc i⟩, ?_⟩
  rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]

private theorem box_inl_apply_eq_rTensor {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (g : G)
    (y : W ⊗[ℂ] W') : box ρ κ (g, 1) y = LinearMap.rTensor W' (ρ g) y := by
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one]
  rfl

private theorem box_inr_apply_eq_lTensor {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (h : H)
    (y : W ⊗[ℂ] W') : box ρ κ (1, h) y = LinearMap.lTensor W (κ h) y := by
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one]
  rfl

private theorem opE_box_comp_inr_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (a : H →₀ ℤ)
    (w : W) (y : W') : opE ((box ρ κ).comp (MonoidHom.inr G H)) a (w ⊗ₜ y) = w ⊗ₜ opE κ a y := by
  simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, MonoidHom.comp_apply,
    MonoidHom.inr_apply, box, Representation.tprod_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one,
    TensorProduct.map_tmul, Module.End.one_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

private theorem mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (a : H →₀ ℤ)
    (N : ℕ) (y : W ⊗[ℂ] W') :
    y ∈ ePart ((box ρ κ).comp (MonoidHom.inr G H)) a N ↔ LinearMap.lTensor W (opE κ a - (N : Module.End ℂ W')) y = 0 := by
  have e : opE ((box ρ κ).comp (MonoidHom.inr G H)) a - (N : Module.End ℂ (W ⊗[ℂ] W')) =
      LinearMap.lTensor W (opE κ a - (N : Module.End ℂ W')) := by
    apply TensorProduct.ext'
    intro w v
    simp [opE_box_comp_inr_tmul, TensorProduct.tmul_sub, Module.End.natCast_apply, TensorProduct.tmul_smul]
  unfold ePart
  rw [LinearMap.mem_ker, e]

private theorem mem_invT_iff_sum_smul_inl_eq_and_inr_fixed {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] {m : ℕ}
    (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (ρ : Representation ℂ (G × H) W)
    (F : Fin m → W) :
    F ∈ invT K₁ K₂ τ₀ ρ ↔ (∀ (k : K₁) (i : Fin m), ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • ρ (↑k, 1) (F j) = F i) ∧
      ∀ k ∈ K₂, ∀ i, ρ (1, k) (F i) = F i := Iff.rfl

set_option maxHeartbeats 800000 in
theorem invBox : InvBox := by
  intro G H W W' _ _ _ _ _ _ ρ κ m K₁ K₂ τ₀ a N
  classical
  let Ψ := TensorProduct.piLeft ℂ W' (fun _ : Fin m => W)
  let T : K₁ → Module.End ℂ (Fin m → W) := fun k =>
    LinearMap.pi fun i => ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • (ρ k ∘ₗ LinearMap.proj j)
  have hT : ∀ k (F : Fin m → W) i, T k F i = ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • ρ k (F j) := by
    intro k F i
    simp only [T, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  haveI indexFFirst : Module.Free ℂ (Fin m → W) := Module.Free.of_divisionRing ℂ _
  haveI indexFSecond : Module.Free ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') := Module.Free.of_divisionRing ℂ _
  haveI indexFThird : Module.Free ℂ ↥(inv1 K₁ τ₀ ρ) := Module.Free.of_divisionRing ℂ _
  haveI iL1 : Module.Flat ℂ (Fin m → W) := Module.Flat.of_free
  haveI iL2 : Module.Flat ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') := Module.Flat.of_free
  have hV1 : ∀ F : Fin m → W, F ∈ inv1 K₁ τ₀ ρ ↔ ∀ k, T k F = F := by
    intro F
    rw [show inv1 K₁ τ₀ ρ = invT K₁ ⊥ τ₀ (ρ.comp (MonoidHom.fst G Unit)) from rfl, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed]
    simp only [MonoidHom.comp_apply, MonoidHom.coe_fst, map_one, Module.End.one_apply, implies_true, and_true,
      funext_iff, hT]
  have hV2 : ∀ w : W', w ∈ fixd κ K₂ ⊓ ePart κ a N ↔ (∀ l ∈ K₂, κ l w = w) ∧ (opE κ a - (N : Module.End ℂ W')) w = 0 := by
    intro w
    rw [Submodule.mem_inf]
    exact Iff.rfl
  have hΨt : ∀ (F : Fin m → W) (w : W') i, Ψ (F ⊗ₜ w) i = F i ⊗ₜ w := by
    intro F w i
    simp [Ψ]
  have hΨl : ∀ (g : W' →ₗ[ℂ] W') x i, Ψ (LinearMap.lTensor _ g x) i = LinearMap.lTensor W g (Ψ x i) := by
    intro g x i
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]
    | tmul F w => rw [LinearMap.lTensor_tmul, hΨt, hΨt, LinearMap.lTensor_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hΨr : ∀ k x i, Ψ (LinearMap.rTensor W' (T k) x) i =
      ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • LinearMap.rTensor W' (ρ k) (Ψ x j) := by
    intro k x i
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
    | tmul F w =>
      simp only [LinearMap.rTensor_tmul, hΨt, hT, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]
  let ι : ↥(inv1 K₁ τ₀ ρ) ⊗[ℂ] ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') →ₗ[ℂ] (Fin m → W ⊗[ℂ] W') :=
    Ψ.toLinearMap ∘ₗ TensorProduct.map (inv1 K₁ τ₀ ρ).subtype (fixd κ K₂ ⊓ ePart κ a N).subtype
  have hinj : Function.Injective ι :=
    Ψ.injective.comp (TensorProduct.map_injective_of_flat_flat (inv1 K₁ τ₀ ρ).subtype
      (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype (Submodule.injective_subtype _) (Submodule.injective_subtype _))
  have hrange : invE K₁ K₂ τ₀ (box ρ κ) a N = LinearMap.range ι := by
    apply le_antisymm
    · intro F hF
      obtain ⟨x, rfl⟩ := Ψ.surjective F
      unfold invE at hF
      rw [Submodule.mem_inf, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed, Submodule.mem_pi] at hF
      obtain ⟨⟨h1, h2⟩, h3⟩ := hF
      have hl : ∀ l ∈ K₂, LinearMap.lTensor _ (κ l) x = x := by
        intro l hl
        apply Ψ.injective
        funext i
        rw [hΨl, ← box_inr_apply_eq_lTensor ρ κ l, h2 l hl i]
      have he : LinearMap.lTensor _ (opE κ a - (N : Module.End ℂ W')) x = 0 := by
        apply Ψ.injective
        funext i
        rw [hΨl, map_zero, Pi.zero_apply, ← mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero ρ κ a N]
        exact h3 i (Set.mem_univ i)
      obtain ⟨y, hy⟩ := memL_lemma_4 (Module.Basis.ofVectorSpace ℂ (Fin m → W)) (fixd κ K₂ ⊓ ePart κ a N) x (fun i => by
        rw [hV2]
        refine ⟨fun l hl' => ?_, ?_⟩
        · rw [← sr_lTensor_apply, hl l hl']
        · rw [← sr_lTensor_apply, he, map_zero])
      have hk : ∀ k, LinearMap.rTensor _ (T k) y = y := by
        intro k
        apply Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W'))
        have e := LinearMap.congr_fun ((LinearMap.lTensor_comp_rTensor (f := T k) (g := (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype)).trans
          (LinearMap.rTensor_comp_lTensor (f := T k) (g := (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype)).symm) y
        simp only [LinearMap.comp_apply] at e
        rw [e, hy]
        apply Ψ.injective
        funext i
        rw [hΨr]
        refine (Finset.sum_congr rfl fun j _ => ?_).trans (h1 k i)
        rw [box_inl_apply_eq_rTensor]
      obtain ⟨z, hz⟩ := mem_range_rTensor_subtype_of_forall_sl_coord_mem (Module.Basis.ofVectorSpace ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W')) (inv1 K₁ τ₀ ρ) y (fun i => by
        rw [hV1]
        intro k
        rw [← sl_rTensor_apply, hk k])
      refine ⟨z, ?_⟩
      rw [← hy, ← hz]
      simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | add s t hs ht => rw [map_add]; exact add_mem hs ht
      | tmul v w =>
        have hv := (hV1 v).1 v.2
        obtain ⟨hw1, hw2⟩ := (hV2 w).1 w.2
        have e : ι (v ⊗ₜ w) = fun i => (v : Fin m → W) i ⊗ₜ (w : W') := by
          funext i
          simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul, Submodule.subtype_apply, hΨt]
        rw [e]
        unfold invE
        rw [Submodule.mem_inf, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed, Submodule.mem_pi]
        refine ⟨⟨fun k i => ?_, fun l hl i => ?_⟩, fun i _ => ?_⟩
        · simp only [box_inl_apply_eq_rTensor, LinearMap.rTensor_tmul]
          conv_rhs => rw [← hv k, hT, TensorProduct.sum_tmul]
          simp only [TensorProduct.smul_tmul']
        · rw [box_inr_apply_eq_lTensor, LinearMap.lTensor_tmul, hw1 l hl]
        · rw [mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero, LinearMap.lTensor_tmul, hw2, TensorProduct.tmul_zero]
  rw [hrange, rank_range_of_injective ι hinj, rank_tensorProduct']

end UpperTheory.V.Z.Desc.V0
