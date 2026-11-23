import Mathlib
open Matrix

namespace GlobalTheory.BlockInvertibleLocal

theorem exists_linearMap_injective_add_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (a c : V →ₗ[k] V) (h : LinearMap.ker a ⊓ LinearMap.ker c = ⊥) :
    ∃ x : V →ₗ[k] V, Function.Injective (a + x ∘ₗ c) := by
  set W := LinearMap.range (c ∘ₗ (LinearMap.ker a).subtype) with hWdef
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range a)
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  have hinjK : Function.Injective (c ∘ₗ (LinearMap.ker a).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : (u : V) ∈ LinearMap.ker a ⊓ LinearMap.ker c :=
      Submodule.mem_inf.2 ⟨u.2, by simpa using hu⟩
    rw [h, Submodule.mem_bot] at hu'
    exact Subtype.ext hu'
  have h1 := LinearMap.finrank_range_of_inj hinjK
  have h2 := Submodule.finrank_add_eq_of_isCompl hR
  have h3 := LinearMap.finrank_range_add_finrank_ker a
  have hdim : Module.finrank k W = Module.finrank k R := by rw [hWdef, h1]; omega
  let e : W ≃ₗ[k] R := LinearEquiv.ofFinrankEq W R hdim
  let x : V →ₗ[k] V := LinearMap.ofIsCompl hW (R.subtype ∘ₗ e.toLinearMap) 0
  refine ⟨x, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top : c v ∈ W ⊔ W')
  have hxw : x (c v) = ((e ⟨w, hw⟩ : R) : V) := by
    rw [← hsum, map_add]
    have hl := LinearMap.ofIsCompl_left_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w, hw⟩
    have hr := LinearMap.ofIsCompl_right_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w', hw'⟩
    simp only at hl hr
    rw [hl, hr]; simp
  have hv' : a v + ((e ⟨w, hw⟩ : R) : V) = 0 := by
    rw [← hxw]; simpa using hv
  have hav : a v = 0 := by
    refine Submodule.disjoint_def.1 hR.disjoint (a v) (LinearMap.mem_range_self a v) ?_
    rw [eq_neg_of_add_eq_zero_left hv']
    exact R.neg_mem (e ⟨w, hw⟩).2
  have he0 : ((e ⟨w, hw⟩ : R) : V) = 0 := by simpa [hav] using hv'
  have hw0 : w = 0 := by
    have : e ⟨w, hw⟩ = 0 := Subtype.ext he0
    have : (⟨w, hw⟩ : W) = 0 := by simpa using this
    simpa using congrArg Subtype.val this
  have hcvW : c v ∈ W := ⟨⟨v, hav⟩, rfl⟩
  have hcvW' : c v ∈ W' := by rw [← hsum, hw0, zero_add]; exact hw'
  have hcv : c v = 0 := Submodule.disjoint_def.1 hW.disjoint _ hcvW hcvW'
  have hmem : v ∈ LinearMap.ker a ⊓ LinearMap.ker c := Submodule.mem_inf.2 ⟨hav, hcv⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

theorem exists_isUnit_det_add_mul_of_field {k : Type} [Field k] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) k) (h : IsUnit (fromBlocks A B C D).det) :
    ∃ X : Matrix (Fin n) (Fin n) k, IsUnit (A + X * C).det := by
  have hinj : Function.Injective (fromBlocks A B C D).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 h)
  have hker : LinearMap.ker (toLin' A) ⊓ LinearMap.ker (toLin' C) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, toLin'_apply, toLin'_apply] at hv
    have hz : (fromBlocks A B C D) *ᵥ (Sum.elim v 0) = (fromBlocks A B C D) *ᵥ 0 := by
      rw [fromBlocks_mulVec, mulVec_zero]
      ext i <;> cases i <;> simp [hv.1, hv.2]
    have h2 := hinj hz
    rw [Submodule.mem_bot]
    funext i
    exact congrFun h2 (Sum.inl i)
  obtain ⟨x, hx⟩ := exists_linearMap_injective_add_comp _ _ hker
  refine ⟨LinearMap.toMatrix' x, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  convert hx using 1
  funext v
  simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]

theorem exists_isUnit_det_add_mul : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  intro O _ _ n A B C D h
  have h' : IsUnit (fromBlocks (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))
      (C.map (IsLocalRing.residue O)) (D.map (IsLocalRing.residue O))).det := by
    rw [← fromBlocks_map]
    have := h.map (IsLocalRing.residue O)
    rwa [RingHom.map_det] at this
  obtain ⟨Y, hY⟩ := exists_isUnit_det_add_mul_of_field _ _ _ _ h'
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) O, X.map (IsLocalRing.residue O) = Y :=
    ⟨Y.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq]⟩
  refine ⟨X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add _), Matrix.map_mul, hX]
  exact hY.ne_zero

end GlobalTheory.BlockInvertibleLocal
