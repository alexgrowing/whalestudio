import Formalism.IncomingBounds.IndexLastStep
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndexSigned

noncomputable section

open Module
open scoped Pointwise

namespace Formalism.IncomingBounds.LatticeIndexAlt

open Formalism.LatticeIndexTer

variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem map_comap_sub (W : Submodule K X) (A : Submodule O X) :
    (A.comap ((W.subtype).restrictScalars O)).map ((W.subtype).restrictScalars O) =
      A ⊓ W.restrictScalars O := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hW⟩
    exact ⟨⟨x, hW⟩, hx, rfl⟩

theorem qlen_comap (W : Submodule K X) (A B : Submodule O X) :
    qlen O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      qlen O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold qlen
  have hinj : Function.Injective ((W.subtype).restrictScalars O) := fun a b h => Subtype.ext h
  let e : ↥(A.comap ((W.subtype).restrictScalars O)) ≃ₗ[O] ↥(A ⊓ W.restrictScalars O) :=
    (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ (map_comap_sub W A))
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e ?_)
  ext z
  rw [Submodule.mem_map_equiv]
  have key : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) = (z : X) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hzW : (z : X) ∈ W := (Submodule.mem_inf.mp z.2).2
  constructor
  · intro h
    have h' : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) ∈ B := h
    rw [key] at h'
    show (z : X) ∈ B ⊓ W.restrictScalars O
    exact Submodule.mem_inf.mpr ⟨h', hzW⟩
  · intro h
    have h2 : (z : X) ∈ B ⊓ W.restrictScalars O := h
    have h' : (z : X) ∈ B := (Submodule.mem_inf.mp h2).1
    rw [← key] at h'
    exact h'

theorem idx_comap (W : Submodule K X) (A B : Submodule O X) :
    idx O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      idx O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold idx
  rw [qlen_comap W A B, qlen_comap W B A]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in

theorem isLat_scale {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (c : K) (hc : c ≠ 0) (A : Submodule O Y) (hA : IsLat O K Y A) :
    IsLat O K Y (A.map ((c • LinearMap.id : Y →ₗ[K] Y).restrictScalars O)) := by
  unfold IsLat at hA ⊢
  refine ⟨hA.1.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hA.2, Submodule.map_top,
    LinearMap.range_eq_top]
  intro x
  refine ⟨c⁻¹ • x, ?_⟩
  simp [smul_smul, hc]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem isLat_sup {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (A B : Submodule O Y) (hA : A.FG) (hB : IsLat O K Y B) : IsLat O K Y (A ⊔ B) := by
  unfold IsLat at hB ⊢
  refine ⟨hA.sup hB.1, ?_⟩
  rw [eq_top_iff, ← hB.2]
  exact Submodule.span_mono (fun x hx => Submodule.mem_sup_right hx)

end Formalism.IncomingBounds.LatticeIndexAlt

namespace Formalism.IncomingBounds

open Formalism.LatticeIndexTer LatticeIndexAlt

theorem index_last_reduction_holds : IndexLastStep := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ e M Θ hM hΘ W
  rw [← idx_comap W M Θ]
  have hc : (algebraMap O K ϖ) ^ e ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero)
  have hNl := isLat_sup (K := K)
    (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) Θ
    (hM.1.map _) hΘ
  generalize hN : M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)
    ⊔ Θ = N at hNl ⊢
  have hMN : ∀ x ∈ M, (algebraMap O K ϖ) ^ e • x ∈ N := by
    intro x hx
    rw [← hN]
    exact Submodule.mem_sup_left ⟨x, hx, by simp⟩
  have hΘN : Θ ≤ N := hN ▸ le_sup_right
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  let fW : W →ₗ[O] W := ((((algebraMap O K ϖ) ^ e) • LinearMap.id : W →ₗ[K] W).restrictScalars O)
  have hA₀ : IsLat O K W (M.comap ι) := LatticeIndexValuation.isLat_comap M hM W
  have hB₀ : IsLat O K W (Θ.comap ι) := LatticeIndexValuation.isLat_comap Θ hΘ W
  have hN₀ : IsLat O K W (N.comap ι) := LatticeIndexValuation.isLat_comap N hNl W
  have hS₀ : IsLat O K W ((M.comap ι).map fW) := isLat_scale _ hc _ hA₀
  have hadd1 := lattice_index_add O K W (M.comap ι) ((M.comap ι).map fW) (Θ.comap ι) hA₀ hS₀ hB₀
  have hadd2 := lattice_index_add O K W ((M.comap ι).map fW) (N.comap ι) (Θ.comap ι) hS₀ hN₀ hB₀
  have h1 : idx O W (M.comap ι) ((M.comap ι).map fW) = e * (finrank K W : ℤ) := by
    have hs := lattice_index_scale O K W ϖ hϖ (-e) (M.comap ι) hA₀
    rw [neg_neg] at hs
    exact hs
  have hSN : (M.comap ι).map fW ≤ N.comap ι := by
    rintro _ ⟨y, hy, rfl⟩
    have := hMN _ hy
    simpa [ι, fW] using this
  have h2 : idx O W ((M.comap ι).map fW) (N.comap ι) ≤ 0 := by
    unfold idx
    rw [subgroupData.qlen_eq_zero hSN]
    simp
  have hle : qlen O W (N.comap ι) (Θ.comap ι) ≤ qlen O X N Θ := by
    unfold qlen
    rw [LatticeIndexValuation.length_map_inj ι hι]
    refine subgroupData.length_le_of_le (Submodule.map_comap_le ι N) (Submodule.map_comap_le ι Θ) ?_
    intro x hx
    obtain ⟨⟨w, -, rfl⟩, hxΘ⟩ := Submodule.mem_inf.mp hx
    exact ⟨w, hxΘ, rfl⟩
  have h3 : idx O W (N.comap ι) (Θ.comap ι) ≤ ((qlen O X N Θ).toNat : ℤ) := by
    have h4 : (qlen O W (N.comap ι) (Θ.comap ι)).toNat ≤ (qlen O X N Θ).toNat :=
      ENat.toNat_le_toNat hle (lattice_quotient_finite O K X N Θ hNl hΘ)
    unfold idx
    omega
  linarith

end Formalism.IncomingBounds
