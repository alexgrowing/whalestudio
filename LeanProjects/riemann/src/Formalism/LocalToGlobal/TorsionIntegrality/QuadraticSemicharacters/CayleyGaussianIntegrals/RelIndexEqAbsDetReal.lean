import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant

noncomputable section
open scoped BigOperators ComplexConjugate
open Module

namespace Formalism.L2.Th1.H

section Real

theorem relIndex_eq_abs_det_real {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L₁ L₂ : AddSubgroup E) (h : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℝ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  classical
  subst h₁ h₂
  rw [← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure] at h ⊢
  have hle : Submodule.span ℤ (Set.range b₁) ≤ Submodule.span ℤ (Set.range b₂) :=
    fun x hx => h hx
  set S₁ := Submodule.span ℤ (Set.range b₁) with hS₁
  set S₂ := Submodule.span ℤ (Set.range b₂) with hS₂
  let B₂ : Basis ι ℤ S₂ := b₂.restrictScalars ℤ
  let B₁ : Basis ι ℤ S₁ := b₁.restrictScalars ℤ
  let N : Submodule ℤ S₂ := S₁.comap S₂.subtype
  let BN : Basis ι ℤ N := B₁.map (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : Module.Free ℤ S₂ := Module.Free.of_basis B₂
  haveI : Module.Finite ℤ S₂ := Module.Finite.of_basis B₂
  have key := Submodule.natAbs_det_basis_change B₂ N BN
  have hcard : Nat.card (S₂ ⧸ N) = S₁.toAddSubgroup.relIndex S₂.toAddSubgroup := rfl
  have hrepr : ∀ (m : S₂) (i : ι), ((B₂.repr m i : ℤ) : ℝ) = b₂.repr (m : E) i := fun m i => by
    rw [← Basis.restrictScalars_repr_apply ℤ b₂ m i]; simp [B₂]
  have hv : ∀ j, (((BN j : N) : S₂) : E) = b₁ j := fun j => by
    simp [BN, B₁, Basis.map_apply, Submodule.comapSubtypeEquivOfLe]
    exact Basis.restrictScalars_apply ℤ b₁ j
  have hdet : ((B₂.det (Subtype.val ∘ BN) : ℤ) : ℝ) = b₂.det b₁ := by
    rw [Basis.det_apply, Basis.det_apply]
    rw [show ((Matrix.det (B₂.toMatrix (Subtype.val ∘ BN)) : ℤ) : ℝ)
        = (Int.castRingHom ℝ) (Matrix.det (B₂.toMatrix (Subtype.val ∘ BN))) from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, Function.comp_apply,
      eq_intCast]
    rw [hrepr, hv]
  rw [← hcard, ← key, ← hdet, Nat.cast_natAbs, Int.cast_abs]

theorem relIndex_map_real {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L₁ L₂ : AddSubgroup E) (h : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℝ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂))
    (f : E ≃ₗ[ℝ] E) (hf : L₁.map (f : E →ₗ[ℝ] E).toAddMonoidHom ≤ L₂) :
    ((L₁.map (f : E →ₗ[ℝ] E).toAddMonoidHom).relIndex L₂ : ℝ)
      = (L₁.relIndex L₂ : ℝ) * |LinearMap.det (f : E →ₗ[ℝ] E)| := by
  classical
  have hb : L₁.map (f : E →ₗ[ℝ] E).toAddMonoidHom = .closure (Set.range (b₁.map f)) := by
    rw [h₁, AddMonoidHom.map_closure, ← Set.range_comp]
    congr 1
  rw [relIndex_eq_abs_det_real _ L₂ hf (b₁.map f) b₂ hb h₂,
    relIndex_eq_abs_det_real L₁ L₂ h b₁ b₂ h₁ h₂]
  have e : ⇑(b₁.map f) = (f : E →ₗ[ℝ] E) ∘ b₁ := by ext i; simp
  rw [e, Basis.det_comp, abs_mul, mul_comm]

theorem exists_basis_of_lattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : AddSubgroup E) (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set E) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, Λ = .closure (Set.range b) := by
  classical
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Module.Free.chooseBasis ℤ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨Basis.ofZLatticeBasis ℝ L b', ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure, Basis.ofZLatticeBasis_span]
  rfl

end Real

theorem isLat_inf {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {Λ Λ₁ : AddSubgroup V}
    (hL : IsLat Λ) (hi : Λ₁.relIndex Λ ≠ 0) : IsLat (Λ ⊓ Λ₁) := by
  obtain ⟨hd, hs⟩ := hL
  refine ⟨DiscreteTopology.of_subset (s := (Λ : Set V)) hd (fun x hx => hx.1), ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  have hm : (Λ₁.relIndex Λ) • x ∈ Λ ⊓ Λ₁ := by
    refine ⟨Λ.nsmul_mem hx _, ?_⟩
    have := AddSubgroup.nsmul_index_mem (Λ₁.addSubgroupOf Λ) ⟨x, hx⟩
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [AddSubgroup.relIndex] using this
  have hn : ((Λ₁.relIndex Λ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  have e : x = ((Λ₁.relIndex Λ : ℕ) : ℝ)⁻¹ • ((Λ₁.relIndex Λ) • x) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem unitary_index : UnitaryIndex := by
  intro V _ _ _ H Λ α δ Ae hL hU
  have hle : latA Λ δ Ae ≤ Λ := by
    rintro y ⟨x, ⟨hxΛ, ⟨z, hz, rfl⟩⟩, rfl⟩
    show Ae (δ z) ∈ Λ
    rw [hU.cay, LinearEquiv.symm_apply_apply]
    exact Λ.sub_mem hxΛ hz
  refine ⟨hle, ?_⟩
  obtain ⟨b₂, hb₂⟩ := exists_basis_of_lattice Λ hL.1 hL.2
  have hL1 := isLat_inf hL hU.idx₁
  obtain ⟨b₁, hb₁⟩ := exists_basis_of_lattice (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) hL1.1 hL1.2
  let f : V ≃ₗ[ℝ] V := Ae.restrictScalars ℝ
  have hmap : latA Λ δ Ae
      = (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ).map (f : V →ₗ[ℝ] V).toAddMonoidHom := rfl
  have key := relIndex_map_real (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) Λ inf_le_left b₁ b₂ hb₁ hb₂ f
    (by rw [← hmap]; exact hle)
  unfold relIdx
  rw [hmap, key, AddSubgroup.inf_relIndex_left]
  congr 1
  have hd : LinearMap.det (f : V →ₗ[ℝ] V)
      = Algebra.norm ℝ (LinearMap.det (Ae : V →ₗ[ℂ] V)) := LinearMap.det_restrictScalars
  rw [hd, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  exact abs_of_nonneg (by positivity)

end Formalism.L2.Th1.H
