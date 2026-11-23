import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section ExtensionInterSubspace

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_compl_inf (L : Submodule (𝓞 K) V) (hL : L.FG) (W₀ : Submodule K V) :
    ∃ C : Submodule (𝓞 K) V, C ≤ L ∧
      (∀ x ∈ L, ∃ a ∈ L ⊓ W₀.restrictScalars (𝓞 K), ∃ c ∈ C, x = a + c) ∧
      ∀ u ∈ Submodule.span K (C : Set V), u ∈ W₀ → u = 0 := by
  classical
  let N : Submodule (𝓞 K) L := (W₀.restrictScalars (𝓞 K)).comap L.subtype
  have htor : Submodule.torsion (𝓞 K) (L ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨z, rfl⟩ := N.mkQ_surjective q
    have h1 : ((a : 𝓞 K) • z) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using haq
    have ha0 : algebraMap (𝓞 K) K (a : 𝓞 K) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have h2 : (z : V) ∈ W₀ := by
      have h3 : ((a : 𝓞 K) • (z : V)) ∈ W₀ := h1
      rw [← algebraMap_smul K] at h3
      have h4 := W₀.smul_mem (algebraMap (𝓞 K) K a)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h4
    rw [Submodule.mem_bot]
    exact (Submodule.Quotient.mk_eq_zero N).2 h2
  have : Module.Flat (𝓞 K) (L ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have := Module.finitePresentation_of_finite (𝓞 K) (L ⧸ N)
  have : Module.Projective (𝓞 K) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ q, N.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  refine ⟨(LinearMap.range s).map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · intro x hx
    have hmem : ((⟨x, hx⟩ : L) - s (N.mkQ ⟨x, hx⟩)) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      have := hs' (N.mkQ ⟨x, hx⟩)
      simp only [Submodule.mkQ_apply] at this ⊢
      rw [this, sub_self]
    refine ⟨x - (s (N.mkQ ⟨x, hx⟩) : V), ⟨L.sub_mem hx (s _).2, hmem⟩,
      (s (N.mkQ ⟨x, hx⟩) : V), ⟨s (N.mkQ ⟨x, hx⟩), ⟨_, rfl⟩, rfl⟩, by abel⟩
  · intro u hu huW
    obtain ⟨d, hd, hdu⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS _ hu
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hdu
    have hW : ((s q : L) : V) ∈ W₀ := by
      rw [show ((s q : L) : V) = d • u from hq, ← algebraMap_smul K d u]
      exact W₀.smul_mem _ huW
    have hq0 : q = 0 := by
      rw [← hs' q]
      exact (Submodule.Quotient.mk_eq_zero N).2 hW
    have h5 : d • u = 0 := by
      rw [← hq, hq0, map_zero, map_zero]
    rw [← algebraMap_smul K d u] at h5
    exact (smul_eq_zero.1 h5).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)

end ExtensionInterSubspace

section Transport

variable {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def imgS (τ : V ≃+ V) (s : R ≃+* R) (h : ∀ (r : R) (x : V), τ (r • x) = s r • τ x)
    (N : Submodule R V) : Submodule R V where
  carrier := τ '' N
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, N.add_mem ha hb, map_add τ a b⟩
  zero_mem' := ⟨0, N.zero_mem, map_zero τ⟩
  smul_mem' := by
    rintro r _ ⟨a, ha, rfl⟩
    exact ⟨s.symm r • a, N.smul_mem _ ha, by rw [h, s.apply_symm_apply]⟩

theorem mem_imgS (τ : V ≃+ V) (s : R ≃+* R) (h : ∀ (r : R) (x : V), τ (r • x) = s r • τ x)
    (N : Submodule R V) (x : V) : x ∈ imgS τ s h N ↔ τ.symm x ∈ N := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨τ.symm x, hx, τ.apply_symm_apply x⟩

theorem symm_semilinear (τ : V ≃+ V) (s : R ≃+* R) (h : ∀ (r : R) (x : V), τ (r • x) = s r • τ x) :
    ∀ (r : R) (x : V), τ.symm (r • x) = s.symm r • τ.symm x := by
  intro r x
  rw [AddEquiv.symm_apply_eq, h, s.apply_symm_apply, τ.apply_symm_apply]

def imgIso (τ : V ≃+ V) (s : R ≃+* R) (h : ∀ (r : R) (x : V), τ (r • x) = s r • τ x) :
    Submodule R V ≃o Submodule R V where
  toFun := imgS τ s h
  invFun := imgS τ.symm s.symm (symm_semilinear τ s h)
  left_inv N := by
    ext x
    rw [mem_imgS, mem_imgS]
    simp
  right_inv N := by
    ext x
    rw [mem_imgS, mem_imgS]
    simp
  map_rel_iff' := by
    intro N M
    constructor
    · intro hle x hx
      have h1 : τ x ∈ imgS τ s h M := hle ⟨x, hx, rfl⟩
      rw [mem_imgS] at h1
      simpa using h1
    · intro hle x hx
      exact (mem_imgS τ s h M x).2 (hle ((mem_imgS τ s h N x).1 hx))

end Transport

end Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd
