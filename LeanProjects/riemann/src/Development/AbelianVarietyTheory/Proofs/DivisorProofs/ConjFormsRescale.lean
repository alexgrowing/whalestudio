import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

section Abstract

variable {K S V W W' : Type} [Field K] [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']

theorem rescale_span_eq {ι κ : Type} [Finite κ] (K0 : Subfield K) (f : Module.Basis ι K V) (b : Module.Basis κ K V)
    (h : ∀ i j, b.repr (f i) j ∈ K0) : Submodule.span K0 (Set.range f) = Submodule.span K0 (Set.range b) := by
  haveI : Finite ι := Finite.of_equiv κ (b.indexEquiv f)
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite κ
  haveI : FiniteDimensional K0 (Submodule.span K0 (Set.range b)) := FiniteDimensional.span_of_finite K0 (Set.finite_range b)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (b.mem_span_iff_repr_mem K0 (f i)).2 fun j => ⟨⟨_, h i j⟩, rfl⟩
  · rw [finrank_span_eq_card (f.linearIndependent.restrict_scalars' K0),
      finrank_span_eq_card (b.linearIndependent.restrict_scalars' K0)]
    exact Fintype.card_congr (f.indexEquiv b)

theorem rescale_mem {ι κ : Type} [Finite κ] (K0 : Subfield K) (bS : Module.Basis ι K S) (b : Module.Basis κ K V)
    (e e' : S ≃ₗ[K] V) (h : ∀ i j, b.repr (e (bS i)) j ∈ K0) (h' : ∀ i j, b.repr (e' (bS i)) j ∈ K0) (a : κ) :
    e' (e.symm (b a)) ∈ Submodule.span K0 (Set.range b) := by
  have h1 := rescale_span_eq K0 (bS.map e) b h
  have h2 := rescale_span_eq K0 (bS.map e') b h'
  have h3 : b a ∈ Submodule.span K0 (Set.range (bS.map e)) := h1 ▸ Submodule.subset_span ⟨a, rfl⟩
  rw [← h2]
  generalize b a = x at h3
  induction h3 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subfield.smul_def, map_smul, map_smul]
    exact Submodule.smul_mem _ r hx

theorem rescale_pair [StarRing K] {κ : Type} (b : κ → V) (σ : K →+* ℂ) (c₁ : V →ₛₗ[σ] W)
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pair (b a) (b a')))
    {x y : V} (hx : x ∈ Submodule.span (Formalism.DivisionValues.cmMax K) (Set.range b))
    (hy : y ∈ Submodule.span (Formalism.DivisionValues.cmMax K) (Set.range b)) : inner ℂ (c₁ x) (c₁ y) = σ (pair x y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a', rfl⟩ := hy
      exact hp a a'
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, inner_add_right, hx, hy, map_add, map_add]
    | smul r x _ hx =>
      rw [Subfield.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hx, map_smul, smul_eq_mul, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, inner_add_left, hx, hy, map_add, LinearMap.add_apply, map_add]
  | smul r x _ hx =>
    rw [Subfield.smul_def, LinearMap.map_smulₛₗ, inner_smul_left, hx, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ← r.2 σ]
    rfl

theorem rescale_inj {κ : Type} [Finite κ] (b : Module.Basis κ K V) (σ : K →+* ℂ) (c : V →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun a => c (b a)) : Function.Injective c := by
  haveI := Fintype.ofFinite κ
  refine (injective_iff_map_eq_zero c).2 fun x hx => ?_
  rw [← b.sum_repr x, map_sum] at hx
  simp only [LinearMap.map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h _ hx
  exact b.ext_elem fun a => by simpa using this a

theorem rescale_span_top {κ : Type} [Finite κ] (b : Module.Basis κ K V) (σ : K →+* ℂ) (c : V →ₛₗ[σ] W) (φ : V ≃ₗ[K] V)
    (h : Submodule.span ℂ (Set.range fun a => c (b a)) = ⊤) :
    Submodule.span ℂ (Set.range fun a => c (φ (b a))) = ⊤ := by
  haveI := Fintype.ofFinite κ
  refine top_le_iff.1 (h ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨a, rfl⟩
  have : b a = ∑ k, b.repr (φ.symm (b a)) k • φ (b k) := by
    conv_lhs => rw [← φ.apply_symm_apply (b a), ← b.sum_repr (φ.symm (b a))]
    simp only [map_sum, map_smul]
  change c (b a) ∈ Submodule.span ℂ _
  rw [this, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem rescale_indep {κ : Type} [Finite κ] (u v : κ → W) (hi : LinearIndependent ℂ u)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (hv : Submodule.span ℂ (Set.range v) = ⊤) : LinearIndependent ℂ v := by
  haveI := Fintype.ofFinite κ
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge
    (Module.finrank_eq_card_basis (Module.Basis.mk hi hu.ge)).symm

theorem rescale_abstract [StarRing K] {ι κ : Type} [Finite κ] (bS : Module.Basis ι K S) (b : Module.Basis κ K V)
    (τ σ : K →+* ℂ) (p : S → W) (c0 c0' : V →ₛₗ[τ] W) (pair : V →ₗ⋆[K] V →ₗ[K] K) (q : S → S → K)
    (e e' : S ≃ₗ[K] V) (h : ∀ i j, b.repr (e (bS i)) j ∈ Formalism.DivisionValues.cmMax K)
    (h' : ∀ i j, b.repr (e' (bS i)) j ∈ Formalism.DivisionValues.cmMax K)
    (hc : ∀ x, p x = c0 (e x)) (hc' : ∀ x, p x = c0' (e' x))
    (hq : ∀ x y, pair (e x) (e y) = q x y) (hq' : ∀ x y, pair (e' x) (e' y) = q x y)
    (hi' : LinearIndependent ℂ fun a => c0' (b a)) (c₁ : V →ₛₗ[σ] W')
    (hi : LinearIndependent ℂ fun a => c₁ (b a)) (hs : Submodule.span ℂ (Set.range fun a => c₁ (b a)) = ⊤)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pair (b a) (b a'))) :
    ∃ c₁' : V →ₛₗ[σ] W', (LinearIndependent ℂ fun a => c₁' (b a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁' (b a)) = ⊤ ∧
      (∀ a a', inner ℂ (c₁' (b a)) (c₁' (b a')) = σ (pair (b a) (b a'))) ∧
      (∀ v', ∃ v, c0' v' = c0 v ∧ c₁ v' = c₁' v) ∧
      ∀ (r : V → V) (ρ : W → W) (ρ' : W' → W'), (∀ v, c0 (r v) = ρ (c0 v)) → (∀ v, c0' (r v) = ρ (c0' v)) →
        (∀ v, c₁ (r v) = ρ' (c₁ v)) → ∀ v, c₁' (r v) = ρ' (c₁' v) := by
  have hφ : ∀ v, c0' (e' (e.symm v)) = c0 v := fun v => by rw [← hc', hc, e.apply_symm_apply]
  have hs' := rescale_span_top b σ c₁ (e.symm.trans e') hs
  refine ⟨c₁.comp (e.symm.trans e').toLinearMap, rescale_indep _ _ hi hs hs', hs', fun a a' => ?_, fun v' => ?_,
    fun r ρ ρ' h0 h0' h1 v => ?_⟩
  · refine (rescale_pair b σ c₁ pair hp (rescale_mem _ bS b e e' h h' a) (rescale_mem _ bS b e e' h h' a')).trans ?_
    rw [hq', ← hq, e.apply_symm_apply, e.apply_symm_apply]
  · refine ⟨e (e'.symm v'), ?_, ?_⟩
    · rw [← hφ, e.symm_apply_apply, e'.apply_symm_apply]
    · simp
  · have : e' (e.symm (r v)) = r (e' (e.symm v)) := rescale_inj b τ c0' hi' (by rw [hφ, h0, h0', hφ])
    change c₁ (e' (e.symm (r v))) = ρ' (c₁ (e' (e.symm v)))
    rw [this, h1]

end Abstract

end GlobalTheory.GalLift
