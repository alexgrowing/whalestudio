import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnimodOver

open Module

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_basis (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ V), Submodule.span ℤ (Set.range b) = Λ := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFin _)
  exact ⟨_, b.ofZLatticeBasis ℝ Λ, b.ofZLatticeBasis_span ℝ Λ⟩

theorem discrete_dual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    DiscreteTopology (B.dualSubmodule Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
  infer_instance

theorem discrete_of_le {L M : Submodule ℤ V} [DiscreteTopology M] (h : L ≤ M) :
    DiscreteTopology L :=
  DiscreteTopology.of_continuous_injective (continuous_inclusion h) (Set.inclusion_injective h)

theorem span_of_le {L M : Submodule ℤ V} (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    Submodule.span ℝ (M : Set V) = ⊤ := by
  rw [eq_top_iff, ← hs]
  exact Submodule.span_mono h

theorem exists_nsmul_mem {L M : Submodule ℤ V} [DiscreteTopology M]
    (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, N • x ∈ L := by
  haveI := discrete_of_le h
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ M := ⟨span_of_le hs h⟩
  have hr : finrank ℤ (L.comap M.subtype) = finrank ℤ M := by
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq, ZLattice.rank ℝ L, ZLattice.rank ℝ M]
  haveI hfin : Finite (M ⧸ L.comap M.subtype) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  refine ⟨Nat.card (M ⧸ L.comap M.subtype), Nat.card_pos, fun x hx => ?_⟩
  have h1 := (L.comap M.subtype).toAddSubgroup.nsmul_index_mem ⟨x, hx⟩
  exact h1

theorem exists_selfDual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ M : Submodule ℤ V, Λ ≤ M ∧ M ≤ B.dualSubmodule Λ ∧ B.dualSubmodule M = M := by
  haveI := discrete_dual B hB Λ hs
  set D := B.dualSubmodule Λ with hD
  haveI : IsZLattice ℝ D := ⟨span_of_le hs hint⟩
  haveI : IsNoetherian ℤ D := inferInstance
  have anti : ∀ {L M : Submodule ℤ V}, L ≤ M → B.dualSubmodule M ≤ B.dualSubmodule L :=
    fun h _ hy x hx => hy x (h hx)
  obtain ⟨M, ⟨h1, h2⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2 this)
    {M : Submodule ℤ D | Λ ≤ M.map D.subtype ∧
      M.map D.subtype ≤ B.dualSubmodule (M.map D.subtype)}
    ⟨Λ.comap D.subtype, by
      simp only [Set.mem_setOf_eq, Submodule.map_comap_subtype, inf_eq_right.2 hint]
      exact ⟨le_rfl, hint⟩⟩
  refine ⟨M.map D.subtype, h1, Submodule.map_subtype_le _ _, le_antisymm ?_ h2⟩
  intro w hw
  have hwD : w ∈ D := anti h1 hw
  have hle : M ≤ M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := le_sup_left
  have heq : M = M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := by
    by_contra hne
    refine hmax _ ⟨h1.trans (Submodule.map_mono hle), ?_⟩ (lt_of_le_of_ne hle hne)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
    have e1 := h2 ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
    have e2 := hw _ ⟨y₁, hy₁, rfl⟩
    have e3 := hw _ ⟨x₁, hx₁, rfl⟩
    have e4 : B (x₁ : V) w = - B w (x₁ : V) := (hA.neg_eq _ _).symm
    have e5 : B w w = 0 := hA w
    have e6 : B (D.subtype (x₁ + a • ⟨w, hwD⟩)) (D.subtype (y₁ + c • ⟨w, hwD⟩)) =
        B (D.subtype x₁) (D.subtype y₁) + a • B w (D.subtype y₁) - c • B w (D.subtype x₁) := by
      simp only [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul,
        LinearMap.add_apply, LinearMap.smul_apply, e4, e5, smul_zero, smul_neg, add_zero]
      ring
    rw [e6]
    exact sub_mem (add_mem e1 (Submodule.smul_mem _ _ e2)) (Submodule.smul_mem _ _ e3)
  have : (⟨w, hwD⟩ : D) ∈ M := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact ⟨_, this, rfl⟩

theorem dualSubmoduleToDual_surjective (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  have hbmem : ∀ i, b i ∈ Λ := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  intro φ
  set y : V := ∑ i, (φ ⟨b i, hbmem i⟩ : ℤ) • B.dualBasis hB b i with hy
  have hymem : y ∈ B.dualSubmodule Λ := by
    rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hLI : LinearIndependent ℤ b := b.linearIndependent.restrict_scalars' ℤ
  let bΛ : Module.Basis (Fin n) ℤ Λ := (Module.Basis.span hLI).map (LinearEquiv.ofEq _ _ hb)
  have hbΛ : ∀ i, (bΛ i : V) = b i := fun i => by simp [bΛ, Module.Basis.span_apply]
  refine ⟨⟨y, hymem⟩, bΛ.ext fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  have hspec := LinearMap.BilinForm.dualSubmoduleParing_spec B ⟨y, hymem⟩ (bΛ j)
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hspec
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply, hspec]
  simp only [hbΛ, hy, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    LinearMap.BilinForm.apply_dualBasis_left, smul_ite, smul_zero, zsmul_eq_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 2
  exact Subtype.ext (hbΛ j).symm

theorem exists_unimodular (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ (M : Submodule ℤ V) (N : ℕ) (Ef : LinearMap.BilinForm ℤ M),
      Λ ≤ M ∧ 0 < N ∧ (∀ x ∈ M, N • x ∈ Λ) ∧ DiscreteTopology M ∧
      Submodule.span ℝ (M : Set V) = ⊤ ∧ (∀ a b : M, (Ef a b : ℝ) = B a b) ∧
      Function.Bijective Ef := by
  obtain ⟨M, h1, h2, h3⟩ := exists_selfDual B hB hA Λ hs hint
  haveI := discrete_dual B hB Λ hs
  haveI : DiscreteTopology M := discrete_of_le h2
  have hsM := span_of_le hs h1
  obtain ⟨N, hN, hNM⟩ := exists_nsmul_mem hs h1
  let e := LinearEquiv.ofEq _ _ h3.symm
  refine ⟨M, N, (B.dualSubmoduleToDual M).comp e.toLinearMap, h1, hN, hNM, this, hsM, ?_, ?_⟩
  · intro a b
    exact B.dualSubmoduleParing_spec (e a) b
  · exact Function.Bijective.comp (g := B.dualSubmoduleToDual M) (f := e)
      ⟨B.dualSubmoduleToDual_injective hB M hsM, dualSubmoduleToDual_surjective B hB M hsM⟩
      e.bijective

end General

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun a b w => by simp [add_dotProduct])
    (fun r a w => by simp [smul_dotProduct])
    (fun a b w => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun r a w => by simp [Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := rfl

theorem imForm_isAlt {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) :
    (imForm Hm).IsAlt := by
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, h.eq, ← Matrix.dotProduct_mulVec]
  intro z
  rw [imForm_apply]
  have hq := key (star z)
  rw [star_star] at hq
  exact Complex.conj_eq_iff_im.mp hq

theorem imForm_nondegenerate {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) :
    (imForm Hm).Nondegenerate := by
  have hL : ∀ z : Fin g → ℂ, (∀ w, imForm Hm z w = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz (Complex.I • z)
    rw [imForm_apply, star_smul, Complex.star_def, Complex.conj_I, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 := hp z hne
    simp [Complex.mul_im] at h1
    linarith
  have hR : ∀ w : Fin g → ℂ, (∀ z, imForm Hm z w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hw (Complex.I • w)
    rw [imForm_apply, smul_dotProduct, smul_eq_mul] at h1
    have h2 := hp w hne
    simp [Complex.mul_im] at h1
    linarith
  first
    | exact ⟨hL, hR⟩
    | exact hL

theorem exists_unimodular_overlattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  intro g Λ Hm hd hs hH hp hint
  obtain ⟨M, N, Ef, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_unimodular (imForm Hm) (imForm_nondegenerate hH hp) (imForm_isAlt hH) Λ hs
      (fun x hx y hy => by
        obtain ⟨n, hn⟩ := hint x hx y hy
        exact Submodule.mem_one.2 ⟨n, by rw [imForm_apply, hn]; simp⟩)
  refine ⟨M, N, Ef, h1, h2, fun x hx => ?_, h4, h5, h6, h7⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact h3 x hx

end GlobalTheory.UnimodOver
