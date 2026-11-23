import Formalism.TruncatedSeriesCounting.LemmaDetPoly
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

open Formalism.NG Formalism.NG.QuotientPowerLengths Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Module IsDiscreteValuationRing

noncomputable section

universe u v w

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.EtaCongruenceSeparation

section
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type*} [Finite X]
  {T : Subalgebra O (X → O)} {V : Type*} [AddCommGroup V] [Module (FractionRing O) V]
  [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
  {act : T →+* Module.End (FractionRing O) V}

lemma exists_sep (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Set X) :
    ∃ u ∈ T, (∀ x ∈ S, u x = 0) ∧ ∀ y ∉ S, u y ≠ 0 := by
  classical
  have := Fintype.ofFinite X
  choose f hfT hf using hs
  let F : X → X → (X → O) := fun y x =>
    if h : y = x then 1 else f y x h - algebraMap O (X → O) (f y x h x)
  have hFT : ∀ y x, F y x ∈ T := by
    intro y x
    simp only [F]
    split_ifs with h
    · exact one_mem _
    · exact sub_mem (hfT y x h) (T.algebraMap_mem _)
  let e : X → (X → O) := fun y => ∏ x, F y x
  have heT : ∀ y, e y ∈ T := fun y => prod_mem fun x _ => hFT y x
  have he_self : ∀ y, e y y ≠ 0 := by
    intro y
    simp only [e, Finset.prod_apply]
    rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [F]
    split_ifs with h
    · simp
    · simp only [Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact sub_ne_zero.mpr (fun h' => hf y x h h')
  have he_other : ∀ y z, y ≠ z → e y z = 0 := by
    intro y z hyz
    simp only [e, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ z) ?_
    simp only [F, dif_neg hyz, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  refine ⟨∑ y ∈ Finset.univ.filter (· ∉ S), e y, sum_mem fun y _ => heT y, ?_, ?_⟩
  · intro x hx
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun y hy => he_other y x ?_
    rintro rfl
    exact (Finset.mem_filter.mp hy).2 hx
  · intro y hy
    rw [Finset.sum_apply, Finset.sum_eq_single y]
    · exact he_self y
    · intro b _ hb
      exact he_other b y hb
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩) h

lemma disj (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Set X) :
    Disjoint (VS T act S) (VS T act Sᶜ) := by
  obtain ⟨u, hu, hu0, hu1⟩ := exists_sep hs S
  let g : Module.End (FractionRing O) V := act ⟨u, hu⟩
  have hV : ∀ x, Vx T act x ≤ Module.End.eigenspace g (algebraMap O (FractionRing O) (u x)) := by
    intro x v hv
    rw [Module.End.mem_eigenspace_iff]
    rw [mem_Vx.mp hv ⟨u, hu⟩, algebraMap_smul]
  have h1 : VS T act S ≤ Module.End.eigenspace g 0 := by
    refine iSup₂_le fun x hx => ?_
    have := hV x
    rwa [hu0 x hx, map_zero] at this
  have h2 : VS T act Sᶜ ≤ ⨆ μ ∈ ({0}ᶜ : Set (FractionRing O)), Module.End.eigenspace g μ := by
    refine iSup₂_le fun x hx => (hV x).trans ?_
    refine le_iSup₂ (f := fun μ (_ : μ ∈ ({0}ᶜ : Set (FractionRing O))) => Module.End.eigenspace g μ)
      _ ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr (hu1 x hx)
  exact ((Module.End.eigenspaces_iSupIndep g).disjoint_biSup (by simp)).mono h1 h2

end

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.EtaCongruenceSeparation

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
