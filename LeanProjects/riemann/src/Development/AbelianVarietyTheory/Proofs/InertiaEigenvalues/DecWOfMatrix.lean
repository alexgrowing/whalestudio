import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplRed

open GlobalTheory.WachTensor

private theorem tensorProduct_map_algHom_smul {O A M N : Type} [CommRing O] [CommRing A] [Algebra O A]
    [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : A →ₐ[O] A) (g : M →ₗ[O] N) (r : A) (x : A ⊗[O] M) :
    TensorProduct.map f.toLinearMap g (r • x) = f r • TensorProduct.map f.toLinearMap g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

private theorem coeffs_eq_of_sum_smul_eq_of_span_eq {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (B : Module.Basis (Fin n) R M) (c : Fin n → M) (hc : Submodule.span R (Set.range c) = ⊤)
    {v w : Fin n → R} (hvw : ∑ i, v i • c i = ∑ i, w i • c i) : v = w := by
  have hs : Function.Surjective (Fintype.linearCombination R c) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hc]
  have hi : Function.Injective (B.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R c) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (B.equivFun.surjective.comp hs)
  apply hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply, hvw]

theorem decW_of_matrix (S : Sit) (E : S.Comparison₂)
    (h : ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE),
      (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) →
        ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧
          ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧
      (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) →
        (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) →
          ∀ i, ∃ e, z i = E.ioE e)) : DecW S E := by
  unfold DecW
  intro T
  have memH : ∀ x, x ∈ Htl S T ↔ ∀ g ∈ Hker S, TWact (S.gR g) T g x = x := fun x => Iff.rfl
  have hH : ∀ g ∈ Hker S, S.W.resΓ g = 1 := fun g hg => MonoidHom.mem_ker.1 hg

  by_cases hsub : Subsingleton (TW S.RW T)
  · have key : ∀ x : TW S.RW T, x ∈ LinearMap.range (E.jD T) := fun x => ⟨0, Subsingleton.elim _ _⟩
    exact ⟨fun y _ => ⟨0, (Htl S T).zero_mem, key _⟩, fun z _ _ => key z⟩
  have : Nontrivial (TW S.RW T) := not_subsingleton_iff_nontrivial.1 hsub
  have : Nontrivial S.RW := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact hsub (Module.subsingleton S.RW _)
  have : Nontrivial S.O := RingHom.domain_nontrivial (algebraMap S.O S.RW)
  have : Nontrivial S.W.EE := RingHom.domain_nontrivial E.ioE.toRingHom
  have : Module.Free S.O ↥T.L.T := T.L.free
  have : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg

  have bW : Module.Basis (Fin (Module.finrank S.O ↥T.L.T)) S.RW (TW S.RW T) :=
    (Module.finBasis S.O ↥T.L.T).baseChange S.RW
  have hr : 0 < Module.finrank S.O ↥T.L.T := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (TW S.RW T)
    exact hxy (bW.repr.injective (Finsupp.ext fun i => absurd i.isLt (by omega)))
  have hdr := (S.W.DD_free T).2
  have : Module.Free S.W.EE (S.W.DD T) := (S.W.DD_free T).1
  have : Module.Finite S.W.EE (S.W.DD T) := Module.finite_of_finrank_pos (by rw [hdr]; exact hr)
  obtain ⟨d, ⟨bD⟩, ⟨bW'⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) S.W.EE (S.W.DD T)) ∧
      Nonempty (Module.Basis (Fin d) S.RW (TW S.RW T)) :=
    ⟨_, ⟨Module.finBasis _ _⟩, ⟨bW.reindex (finCongr hdr.symm)⟩⟩

  have hexp : ∀ x : S.W.DD T, E.jD T x = ∑ i, E.ioE (bD.repr x i) • E.jD T (bD i) := by
    intro x
    conv_lhs => rw [← bD.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => E.jD_smul T _ _
  have hspan : Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hexp x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : ∀ v w : Fin d → S.RW, ∑ i, v i • E.jD T (bD i) = ∑ i, w i • E.jD T (bD i) → v = w :=
    fun v w hvw => coeffs_eq_of_sum_smul_eq_of_span_eq bW' _ hspan hvw
  have hsurj : ∀ y : TW S.RW T, ∃ v : Fin d → S.RW, y = ∑ i, v i • E.jD T (bD i) := by
    intro y
    have hy : y ∈ Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun S.RW).1 hy
    exact ⟨v, hv.symm⟩

  have actS : ∀ g (r : S.RW) (x : TW S.RW T),
      TWact (S.gR g) T g (r • x) = S.gR g r • TWact (S.gR g) T g x :=
    fun g r x => tensorProduct_map_algHom_smul (S.gR g) (T.actT g) r x
  have mapS : ∀ (r : S.RW) (x : TW S.RW T), TWmap S.φR T (r • x) = S.φR r • TWmap S.φR T x :=
    fun r x => tensorProduct_map_algHom_smul S.φR LinearMap.id r x
  have hfix : ∀ g ∈ Hker S, ∀ x, TWact (S.gR g) T g (E.jD T x) = E.jD T x := by
    intro g hg x
    rw [← E.jD_act, hH g hg, S.W.γD_one]
  have hact : ∀ g ∈ Hker S, ∀ v : Fin d → S.RW,
      TWact (S.gR g) T g (∑ i, v i • E.jD T (bD i)) = ∑ i, S.gR g (v i) • E.jD T (bD i) := by
    intro g hg v
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [actS, hfix g hg]
  have hinv : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ Htl S T ↔ ∀ i, ∀ g ∈ Hker S, S.gR g (v i) = v i := by
    intro v
    rw [memH]
    constructor
    · intro hv i g hg
      exact congrFun (hinj _ _ ((hact g hg v).symm.trans (hv g hg))) i
    · intro hv g hg
      rw [hact g hg v]
      exact Finset.sum_congr rfl fun i _ => by rw [hv i g hg]
  have hk : ∀ k, TWmap S.φR T (E.jD T (bD k)) =
      ∑ i, E.ioE (bD.repr (S.W.φD T (bD k)) i) • E.jD T (bD i) := fun k => by
    rw [← E.jD_φ]
    exact hexp _
  have hφ : ∀ z : Fin d → S.RW, TWmap S.φR T (∑ k, z k • E.jD T (bD k)) =
      ∑ i, (∑ k, E.ioE (bD.repr (S.W.φD T (bD k)) i) * S.φR (z k)) • E.jD T (bD i) := by
    intro z
    rw [map_sum]
    simp only [mapS, hk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  have hrng : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ LinearMap.range (E.jD T) ↔ ∀ i, ∃ e, v i = E.ioE e := by
    intro v
    constructor
    · rintro ⟨x, hx⟩
      rw [hexp] at hx
      have hv := hinj _ _ hx
      exact fun i => ⟨bD.repr x i, (congrFun hv i).symm⟩
    · intro hv
      choose e he using hv
      refine ⟨∑ i, e i • bD i, ?_⟩
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, he i]

  obtain ⟨h1, h2⟩ := h d (Matrix.of fun i k => bD.repr (S.W.φD T (bD k)) i)
  simp only [Matrix.of_apply] at h1 h2
  refine ⟨fun y hy => ?_, fun z hz hφz => ?_⟩
  · obtain ⟨v, rfl⟩ := hsurj y
    obtain ⟨z, hzH, hz⟩ := h1 v ((hinv v).1 hy)
    refine ⟨∑ i, z i • E.jD T (bD i), (hinv z).2 hzH, ?_⟩
    rw [hφ z, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    exact (hrng _).2 hz
  · obtain ⟨u, rfl⟩ := hsurj z
    have hu := (hinv u).1 hz
    rw [hφ u, ← Finset.sum_sub_distrib] at hφz
    simp only [← sub_smul] at hφz
    exact (hrng u).2 (h2 u hu ((hrng _).1 hφz))

end GlobalTheory.DecomplRed
