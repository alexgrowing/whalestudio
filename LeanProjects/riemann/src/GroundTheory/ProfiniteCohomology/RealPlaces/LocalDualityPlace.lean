import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDuality
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
import GroundTheory.ProfiniteCohomology.LocalTateDuality.InjectiveCohomologyMapKummerSeqOpenFTwo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global Involution OrderTwo

open scoped NumberField.LiesOver

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (v : InfinitePlace K.1) (hv : v.IsReal)

include hv in

theorem exists_isComplex_infCompletion_algEquiv : ∃ (F : FiniteSubfield) (_ : Fact (K ≤ F))
    (w : v.placesOver F.1), (w : InfinitePlace F.1).IsComplex ∧
      Nonempty ((w : InfinitePlace F.1).Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion) := by
  obtain ⟨F, hF, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  refine ⟨F, hF, w, ?_, ⟨e⟩⟩
  by_contra hw
  have h1 : Module.finrank v.Completion (AlgebraicClosure v.Completion) = 1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact (GroundTheory.Global.InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2
      fun h => hw h.2
  have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure v.Completion)
    (n := 2) (by norm_num)
  have hmem : i ∈ (⊥ : Subalgebra v.Completion (AlgebraicClosure v.Completion)) := by
    rw [hbt]
    exact Algebra.mem_top
  obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hmem
  have hx2 : x ^ 2 = -1 := by
    apply (algebraMap v.Completion (AlgebraicClosure v.Completion)).injective
    rw [map_pow, hx, hi, map_neg, map_one]
  have h := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) hx2
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x)]

include hv in

theorem finrank_infAlgClosure_of_isReal :
    Module.finrank v.Completion (AlgebraicClosure v.Completion) = 2 := by
  obtain ⟨F, _, w, hw, ⟨e⟩⟩ := exists_isComplex_infCompletion_algEquiv v hv
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  rw [← e.toLinearEquiv.finrank_eq]
  exact (GroundTheory.Global.InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace F.1)).2 ⟨hv, hw⟩

include hv in

theorem extensionEmbeddingOfIsReal_norm_pos (y : AlgebraicClosure v.Completion) (hy : y ≠ 0) :
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) := by
  obtain ⟨F, _, w, hw, ⟨e⟩⟩ := exists_isComplex_infCompletion_algEquiv v hv
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have hy' : e.symm y ≠ 0 := (map_ne_zero e.symm).2 hy
  have hn : Algebra.norm v.Completion y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hmem : Units.mk0 _ hn ∈ GroundTheory.Global.InfinitePlace.normSubgroup v (w : InfinitePlace F.1) :=
    ⟨Units.mk0 _ hy', Units.ext (by
      rw [Units.coe_map, Units.val_mk0, Units.val_mk0]
      exact Algebra.norm_eq_of_algEquiv e.symm y)⟩
  exact (GroundTheory.Global.InfinitePlace.mem_normSubgroup_iff hv hw _).1 hmem

include hv in

theorem neg_one_not_mem_range_norm_infAlgClosure :
    (-1 : v.Completion) ∉ Set.range (Algebra.norm v.Completion :
      AlgebraicClosure v.Completion → v.Completion) := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    exact zero_ne_one (neg_eq_zero.1 hy.symm).symm
  have h := extensionEmbeddingOfIsReal_norm_pos v hv y hy0
  rw [hy, map_neg, map_one] at h
  linarith

include hv in
theorem card_realGal_eq_two :
    Fintype.card Gal(AlgebraicClosure v.Completion / v.Completion) = 2 := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, finrank_infAlgClosure_of_isReal v hv]

include hv in
theorem exists_ne_one_gal_infAlgClosure :
    ∃ c : Gal(AlgebraicClosure v.Completion / v.Completion), c ≠ 1 := by
  have h := card_realGal_eq_two v hv
  obtain ⟨c, d, hcd⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
    1 < Fintype.card Gal(AlgebraicClosure v.Completion / v.Completion))
  by_cases hc : c = 1
  · exact ⟨d, fun hd => hcd (hc.trans hd.symm)⟩
  · exact ⟨c, hc⟩

def realConj : Gal(AlgebraicClosure v.Completion / v.Completion) :=
  (exists_ne_one_gal_infAlgClosure v hv).choose

theorem realConj_ne_one : realConj v hv ≠ 1 :=
  (exists_ne_one_gal_infAlgClosure v hv).choose_spec

theorem eq_one_or_eq_realConj (g : Gal(AlgebraicClosure v.Completion / v.Completion)) :
    g = 1 ∨ g = realConj v hv := by
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr (eq_of_ne_one_of_card_eq_two (card_realGal_eq_two v hv) hg
      (realConj_ne_one v hv))

theorem realConj_apply_of_pow_eq_one (u : (AlgebraicClosure v.Completion)ˣ) {k : ℕ} (hk : 0 < k)
    (huk : u ^ k = 1) : realConj v hv (u : AlgebraicClosure v.Completion) = ((u⁻¹ : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) := by
  classical
  have hu0 : (u : AlgebraicClosure v.Completion) ≠ 0 := Units.ne_zero _
  have hprod : algebraMap v.Completion (AlgebraicClosure v.Completion)
      (Algebra.norm v.Completion (u : AlgebraicClosure v.Completion)) =
        (u : AlgebraicClosure v.Completion) * realConj v hv u := by
    rw [Algebra.norm_eq_prod_automorphisms]
    have huniv : (Finset.univ : Finset Gal(AlgebraicClosure v.Completion / v.Completion)) =
        {1, realConj v hv} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact eq_one_or_eq_realConj v hv g
    rw [huniv, Finset.prod_pair (realConj_ne_one v hv).symm, AlgEquiv.one_apply]
  have hr : Algebra.norm v.Completion (u : AlgebraicClosure v.Completion) = 1 := by
    have hpos := extensionEmbeddingOfIsReal_norm_pos v hv u hu0
    have hpow : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        (Algebra.norm v.Completion (u : AlgebraicClosure v.Completion))) ^ k = 1 := by
      rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, huk, Units.val_one, map_one, map_one]
    have h1 := (pow_eq_one_iff_of_nonneg hpos.le hk.ne').1 hpow
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
    rw [h1, map_one]
  rw [hr, map_one] at hprod
  rw [Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_right hprod.symm

theorem realConj_galUnits_of_torsion (ζ : galUnits.{0} v.Completion (AlgebraicClosure v.Completion))
    (hζ : ∃ k : ℕ, 0 < k ∧ k • ζ = 0) :
    (galUnits.{0} v.Completion (AlgebraicClosure v.Completion)).ρ (realConj v hv) ζ = -ζ := by
  obtain ⟨k, hk, hkζ⟩ := hζ
  obtain ⟨u, rfl⟩ : ∃ u : (AlgebraicClosure v.Completion)ˣ,
      (Additive.ofMul u : Additive (AlgebraicClosure v.Completion)ˣ) = ζ :=
    ⟨Additive.toMul (ζ : Additive (AlgebraicClosure v.Completion)ˣ), rfl⟩
  have huk : u ^ k = 1 := by
    change k • (Additive.ofMul u : Additive (AlgebraicClosure v.Completion)ˣ) = 0 at hkζ
    rwa [← ofMul_pow, ofMul_eq_zero] at hkζ
  show Additive.ofMul (galUnitsHom v.Completion (AlgebraicClosure v.Completion) (realConj v hv) u) =
    Additive.ofMul u⁻¹
  congr 1
  apply Units.ext
  rw [coe_galUnitsHom_apply]
  exact realConj_apply_of_pow_eq_one v hv u hk huk

theorem nonempty_addEquiv_galRootsOfUnity_infAlgClosure (k : ℕ) (hk : 0 < k) :
    Nonempty (galRootsOfUnity.{0} v.Completion (AlgebraicClosure v.Completion) k ≃+ ZMod k) :=
  nonempty_addEquiv_galRootsOfUnity (Nat.cast_ne_zero.2 hk.ne')

theorem realInv_eq_placeInv
    (x : cohomology (galUnits.{0} v.Completion (AlgebraicClosure v.Completion)) 2) :
    realInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
        (infAlgClosure_mul_mem_range_norm v) x =
      placeInv (.inl v)
        (cohomologyULiftIntAddEquiv (galUnits.{0} v.Completion (AlgebraicClosure v.Completion)) 2 x) :=
  rfl

end GroundTheory.ProfCoh
