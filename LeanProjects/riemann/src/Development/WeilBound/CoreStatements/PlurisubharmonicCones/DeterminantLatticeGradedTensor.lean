import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt

open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem gen_ratio {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    s / t ∈ regAt ξ p := by
  have : s ∈ Submodule.span (regAt ξ p) {t} := by rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have : s / t = a := by rw [← ha, div_eq_iff ht.1]; rfl
  rw [this]; exact a.2

theorem tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  have h0 : ∏ i, s i ^ a i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs i).1
  refine ⟨h0, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2
    (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨s, hs, rfl⟩)))⟩
  rintro _ ⟨s', hs', rfl⟩
  have hm : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p := by
    refine prod_mem fun i _ => ?_
    rcases Int.eq_nat_or_neg (a i) with ⟨n, h | h⟩
    · rw [h, zpow_natCast]; exact pow_mem (gen_ratio (hs' i) (hs i)) n
    · rw [h, _root_.zpow_neg, ← _root_.inv_zpow, inv_div, zpow_natCast]; exact pow_mem (gen_ratio (hs i) (hs' i)) n
  refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
  show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = _
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]

end

end N1

open N1

theorem determinant_lattice_graded_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  intro X Ω _ ξ V _ _ L r b₀ h₀ hL
  funext p
  obtain ⟨U, hU, b, hfl, hb⟩ := hL p trivial
  replace hb := hb p trivial hU
  have hmem : ∀ k : Fin r, ∃ c : Fin r → Ω, (∀ k', k < k' → c k' = 0) ∧ b k = ∑ k', c k' • b₀ k' := by
    intro k
    have h1 : b k ∈ flagStep Ω b₀ (k + 1) := by
      rw [← hfl]; exact Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
    obtain ⟨c, hc, e⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨c, fun k' h => (Finsupp.mem_supported' Ω c).1 hc k' (by simp only [Set.mem_ofPred_eq, not_lt]; exact h), ?_⟩
    rw [← e, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  choose c hc0 hc using hmem
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun k' k => c k k'
  have hT : T.BlockTriangular id := fun k' k h => hc0 k k' h
  have h1 := determinant_lattice_generator X Ω ξ V L r b₀ b T p h₀ hb hc
  have h2 : ∀ i, (L.gr b₀ i).IsGenAt p (T i i) := fun i => by
    refine FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ b p i _ h₀ hfl hb ?_
    rw [hc i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    show c i i • b₀ i + _ - c i i • b₀ i ∈ _
    rw [add_sub_cancel_left]
    refine Submodule.sum_mem _ fun k' hk' => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk') with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k', h, rfl⟩)
    · rw [hc0 i k' h, zero_smul]; exact Submodule.zero_mem _
  have h3 := tens_gen (Λ := fun i => L.gr b₀ i) (fun _ => 1) h2
  rw [h1.2, h3.2, Matrix.det_of_isUpperTriangular hT]
  simp

end LevelTowerAlt
