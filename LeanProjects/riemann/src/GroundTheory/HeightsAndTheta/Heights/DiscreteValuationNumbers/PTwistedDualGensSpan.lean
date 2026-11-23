import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensSpan.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    exact ⟨n, by rw [← mul_assoc]; exact mul_mem hn (ht q)⟩

theorem TwistedDualGensSpan.proof : TwistedDualGensSpan.Statement := by
  unfold TwistedDualGensSpan.Statement
  intro R _ Ω _ _ K _ ι y N E _ _ B a M φ hφ c hc
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  obtain ⟨β, hβ⟩ : ∃ β : Module.Basis (Fin N) Ω E, ∀ q, β q = b l0 q :=
    ⟨Module.Basis.mk (hli l0) (hsp l0).ge, fun q => Module.Basis.mk_apply _ _ _⟩
  have key : ∀ q, β.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have hden : ∀ l r, ∃ D ∈ chartRing R (segreVec y) c, D ≠ 0 ∧
        (f l ≠ 0 → D * β.coord q (b l r) ∈ chartRing R (segreVec y) c) := by
      intro l r
      by_cases hl : f l = 0
      · exact ⟨1, one_mem _, one_ne_zero, fun h => (h hl).elim⟩
      obtain ⟨n, hn⟩ := (hiff l (b l r)).2 ⟨Pi.single r 1, fun q' => ⟨0, by
        by_cases h : q' = r
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l0 _).1 ⟨0, by simpa using hn⟩
      obtain ⟨m, hm⟩ := ha' q
      refine ⟨f l0 ^ m * f l ^ n, mul_mem (pow_mem (hf l0) _) (pow_mem (hf l) _),
        mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl), fun _ => ?_⟩
      have hc' : β.coord q (f l ^ n • b l r) = a' q := by
        rw [hrep, show ∑ q, a' q • b l0 q = ∑ q, a' q • β q by simp [hβ],
          Module.Basis.coord_apply, Module.Basis.repr_sum_self]
      have : f l0 ^ m * f l ^ n * β.coord q (b l r) = f l0 ^ m * a' q := by
        rw [← hc', map_smul, smul_eq_mul]; ring
      rw [this]
      exact hm
    choose D hDA hD0 hDc using hden
    set d : Ω := ∏ p : Fin k × Fin N, D p.1 p.2 with hd
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 _ _
    have hdc : ∀ l r, f l ≠ 0 → d * β.coord q (b l r) ∈ chartRing R (segreVec y) c := by
      intro l r hl
      have hsplit := Finset.mul_prod_erase Finset.univ (fun p : Fin k × Fin N => D p.1 p.2)
        (Finset.mem_univ (l, r))
      dsimp only at hsplit
      rw [hd, ← hsplit]
      have : D l r * (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * β.coord q (b l r) =
          (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * (D l r * β.coord q (b l r)) := by ring
      rw [this]
      exact mul_mem (prod_mem fun p _ => hDA _ _) (hDc l r hl)
    have hψ : ∀ v ∈ B.lat c, (d • β.coord q) v ∈ chartRing R (segreVec y) c := by
      intro v hv
      rw [LinearMap.smul_apply, smul_eq_mul]
      refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
      intro l
      by_cases hl : f l = 0
      · exact ⟨1, by simp [hl]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
      obtain ⟨n, hn⟩ := TwistedDualGensSpan.sum_mul_mem_localized _ (hf l) a'
        (fun r => d * β.coord q (b l r)) ha' (fun r => hdc l r hl)
      refine ⟨n, ?_⟩
      have : d * β.coord q v = ∑ r, a' r * (d * β.coord q (b l r)) := by
        rw [hrep, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, smul_eq_mul]; ring
      rw [smul_eq_mul, this]
      exact hn
    obtain ⟨u, -, hu⟩ := hφ.generate c hc (d • β.coord q) hψ
    have hmem : d • β.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have : β.coord q = d⁻¹ • (d • β.coord q) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  rw [eq_top_iff, ← β.dualBasis.span_eq, Module.Basis.coe_dualBasis]
  exact Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact key q)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
