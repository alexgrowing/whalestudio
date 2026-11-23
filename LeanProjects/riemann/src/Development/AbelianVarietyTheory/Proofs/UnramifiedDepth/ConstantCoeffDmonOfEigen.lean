import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CharacterColumns

theorem dof_zero_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (f : PS R 1 d) :
    Dof F 0 f = 0 := by
  simp [Dof]

theorem dmonOf_congr_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u u' : ι → Fin d → R) (mo : ι →₀ ℕ) (hu : ∀ l, mo l ≠ 0 → u l = u' l)
    (f : PS R 1 d) : DmonOf F u mo f = DmonOf F u' mo f := by
  unfold DmonOf
  congr 1
  funext l g
  by_cases hl : mo l = 0
  · rw [hl]; rfl
  · rw [hu l hl]

theorem nabVal_congr_dir {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (w0 : O)
    (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u u' : ι → Fin d → k) (mo : ι →₀ ℕ)
    (hu : ∀ l, mo l ≠ 0 → u l = u' l) :
    B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) =
      B.nabVal k h w0 m f u' (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one,
    dmonOf_congr_dir _ u u' mo hu]

theorem constantCoeff_dmonOf_eigen {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (S : Set ι) (χ : PS R 1 d) (y : ι → R)
    (h1 : constantCoeff χ = 1) (hχ : ∀ l ∈ S, Dof F (u l) χ = C (y l) * χ) (mo : ι →₀ ℕ)
    (hmo : ∀ l, mo l ≠ 0 → l ∈ S) :
    constantCoeff (DmonOf F (S.indicator u) mo χ) = ∏ l, y l ^ mo l := by
  have key := constantCoeff_dmonOf_sub_mem R d F ⊥ ι (S.indicator u) (S.indicator y) χ (by
    intro l mo'
    by_cases hl : l ∈ S
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, hχ l hl, sub_self, map_zero]
      exact Ideal.zero_mem _
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem hl, dof_zero_dir, map_zero, zero_mul,
        sub_self, map_zero]
      exact Ideal.zero_mem _) mo
  rw [Ideal.mem_bot, sub_eq_zero, h1, mul_one] at key
  rw [key]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : mo l = 0
  · rw [hl, pow_zero, pow_zero]
  · rw [Set.indicator_of_mem (hmo l hl)]

end GlobalTheory.CharacterColumns

namespace GlobalTheory

open CharacterColumns

theorem nabVal_character_columns :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  intro COL R _ d O _ _ k _ _ _ B h hh hinj w0 N m n I hN a c hac ι _ u S α hα hβ χ y h1 hχ P hP
  classical
  have hcol : ∀ b, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, (∀ l, mo l ≠ 0 → l ∈ S b) → ∃ s : R,
      s - ∏ l, y (l, b) ^ mo l ∈ I ∧
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
    intro b
    have hz : (fun i => algebraMap R k ((0 : Fin d → R) i)) = 0 := by
      funext i; simp
    obtain ⟨g, hg⟩ := COL R d O k B h hh hinj w0 (a b) (c b) N m I (hac b) hN ι ((S b).indicator u)
      (fun l => if l ∈ S b then α b l else 1)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).1
        · rw [if_neg hl, sub_self]; exact I.zero_mem)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).2.1
        · rw [if_neg hl]; exact isUnit_one)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl, Set.indicator_of_mem hl]; exact (hα b l hl).2.2
        · rw [Set.indicator_of_notMem hl, hz, Matrix.mulVec_zero, smul_zero])
      (by
        intro l l'
        by_cases hl : l ∈ S b
        · by_cases hl' : l' ∈ S b
          · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl']; exact hβ b l hl l' hl'
          · rw [Set.indicator_of_notMem hl', hz, Matrix.mulVec_zero, Matrix.mulVec_zero,
              dotProduct_zero]
            exact zero_mem _
        · rw [Set.indicator_of_notMem hl, hz, zero_dotProduct]
          exact zero_mem _)
      (χ b)
    refine ⟨g, fun mo hmo => ?_⟩
    obtain ⟨r, hr, e⟩ := hg mo
    refine ⟨∏ l, y (l, b) ^ mo l + r, by rwa [add_sub_cancel_left], ?_⟩
    rw [constantCoeff_dmonOf_eigen B.G.F u (S b) (χ b) (fun l => y (l, b)) (h1 b) (hχ b) mo hmo] at e
    rw [← e]
    refine nabVal_congr_dir B h w0 m _ _ _ mo fun l hl => ?_
    rw [Set.indicator_of_mem (hmo l hl)]
  choose g hg using hcol
  have hs : ∀ (mo : ι × Fin n →₀ ℕ) (b : Fin n), ∃ s : R, mo ∈ P.support →
      s - ∏ l, y (l, b) ^ mo (l, b) ∈ I ∧
      B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k s := by
    intro mo b
    by_cases hmo : mo ∈ P.support
    · obtain ⟨s, hs⟩ := hg b (colM mo b) (fun l hl => hP mo hmo l b hl)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h' => absurd h' hmo⟩
  choose s hs using hs
  refine ⟨g, ∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b - MvPolynomial.eval y P, ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo hmo => ?_
    rw [← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b hmo).1
  · rw [add_sub_cancel, map_sum]
    refine Finset.sum_congr rfl fun mo hmo => ?_
    rw [map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => (hs mo b hmo).2

end GlobalTheory
