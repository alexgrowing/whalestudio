import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatUnitProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def IsBddUnit (G : WTZ E) (s t : Rul Xo c) : Prop :=
  Even G.2 ∧ s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw G) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw G) ∧
    GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧
    (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z,
      GlobalTheory.AllWt.homN (U σ) x G s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) x (-G) t z ≤ C) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)

theorem exZ_zero' : Formalism.L2.Pj.exZ Dw (0 : WTZ E) = 0 := by
  funext i; cases i <;> rfl

theorem exZ_add_eq' (G G' : WTZ E) : Formalism.L2.Pj.exZ Dw (G + G') = Formalism.L2.Pj.exZ Dw G + Formalism.L2.Pj.exZ Dw G' :=
  funext fun i => exZ_add _ _ i

theorem exZ_neg_eq' (G : WTZ E) : Formalism.L2.Pj.exZ Dw (-G) = -Formalism.L2.Pj.exZ Dw G := by
  funext i; cases i <;> rfl

theorem homN_idem_le {σ : c.F →+* ℂ} (V : Unf Xo c σ r) {z} (hz : z ∈ framesOn V Z) :
    GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z ≤ 1 := by
  obtain ⟨hd, hl⟩ := hz
  rcases eq_or_ne (GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z) 0 with h | h
  · rw [h]; exact zero_le_one
  · rw [GlobalTheory.FlatLine.homN_idem V x hd hl (GlobalTheory.FlatLine.tested_of_homN_ne V x hd h)]

theorem isBddUnit_zero : IsBddUnit U x Z 0 (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z) := by
  have hm : GlobalTheory.FlatLine.idem Z ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (0 : WTZ E)) := by
    rw [exZ_zero']; exact GlobalTheory.FlatLine.idem_mem_secZ Z
  refine ⟨by simp, hm, by rwa [exZ_zero', neg_zero, ← exZ_zero' (Dw := Dw)], GlobalTheory.FlatLine.idem_mul_idem Z,
    GlobalTheory.FlatLine.idem_mul_idem Z, GlobalTheory.FlatLine.idem_mul_idem Z, fun σ _ => ⟨1, fun z hz => ?_⟩, 1, one_pos,
    fun la v hv => ?_⟩
  · rw [neg_zero]; exact ⟨homN_idem_le x Z (U σ) hz, homN_idem_le x Z (U σ) hz⟩
  · rw [Nat.cast_one, one_smul, GlobalTheory.FlatLine.val_idem hv]; exact ⟨le_rfl, le_rfl⟩

variable {U x Z}

theorem IsBddUnit.mul {G G' : WTZ E} {s t s' t' : Rul Xo c} (h : IsBddUnit U x Z G s t)
    (h' : IsBddUnit U x Z G' s' t') : IsBddUnit U x Z (G + G') (s * s') (t * t') := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  obtain ⟨hG', hs', ht', his', hit', hst', hb', m', hm', hv'⟩ := h'
  refine ⟨hG.add hG', ?_, ?_, by rw [← mul_assoc, his], by rw [← mul_assoc, hit], ?_,
    fun σ hσ => ?_, m * m', Nat.mul_pos hm hm', fun la v hw => ?_⟩
  · rw [exZ_add_eq']; exact GlobalTheory.AllWt.mul_mem_secZ hs hs'
  · rw [exZ_add_eq', neg_add]; exact GlobalTheory.AllWt.mul_mem_secZ ht ht'
  · rw [mul_mul_mul_comm, hst, hst', GlobalTheory.FlatLine.idem_mul_idem]
  · obtain ⟨C, hC⟩ := hb σ hσ
    obtain ⟨C', hC'⟩ := hb' σ hσ
    refine ⟨max C 0 * max C' 0, fun z hz => ⟨?_, ?_⟩⟩
    · rw [GlobalTheory.AllWt.homN_mul (U σ) x hG hG' s s' z hz.1]
      exact mul_le_mul ((hC z hz).1.trans (le_max_left _ _)) ((hC' z hz).1.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
    · rw [neg_add, GlobalTheory.AllWt.homN_mul (U σ) x (G := -G) (G' := -G') hG.neg hG'.neg t t' z hz.1]
      exact mul_le_mul ((hC z hz).2.trans (le_max_left _ _)) ((hC' z hz).2.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
  · have hV := GlobalTheory.FlatLine.isVal_valOn hw
    rw [Nat.cast_mul, ← smul_mul_smul_comm, ← smul_mul_smul_comm, hV.mul, hV.mul]
    exact ⟨add_nonneg (hv la v hw).1 (hv' la v hw).1, add_nonneg (hv la v hw).2 (hv' la v hw).2⟩

theorem IsBddUnit.swap {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) : IsBddUnit U x Z (-G) t s := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  refine ⟨hG.neg, by rwa [exZ_neg_eq'], by rwa [exZ_neg_eq', neg_neg], hit, his,
    by rw [mul_comm, hst], fun σ hσ => ?_, m, hm, fun la v hw => (hv la v hw).symm⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  exact ⟨C, fun z hz => ⟨(hC z hz).2, by rw [neg_neg]; exact (hC z hz).1⟩⟩

theorem exists_nsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (k : ℕ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (k • G) s' t' := by
  induction k with
  | zero => exact ⟨_, _, by rw [zero_nsmul]; exact isBddUnit_zero U x Z⟩
  | succ k ih =>
    obtain ⟨s', t', h'⟩ := ih
    exact ⟨_, _, by rw [succ_nsmul]; exact h'.mul h⟩

theorem exists_zsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (n : ℤ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (n • G) s' t' := by
  cases n with
  | ofNat k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h k
    exact ⟨s', t', by rw [Int.ofNat_eq_natCast, natCast_zsmul]; exact h'⟩
  | negSucc k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h (k + 1)
    exact ⟨t', s', by rw [negSucc_zsmul]; exact h'.swap⟩

theorem exists_sum {ι : Type} (G : ι → WTZ E) (hu : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t)
    (n : ι → ℤ) (S : Finset ι) : ∃ s t : Rul Xo c, IsBddUnit U x Z (∑ i ∈ S, n i • G i) s t := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨_, _, by rw [Finset.sum_empty]; exact isBddUnit_zero U x Z⟩
  | insert a S ha ih =>
    obtain ⟨s, t, h⟩ := ih
    obtain ⟨s₀, t₀, h₀⟩ := hu a
    obtain ⟨s₁, t₁, h₁⟩ := exists_zsmul h₀ (n a)
    exact ⟨_, _, by rw [Finset.sum_insert ha]; exact h₁.mul h⟩

end GlobalTheory.FlatUnitProd

open GlobalTheory.FlatUnitProd in

theorem GlobalTheory.FlatUnitProd.exists_unit_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  intro E _ _ _ H Dw l Xo c r U x Z ι _ G hev hu n
  have hu' : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t := fun i => by
    obtain ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩ := hu i
    exact ⟨s, t, hev i, h1, h2, h3, h4, h5, h6, m, hm, hv⟩
  obtain ⟨s, t, -, h1, h2, h3, h4, h5, h6, m, hm, hv⟩ := exists_sum G hu' n Finset.univ
  exact ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩
