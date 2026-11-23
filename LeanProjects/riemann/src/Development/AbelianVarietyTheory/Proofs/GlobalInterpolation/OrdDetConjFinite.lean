import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.OrdDetConj

open GlobalTheory.CharValCompare

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem ordE_mul (P : HeightOneSpectrum (𝓞 E)) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordE P (a * b) = ordE P a + ordE P b := by
  unfold ordE
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]

theorem exists_ordE_star (P : HeightOneSpectrum (𝓞 E)) :
    ∃ m : ℤ, 0 ≤ m ∧ ∀ a : E, a ≠ 0 → ordE (conjPrime₂ P) (star a) = m * ordE P a := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hs0 : (conjPrime₂ P).valuation E (star π) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 hπ0)
  refine ⟨ordE (conjPrime₂ P) (star π), ?_, fun a ha => ?_⟩
  · have h1 : (conjPrime₂ P).valuation E (star π) ≤ 1 := intAt_iff.1 (intAt_star (intAt_iff.2 (by
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)))
    unfold ordE
    rw [neg_nonneg, WithZero.log_le_iff_le_exp hs0]
    exact h1
  · have ha' : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have hsa : (conjPrime₂ P).valuation E (star a) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 ha)
    have h1 : P.valuation E (a * π ^ (WithZero.log (P.valuation E a))) = 1 := by
      rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      conv_lhs => arg 1; rw [← WithZero.exp_log ha']
      rw [← WithZero.exp_add]
      simp
    have h2 := congrArg WithZero.log (val_star_eq_one h1)
    rw [star_mul', star_zpow₀, map_mul, map_zpow₀, WithZero.log_mul hsa (zpow_ne_zero _ hs0), WithZero.log_zpow,
      WithZero.log_one, smul_eq_mul] at h2
    unfold ordE
    linear_combination -h2

theorem ordE_star (P : HeightOneSpectrum (𝓞 E)) {a : E} (ha : a ≠ 0) : ordE (conjPrime₂ P) (star a) = ordE P a := by
  obtain ⟨m, hm, h⟩ := exists_ordE_star P
  obtain ⟨m', hm', h'⟩ := exists_ordE_star (conjPrime₂ P)
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have h1 : ordE P π = 1 := by
    unfold ordE
    rw [hπ, WithZero.log_exp, neg_neg]
  have h2 := h' (star π) (star_ne_zero.2 hπ0)
  rw [conjP_conjP, star_star, h π hπ0, h1, mul_one] at h2
  have h3 : m = 1 := Int.eq_one_of_mul_eq_one_left hm h2.symm
  rw [h a ha, h3, one_mul]

theorem ordDet_conjP {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ordDet (conjPrime₂ P) N = -ordDet P N := by
  obtain ⟨f, hf⟩ := exists_isFr P hN.1
  obtain ⟨f', hf'⟩ := exists_isFr (conjPrime₂ P) hN.1
  have h := val_dual hN hf hf'
  have h0 : star (dt f) ≠ 0 := star_ne_zero.2 (dt_ne _)
  rw [← ordE_eq_zero_iff (mul_ne_zero h0 (dt_ne _)), ordE_mul _ h0 (dt_ne _), ordE_star P (dt_ne _)] at h
  rw [ordDet_eq hf, ordDet_eq hf']
  linear_combination h

theorem finite_pos {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N}.Finite := by
  rcases Set.eq_empty_or_nonempty {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N} with h | ⟨P, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((gen_detI hf).2 _).2 le_rfl)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (zero_mem _)
  have hx0 : s • dt f ≠ 0 := smul_ne_zero hs0 (dt_ne _)
  refine (HeightOneSpectrum.Support.finite (𝓞 E) (s • dt f)⁻¹).subset fun Q hQ => ?_
  obtain ⟨g, hg⟩ := exists_isFr Q hN
  have h1 := ((gen_detI hg).2 _).1 (le_locP Q _ hx)
  have h2 : Q.valuation E (dt g) < 1 := by
    rw [Set.mem_ofPred_eq, ordDet_eq hg, ordE, neg_pos,
      WithZero.log_lt_iff_lt_exp ((Valuation.ne_zero_iff _).2 (dt_ne _))] at hQ
    exact hQ
  show 1 < Q.valuation E (s • dt f)⁻¹
  rw [map_inv₀, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]
  exact h1.trans_lt h2

theorem ordDet_conj_finite : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 E), ordDet (conjPrime₂ P) N = -ordDet P N) ∧ {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite := by
  intro E _ _ _ n N hN
  refine ⟨ordDet_conjP hN, ((finite_pos hN.1).union ((finite_pos hN.1).image conjPrime₂)).subset fun Q hQ => ?_⟩
  rcases lt_or_gt_of_ne hQ with h | h
  · refine Or.inr ⟨conjPrime₂ Q, ?_, conjP_conjP Q⟩
    rw [Set.mem_ofPred_eq, ordDet_conjP hN]
    exact neg_pos.2 h
  · exact Or.inl h

end GlobalTheory.OrdDetConj
