import Formalism.SharpRestriction.LevelLetterCocycles.StatementOfDegreeAndBound
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks (K : FinExt l) {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

theorem sqrt_notMem (y : Om l) (hy : y ^ 2 = -(l : Om l)) : y ∉ MaximalUnramifiedExtension l := by
  intro h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
    rw [e]
    exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
  have h0 : y ≠ 0 := by
    rintro rfl
    have : (l : Om l) = 0 := by simpa using hy.symm
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  obtain ⟨k, hk⟩ := norm_Kur_zpow h h0
  have h2 : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hy, norm_neg, hn]
  have h3 : (l : ℝ) ^ (k * 2) = (l : ℝ) ^ (-1 : ℤ) := by
    rw [zpow_mul, ← hk, zpow_neg_one, ← h2]; norm_cast
  have := zpow_right_injective₀ hl0 hl1.ne' h3
  omega

theorem deg_two (K : FinExt l) (y : Om l) (hy : y ^ 2 = -(l : Om l))
    (hK : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y}) :
    finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) * 2 := by
  have hint : IsIntegral (K0 K) y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have h1 : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y}) :=
    congrArg (fun F : IntermediateField ℚ_[l] (Om l) => finrank ℚ_[l] ↥F) hK
  rw [h1, finrank_sup_adjoin]
  congr 1
  have hle : (minpoly (K0 K) y).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 + Polynomial.C (l : ↥(K0 K))).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
    have hd : (Polynomial.X ^ 2 + Polynomial.C (l : ↥(K0 K))).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
    rw [← hd]
    refine Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ ?_) hm.ne_zero
    simp [hy]
  have hne : (minpoly (K0 K) y).natDegree ≠ 1 := by
    rw [Ne, minpoly.natDegree_eq_one_iff]
    rintro ⟨c, hc⟩
    exact sqrt_notMem y hy (hc ▸ c.2.2)
  have := minpoly.natDegree_pos hint
  omega

theorem preamble_degree_clauses (D : D7) : Formalism.MainNotions.EmbeddingTypeJumps.DegreeClauses D := by
  intro i hl w hw
  obtain ⟨⟨y, hy, hK⟩, -⟩ := Formalism.MainNotions.EmbeddingTypeJumps.preamble_first_clauses D i hl w hw
  have h2 := deg_two _ y hy hK
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos (D.nbr i w hw).Kw
  have ht := Module.finrank_mul_finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1
  have hodd : D.nd.l i % 2 = 1 := by
    obtain ⟨-, -, h3, h7, -⟩ := D.host.hyp
    rcases hl with h | h <;> rw [h] <;> omega
  refine ⟨Nat.eq_of_mul_eq_mul_left hp (ht.trans h2), ?_⟩
  rw [finrank_Ks _ one_pos, h2]
  obtain ⟨k, hk⟩ : ∃ k, D.nd.l i - 1 = 2 * k := ⟨(D.nd.l i - 1) / 2, by omega⟩
  rw [hk, Nat.mul_div_cancel_left _ two_pos]
  simp only [Nat.sub_self, pow_zero]
  ring

theorem scaled_lattice_nonzero_holds (D : D7) : Formalism.MainNotions.EmbeddingTypeJumps.Conclusion0 D := Formalism.MainNotions.EmbeddingTypeJumps.preamble_of_degree_clauses D (preamble_degree_clauses D)

theorem vdeg (K : FinExt l) {m : ℕ} (hm : 0 < m) :
    padicValNat l (finrank ℚ_[l] ↥(Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Ks K 1)) = m - 1 := by
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have h1 : 0 < l - 1 := by have := (Fact.out : l.Prime).one_lt; omega
  have e : finrank ℚ_[l] ↥(Ks K m) = l ^ (m - 1) * finrank ℚ_[l] ↥(Ks K 1) := by
    rw [finrank_Ks K hm, finrank_Ks K one_pos]; simp only [Nat.sub_self, pow_zero]; ring
  have h0 : finrank ℚ_[l] ↥(Ks K 1) ≠ 0 := by
    rw [finrank_Ks K one_pos]
    exact Nat.mul_ne_zero hp.ne' (Nat.mul_ne_zero (pow_pos (Fact.out : l.Prime).pos _).ne' h1.ne')
  rw [e, padicValNat.mul (pow_pos (Fact.out : l.Prime).pos _).ne' h0, padicValNat.prime_pow]
  omega

theorem gK_zero (K : FinExt l) (h2 : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) * 2) :
    padicValNat l (finrank ℚ_[l] ↥(Ks K 1)) - padicValNat l (finrank ℚ_[l] ↥K.1) = 0 := by
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have hl := (Fact.out : l.Prime).one_lt
  have h1 : padicValNat l (l - 1) = 0 := padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  rw [finrank_Ks K one_pos, h2]
  simp only [Nat.sub_self, pow_zero, one_mul]
  rw [padicValNat.mul hp.ne' (by omega), padicValNat.mul hp.ne' (by omega), h1]
  omega

end Formalism.MainNotions.N.PreambleDegrees
