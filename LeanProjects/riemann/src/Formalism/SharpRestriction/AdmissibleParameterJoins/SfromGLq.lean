import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLp
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLe

noncomputable section

namespace Formalism.MainNotions.J

open Finset NumberField IsDedekindDomain Formalism.BasicNotions

theorem card_GL_real (g n : ℕ) [Fact g.Prime] :
    (Nat.card (GL (Fin n) (ZMod g)) : ℝ) = LocalBesselAndTopKernel.cardGL (g : ℝ) n := by
  rw [Matrix.card_GL_field, ZMod.card]
  unfold LocalBesselAndTopKernel.cardGL
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((g ^ n - g ^ i : ℕ) : ℝ)) n]
  refine prod_congr rfl fun i hi => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : g.Prime).pos (le_of_lt (mem_range.mp hi)))]
  push_cast
  rfl

theorem cardGL_factor (q : ℝ) (k : ℕ) :
    LocalBesselAndTopKernel.cardGL q k = q ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1) := by
  unfold LocalBesselAndTopKernel.cardGL
  have h1 : ∀ i ∈ range k, q ^ k - q ^ i = q ^ i * (q ^ (k - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := mem_range.mp hi
    have : k = i + (k - 1 - i + 1) := by omega
    conv_lhs => rw [this, pow_add]
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id,
    prod_range_reflect (fun j => q ^ (j + 1) - 1) k]
  congr 1
  rw [range_eq_Ico, prod_Ico_add' (fun j => q ^ j - 1) 0 k 1]
  refine prod_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

theorem idxColLoc_eq (g k : ℕ) [Fact g.Prime] :
    StandardLattice.idxColLoc g k = ∏ i ∈ Finset.Icc 1 k, ((g : ℝ) ^ i - 1) := by
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  have hc : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      g ^ (k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin k) (ZMod g) =>
      isUnitri_iff (A : Matrix (Fin k) (Fin k) (ZMod g))), card_pat _ (by simp [upS]), card_upS, Nat.card_zmod]
  have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  rw [card_GL_real, hc, cardGL_factor, Nat.cast_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hg)]

theorem dim_arith (k r c : ℕ) (h : c + k = (k + 2 * r + 1) * (k + 2 * r + 1 - 1) / 2) :
    c = r * (2 * k + 2 * r + 1) + k * (k - 1) / 2 := by
  rcases k with _ | k
  · have e : (0 + 2 * r + 1) * (0 + 2 * r + 1 - 1) = 2 * (r * (2 * 0 + 2 * r + 1)) + 0 := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega
  · have e : (k + 1 + 2 * r + 1) * (k + 1 + 2 * r + 1 - 1) =
        2 * (r * (2 * (k + 1) + 2 * r + 1) + (k + 1)) + (k + 1) * (k + 1 - 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega

theorem idxRowLoc_eq (g k m : ℕ) [Fact g.Prime] (hm : Even m) (h2 : 2 ≤ m) :
    StandardLattice.idxRowLoc g k m = LocalBesselAndTopKernel.cardGL (g : ℝ) (k + m - 1) /
      ((g : ℝ) ^ ((m / 2 - 1) * (2 * k + 2 * (m / 2 - 1) + 1)) * (g : ℝ) ^ (k * (k - 1) / 2)) := by
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  obtain ⟨a, rfl⟩ := hm
  have ha : (a + a) / 2 - 1 = a - 1 := by omega
  have hn : k + (a + a) - 1 = k + 2 * (a - 1) + 1 := by omega
  have hc : Nat.card {A : GL (Fin (k + (a + a) - 1)) (ZMod g) //
      StandardLattice.IsRowLev k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))} =
      g ^ (((a + a) / 2 - 1) * (2 * k + 2 * ((a + a) / 2 - 1) + 1) + k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin (k + (a + a) - 1)) (ZMod g) =>
      isRowLev_iff k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))),
      card_pat _ (by simp only [rowS, upS, mem_filter, mem_univ, true_and]; exact fun p hp => hp.1), Nat.card_zmod]
    congr 1
    have h := card_rowS k ((a + a) / 2 - 1) (k + (a + a) - 1) (by omega)
    rw [ha] at h ⊢
    rw [hn] at h ⊢
    exact dim_arith k (a - 1) _ h
  rw [card_GL_real, hc, Nat.cast_pow, pow_add]

theorem finprod_typed (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) (φ : ℕ → ℝ) :
    ∏ᶠ p ∈ S.typedPl D, φ (Ideal.absNorm p.asIdeal) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  have hf : D.R.f ≠ 0 := by
    unfold Ranks.f Ranks.n
    positivity
  have hfin : ∀ i, ({p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}).Finite := by
    intro i
    have hc := (h i).1
    have hF : Finite {p : HeightOneSpectrum (𝓞 D.host.F) // ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact hf)
    exact Set.finite_coe_iff.mp hF
  have hone : ∀ i, ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal) = φ (D.host.g i) ^ D.R.f := by
    intro i
    have e : ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
        φ (Ideal.absNorm p.asIdeal) =
        ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
          φ (D.host.g i) :=
      finprod_mem_congr rfl fun p hp => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, (h i).2 p hp]
    rw [e, finprod_mem_eq_finite_toFinset_prod _ (hfin i), Finset.prod_const,
      ← Set.ncard_eq_toFinset_card _ (hfin i), ← Nat.card_coe_set_eq]
    exact congrArg _ (h i).1
  have hdis : Disjoint {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := by
    refine Set.disjoint_left.mpr fun p h0 h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' : (a : 𝓞 D.host.F) * ((D.host.g 0 : ℕ) : 𝓞 D.host.F) + (b : 𝓞 D.host.F) * ((D.host.g 1 : ℕ) : 𝓞 D.host.F) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.F) hab
    rw [← hab']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hU : S.typedPl D = {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} ∪
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := rfl
  rw [hU, finprod_mem_union hdis (hfin 0) (hfin 1), hone 0, hone 1]

theorem idxColTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxColTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxColTie StandardLattice.idxPi S.gaG
  rw [finprod_typed D h (fun N => ∏ i ∈ Finset.Icc 1 D.R.k, ((N : ℝ) ^ i - 1)), idxColLoc_eq, idxColLoc_eq]

theorem idxRowTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxRowTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxRowTie StandardLattice.idxSig LocalBesselAndTopKernel.idxRows
  rw [finprod_typed D h (fun N => LocalBesselAndTopKernel.cardGL (N : ℝ) D.R.r /
    ((N : ℝ) ^ LocalBesselAndTopKernel.dimNS D * (N : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))),
    idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m, idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m]
  rfl

theorem column_row_ranks_of_columns (D : D7) (Lv : LevelData D) (h4 : StandardLattice.Conclusion4f D Lv) (h2 : StandardLattice.VolumeEqMass₂ D)
    (hD : StandardLattice.FactDstar D) (hc : ColHyp D) : LocalBesselAndTopKernel.FamilyMidVolume D :=
  column_row_ranks D Lv h4 h2 hD hc (idxColTie_of D hc.2.1) (idxRowTie_of D hc.2.1)

theorem family_column_row_ranks_of_columns {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 Cg cb Cu cT CT : ℝ)
    (h : S.OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      (∃ Lv : LevelData (Fm.D x i), StandardLattice.Conclusion4f (Fm.D x i) Lv) ∧ StandardLattice.VolumeEqMass₂ (Fm.D x i) ∧ StandardLattice.FactDstar (Fm.D x i) ∧
        ColHyp (Fm.D x i)) :
    LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT := by
  refine family_column_row_ranks Fm C0 Cg cb Cu cT CT (S.OwnEv.mono (fun C' Cl x i hxi hh => ?_) h)
  obtain ⟨h4, h2, hD, hc⟩ := hxi hh
  exact ⟨h4, h2, hD, hc, idxColTie_of _ hc.2.1, idxRowTie_of _ hc.2.1⟩

end Formalism.MainNotions.J

end
