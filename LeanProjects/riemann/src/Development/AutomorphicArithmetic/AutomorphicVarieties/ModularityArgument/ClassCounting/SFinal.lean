import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.CardAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.PrimeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumFin
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EmultiplicityPowSubOneOdd

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

private theorem sf_card (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    refine ⟨0, Module.length_eq_zero, ?_⟩
    haveI := uniqueOfSubsingleton (0 : M')
    simp
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule ℤ_[l] (M ⧸ N)›
    rw [IsLocalRing.eq_maximalIdeal hm] at e
    have hq : Nat.card (M ⧸ N) = l := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr PadicInt.residueField.toEquiv).trans (Nat.card_zmod l)
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      push_cast
      rfl
    · have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
      rw [h2]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [hq, hc, pow_succ, mul_comm]

open KStar.TotallyRealRoots in
private theorem sf_nu {l : ℕ} [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (h0 : U.index ≠ 0) {e : ℕ} (he : e ≠ 0) :
    nu l U e ≤ ((2 + padicValNat l U.index + padicValNat l e : ℕ) : ℕ∞) := by
  have hp : Prime (l : ℤ_[l]) := PadicInt.prime_p
  have hunit : IsUnit (1 + (l : ℤ_[l]) ^ 2) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((l : ℤ_[l]) ^ 2)‖ < 1 := by
      rw [norm_pow, PadicInt.norm_p]
      have h2 : (1:ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      have h3 : (0:ℝ) < (l:ℝ)⁻¹ := by positivity
      have h4 : (l:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [PadicInt.norm_add_eq_max_of_ne] <;> simp_all [ne_of_gt, le_of_lt]
  have hmem : hunit.unit ^ U.index ∈ U := U.pow_index_mem hunit.unit
  by_contra hcon
  push_neg at hcon
  have hle : (((2 + padicValNat l U.index + padicValNat l e + 1 : ℕ)) : ℕ∞) ≤ nu l U e := by
    have := Order.add_one_le_of_lt hcon
    exact_mod_cast this
  have hdvd := (KStar.TotallyRealRoots.le_nu_iff.1 hle) _ hmem
  have hw : ((hunit.unit ^ U.index : ℤ_[l]ˣ) : ℤ_[l]) ^ e = (1 + (l:ℤ_[l]) ^ 2) ^ (U.index * e) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_mul]
  rw [hw] at hdvd
  have hm := KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq (l := l) (u := 1 + (l:ℤ_[l]) ^ 2) (by simp) (U.index * e)
  rw [add_sub_cancel_left, emultiplicity_pow_self hp.ne_zero hp.not_unit,
    ← padicValNat_eq_emultiplicity (Nat.mul_ne_zero h0 he), padicValNat.mul h0 he] at hm
  have h5 := (pow_dvd_iff_le_emultiplicity).1 hdvd
  rw [hm] at h5
  norm_cast at h5
  omega

private theorem sf_loc {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (D : LData L Ω l) {e : ℕ} (he : e ≠ 0) :
    sumLocalH0TwistLength D e ≤ ((Module.finrank ℚ L * (2 + Nat.log l (Module.finrank ℚ L) + e) : ℕ) : ℕ∞) := by
  rw [LDataCardLeFinrank.local_H0_length_eq_sum]
  set n := Module.finrank ℚ L with hn
  have hv : ∀ v : D.S, KStar.TotallyRealRoots.nu l (LDataCardLeFinrank.decImage L l (D.A v)) ((e : ℤ).natAbs) ≤
      ((2 + Nat.log l n + e : ℕ) : ℕ∞) := by
    intro v
    obtain ⟨_, hi0, hin⟩ := LDataCardLeFinrank.ineOpen L Ω l v (D.A v) (LDataCardLeFinrank.above_of_mem D v) (D.hA v)
    have hdvd : (LDataCardLeFinrank.decImage L l (D.A v)).index ∣ (LDataCardLeFinrank.ineImage L l (D.A v)).index :=
      Subgroup.index_dvd_of_le (LDataCardLeFinrank.ineImage_le_decImage L l (D.A v))
    have hd0 : (LDataCardLeFinrank.decImage L l (D.A v)).index ≠ 0 := by
      intro h
      rw [h] at hdvd
      exact hi0 (Nat.eq_zero_of_zero_dvd hdvd)
    have hdn : (LDataCardLeFinrank.decImage L l (D.A v)).index ≤ n :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd) hin
    have hne : (e : ℤ).natAbs ≠ 0 := by simpa using he
    refine le_trans (sf_nu _ hd0 hne) ?_
    have a1 : padicValNat l (LDataCardLeFinrank.decImage L l (D.A v)).index ≤ Nat.log l n :=
      le_trans (padicValNat_le_nat_log _) (Nat.log_mono_right hdn)
    have a2 : padicValNat l e ≤ e := by
      have hp := (Fact.out : l.Prime)
      have b1 : l ^ padicValNat l e ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) pow_padicValNat_dvd
      have b2 : padicValNat l e < l ^ padicValNat l e := Nat.lt_pow_self hp.one_lt
      omega
    have hea : (e : ℤ).natAbs = e := rfl
    rw [hea]
    exact_mod_cast (by omega : 2 + padicValNat l (LDataCardLeFinrank.decImage L l (D.A v)).index + padicValNat l e ≤
      2 + Nat.log l n + e)
  calc _ ≤ ∑ _v : D.S, ((2 + Nat.log l n + e : ℕ) : ℕ∞) := Finset.sum_le_sum fun v _ => hv v
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, ← Nat.cast_mul]
      exact_mod_cast Nat.mul_le_mul_right _ (LDataCardLeFinrank.cardAbove L Ω l D)

theorem UpperTheory.V.ZK.sFinal :
    UpperTheory.V.ZK.SFinal := by
  rw [SFinal.eq_1]
  rintro hPT hLF hLTD ⟨C, hC⟩
  obtain ⟨CK, _, hCK⟩ := K.numFin C
  refine ⟨CK, ?_⟩
  rw [LemmaK.eq_1]
  intro l _ L Ω _ _ _ _ _ D htc hmu e he
  rw [ShaK.eq_1] at hC
  obtain ⟨s, hs, hslog⟩ := hC l L htc hmu e he
  set n := Module.finrank ℚ L with hn
  have hV := LDataCardLeFinrank.VLen_le_shaLen_add hPT hLF hLTD (LDataCardLeFinrank.ptCase_of_isTotallyComplex L l) D (e : ℤ)
  rw [VLen.eq_1, LDataCardLeFinrank.shaLen_eq_shaInv, hs] at hV
  have hloc := sf_loc D (e := e) (by omega)
  have hlen : Module.length ℤ_[l] (H2 (zlTw D ((e : ℤ) + 1))) ≤ ((s + n * (2 + Nat.log l n + e) : ℕ) : ℕ∞) := by
    rw [Nat.cast_add]
    rw [← hn] at hloc
    exact le_trans hV (add_le_add le_rfl hloc)
  have hfl : IsFiniteLength ℤ_[l] (H2 (zlTw D ((e : ℤ) + 1))) := by
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  obtain ⟨k, hk, hcard⟩ := sf_card l _ hfl
  have hkK : k ≤ s + n * (2 + Nat.log l n + e) := by
    rw [hk] at hlen
    exact_mod_cast hlen
  have hfin : Finite (H2 (zlTw D ((e : ℤ) + 1))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  refine ⟨hfin, ?_⟩
  rw [hcard, Nat.cast_pow, Real.log_pow]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1.le
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hD1 : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (discr_ne_zero L)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hDR : (1 : ℝ) ≤ (discr L).natAbs := by exact_mod_cast hD1
  have hln : (l : ℝ) ≤ n + 1 := by exact_mod_cast K.primeLe l L hmu
  have hX : Real.log l ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) hln
  have hX0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLog : (Nat.log l n : ℝ) * Real.log l ≤ Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_pow]
    have hpl : ((l : ℝ) ^ Nat.log l n) ≤ n := by exact_mod_cast Nat.pow_log_le_self l (by omega)
    exact Real.log_le_log (by positivity) (by linarith)
  have hY : 1 / 2 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := by
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 2 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hnum := hCK e n (discr L).natAbs he hn1 hD1
  have hk' : (k : ℝ) ≤ s + n * (2 + Nat.log l n + e) := by exact_mod_cast hkK
  have e1 : (k : ℝ) * Real.log l ≤ (s + n * (2 + Nat.log l n + e)) * Real.log l :=
    mul_le_mul_of_nonneg_right hk' hlogl
  have e2 : (n : ℝ) * (2 + e) * Real.log l ≤ n * (2 + e) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have e3 : (n : ℝ) * ((Nat.log l n : ℝ) * Real.log l) ≤ n * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hLog (by positivity)
  have hcoef : (3 + e : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ)) := by
    have q1 : (3 + e : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * (1 / 2) := by nlinarith
    have q2 : 4 * (2 * e * (2 * e + 3)) * (1 / 2 : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    linarith
  have e4 : (n : ℝ) * (3 + e) * Real.log ((n : ℝ) + 1) ≤
      n * (4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ))) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity)) hX0
  linarith [e1, e2, e3, e4, hnum, hslog]
