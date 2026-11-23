import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.JacobianTransformationLaw

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section PhiFacts

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem fPos_lt' {k₀ c n l : ℕ} (_hk : k₀ ≤ n) (hl : l < n + c) : fPos k₀ c n l < n + c := by
  unfold fPos
  split_ifs <;> omega

theorem fIdx_fPos' {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : fIdx k₀ c n (fPos k₀ c n l) = l := by
  unfold fIdx fPos
  split_ifs <;> omega

theorem eN_out {N s : ℕ} (hs : ¬ s < N) : eN E N s = 0 := by
  funext l
  have hl := l.isLt
  simp only [eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem entB_add' {N' N : ℕ} (q k₀ c' n' c n : ℕ) (x y : HomE E N' N) (p p' : ℕ) :
    entB q k₀ c' n' c n 0 0 (x + y) p p' = entB q k₀ c' n' c n 0 0 x p p' + entB q k₀ c' n' c n 0 0 y p p' := by
  unfold entB atN
  split_ifs <;> simp [add_mul]

theorem unitV_congr' (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) :
    unitV ξ a = unitV ξ b := by
  unfold unitV
  by_cases ha : IsUnit (redP P a)
  · have hb : IsUnit (redP P b) := h ▸ ha
    rw [dif_pos ha, dif_pos hb, show ha.unit = hb.unit from Units.ext h]
  · rw [dif_neg ha, dif_neg (h ▸ ha)]

theorem aym_det_zero (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) (hr : n + c < r ∨ n' + c' < r) :
    (AYm q k₀ r c' n' c n x).det = 0 := by
  have hq : ∀ a b : ℕ, entB q k₀ c' n' c n 0 0 x a b
      = atN (x (eN E (n' + c') (fIdx k₀ c' n' b))) (fIdx k₀ c n a) := by
    intro a b
    simp [entB, scE]
  rcases hr with hr | hr
  · by_cases hz : ∃ s : Fin r, n + c ≤ fIdx k₀ c n s.1
    · obtain ⟨s, hs⟩ := hz
      apply Matrix.det_eq_zero_of_row_eq_zero s
      intro t
      simp only [AYm, Matrix.of_apply, hq, atN]
      rw [dif_neg (by omega)]
    · push_neg at hz
      obtain ⟨s, s', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun s : Fin r => (⟨fIdx k₀ c n s.1, hz s⟩ : Fin (n + c))) (by simp; omega)
      apply Matrix.det_zero_of_row_eq hne
      funext t
      have he : fIdx k₀ c n s.1 = fIdx k₀ c n s'.1 := congrArg Fin.val heq
      simp only [AYm, Matrix.of_apply, hq, he]
  · by_cases hz : ∃ t : Fin r, n' + c' ≤ fIdx k₀ c' n' t.1
    · obtain ⟨t, ht⟩ := hz
      apply Matrix.det_eq_zero_of_column_eq_zero t
      intro s
      simp only [AYm, Matrix.of_apply, hq, eN_out (E := E) (show ¬ fIdx k₀ c' n' t.1 < n' + c' by omega),
        map_zero]
      simp [atN]
    · push_neg at hz
      obtain ⟨t, t', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun t : Fin r => (⟨fIdx k₀ c' n' t.1, hz t⟩ : Fin (n' + c'))) (by simp; omega)
      apply Matrix.det_zero_of_column_eq hne
      intro s
      have he : fIdx k₀ c' n' t.1 = fIdx k₀ c' n' t'.1 := congrArg Fin.val heq
      simp only [AYm, Matrix.of_apply, hq, he]

end PhiFacts

theorem test_function_support : PhiSuppP := by
  intro E K _ _ _ _ P q ξ k₀ r c' n' c n hk hk' y hy s l
  have hc : ∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k₀ c' n' c n 0 0 y p p') := by
    by_contra hc
    apply hy
    unfold PhiQ
    rw [if_neg (fun h => hc h.1)]
  by_cases hs : s < n' + c'
  · have h1 := hc _ _ (fPos_lt' hk l.2) (fPos_lt' hk' hs)
    simpa [entB, scE, fIdx_fPos' hk l.2, fIdx_fPos' hk' hs, atN, l.2] using h1
  · rw [eN_out (E := E) hs, map_zero]
    exact ⟨0, 1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩

private theorem algebraMap_integers_injective {E : Type} [Field E] [NumberField E] :
    Function.Injective (algebraMap (𝓞 E) E) := by
  first
    | exact IsFractionRing.injective (𝓞 E) E
    | exact FaithfulSMul.algebraMap_injective (𝓞 E) E

private theorem mul_not_mem_of_not_mem {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {s t : 𝓞 E}
    (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

private theorem one_not_mem_asIdeal {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

private theorem intAt_add_of_starRing {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨s2 * r1 + s1 * r2, s1 * s2, mul_not_mem_of_not_mem hs1 hs2, ?_⟩
  simp only [map_add, map_mul]
  rw [← h1, ← h2]
  ring

private theorem intAt_mul_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a * b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * r2, s1 * s2, mul_not_mem_of_not_mem hs1 hs2, ?_⟩
  simp only [map_mul]
  rw [← h1, ← h2]
  ring

private theorem intAt_neg_of_starRing {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [mul_neg, h, map_neg]⟩

private theorem intAt_natCast_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} (m : ℕ) : IntAt P (m : E) :=
  ⟨m, 1, one_not_mem_asIdeal, by simp⟩

private theorem mk_mul_redP_eq_of_mul_eq {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a : E} (r s : 𝓞 E) (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  haveI : P.asIdeal.IsMaximal := by
    first
      | exact P.isMaximal
      | exact P.isPrime.isMaximal P.ne_bot
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hs0
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨b * Ideal.Quotient.mk P.asIdeal r, r, s, hs, h, by rw [← mul_assoc, hb, one_mul]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc⟩ := hex.choose_spec
  have hs0' : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have key : s * r' = s' * r := algebraMap_integers_injective (by simp only [map_mul]; rw [← h, ← h']; ring)
  apply mul_left_cancel₀ hs0'
  calc Ideal.Quotient.mk P.asIdeal s' * (Ideal.Quotient.mk P.asIdeal s * hex.choose)
      = Ideal.Quotient.mk P.asIdeal s * (Ideal.Quotient.mk P.asIdeal s' * hex.choose) := by ring
    _ = Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r' := by rw [hc]
    _ = Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r := by
      rw [← map_mul, ← map_mul, key]

private theorem redP_add_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a + b) = redP P a + redP P b := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  have hs := mul_not_mem_of_not_mem hs1 hs2
  have e3 := mk_mul_redP_eq_of_mul_eq (a := a + b) (s2 * r1 + s1 * r2) (s1 * s2) hs (by
    simp only [map_add, map_mul]
    rw [← h1, ← h2]
    ring)
  have e1 := mk_mul_redP_eq_of_mul_eq r1 s1 hs1 h1
  have e2 := mk_mul_redP_eq_of_mul_eq r2 s2 hs2 h2
  have hs0 : Ideal.Quotient.mk P.asIdeal (s1 * s2) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [e3]
  simp only [map_add, map_mul]
  rw [← e1, ← e2]
  ring

private theorem redP_mul_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a * b) = redP P a * redP P b := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  have hs := mul_not_mem_of_not_mem hs1 hs2
  have e3 := mk_mul_redP_eq_of_mul_eq (a := a * b) (r1 * r2) (s1 * s2) hs (by
    simp only [map_mul]
    rw [← h1, ← h2]
    ring)
  have e1 := mk_mul_redP_eq_of_mul_eq r1 s1 hs1 h1
  have e2 := mk_mul_redP_eq_of_mul_eq r2 s2 hs2 h2
  have hs0 : Ideal.Quotient.mk P.asIdeal (s1 * s2) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [e3]
  simp only [map_mul]
  rw [← e1, ← e2]
  ring

private theorem redP_natCast {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} (m : ℕ) :
    redP P (m : E) = Ideal.Quotient.mk P.asIdeal (m : 𝓞 E) := by
  have e := mk_mul_redP_eq_of_mul_eq (P := P) (a := (m : E)) (m : 𝓞 E) 1 one_not_mem_asIdeal (by simp)
  rwa [map_one, one_mul] at e

private theorem redP_det_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {r : ℕ} (M : Matrix (Fin r) (Fin r) E)
    (hM : ∀ i j, IntAt P (M i j)) :
    redP P M.det = (Matrix.of fun i j => redP P (M i j)).det := by
  let S : Subring E :=
    { carrier := {a | IntAt P a}
      mul_mem' := fun ha hb => intAt_mul_twisted_eisenstein_coset ha hb
      one_mem' := by simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 1
      add_mem' := fun ha hb => intAt_add_of_starRing ha hb
      zero_mem' := by simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 0
      neg_mem' := fun ha => intAt_neg_of_starRing ha }
  let φ : S →+* 𝓞 E ⧸ P.asIdeal :=
    { toFun := fun a => redP P (a : E)
      map_one' := by simpa using redP_natCast (P := P) 1
      map_mul' := fun a b => redP_mul_twisted_eisenstein_coset a.2 b.2
      map_zero' := by simpa using redP_natCast (P := P) 0
      map_add' := fun a b => redP_add_twisted_eisenstein_coset a.2 b.2 }
  let MS : Matrix (Fin r) (Fin r) S := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have h1 : ((MS.det : S) : E) = M.det := by
    change S.subtype MS.det = M.det
    rw [RingHom.map_det]
    rfl
  have h2 : φ MS.det = (Matrix.of fun i j => redP P (M i j)).det := by
    rw [RingHom.map_det]
    rfl
  rw [← h1, ← h2]
  rfl

theorem test_function_periodicity : PhiPerP := by
  intro E K _ _ _ _ P _ _ ξ k₀ r c' n' c n y ε hε
  have hq : ∀ (x : HomE E (n' + c') (n + c)) (a b : ℕ), entB (qOf P) k₀ c' n' c n 0 0 x a b
      = atN (x (eN E (n' + c') (fIdx k₀ c' n' b))) (fIdx k₀ c n a) := by
    intro x a b
    simp [entB, scE]
  have hq0 : (qOf P : E) ≠ 0 := by
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    simp only [qOf]
    exact_mod_cast h0
  have hredq : redP P (qOf P : E) = 0 := by
    rw [redP_natCast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hεd : ∀ p p', IntAt P (entB (qOf P) k₀ c' n' c n 0 0 ε p p' / (qOf P : E)) := by
    intro p p'
    rw [hq]
    unfold atN
    split_ifs with hi
    · exact hε _ _
    · rw [zero_div]
      simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 0
  have hε1 : ∀ p p', IntAt P (entB (qOf P) k₀ c' n' c n 0 0 ε p p') := by
    intro p p'
    have h := intAt_mul_twisted_eisenstein_coset (intAt_natCast_twisted_eisenstein_coset (P := P) (qOf P)) (hεd p p')
    rwa [mul_div_cancel₀ _ hq0] at h
  have hεr : ∀ p p', redP P (entB (qOf P) k₀ c' n' c n 0 0 ε p p') = 0 := by
    intro p p'
    rw [← mul_div_cancel₀ (entB (qOf P) k₀ c' n' c n 0 0 ε p p') hq0,
      redP_mul_twisted_eisenstein_coset (intAt_natCast_twisted_eisenstein_coset (qOf P)) (hεd p p'), hredq, zero_mul]
  have e : ∀ p p', entB (qOf P) k₀ c' n' c n 0 0 (y + ε) p p'
      = entB (qOf P) k₀ c' n' c n 0 0 y p p' + entB (qOf P) k₀ c' n' c n 0 0 ε p p' :=
    fun p p' => entB_add' _ _ _ _ _ _ y ε p p'
  simp only [PhiQ]
  simp only [e]
  split_ifs with h1 h2 h2
  · apply unitV_congr'
    by_cases hr : n + c < r ∨ n' + c' < r
    · have d1 := aym_det_zero (qOf P) k₀ r c' n' c n (y + ε) hr
      have d2 := aym_det_zero (qOf P) k₀ r c' n' c n y hr
      simp only [AYm, e] at d1 d2
      rw [d1, d2]
    · push_neg at hr
      have hi : ∀ i : Fin r, i.1 < n + c := fun i => by have := i.2; omega
      have hj : ∀ j : Fin r, j.1 < n' + c' := fun j => by have := j.2; omega
      rw [redP_det_twisted_eisenstein_coset (Matrix.of fun s t : Fin r =>
          entB (qOf P) k₀ c' n' c n 0 0 y s.1 t.1 + entB (qOf P) k₀ c' n' c n 0 0 ε s.1 t.1)
          (fun i j => by rw [Matrix.of_apply, ← e]; exact h1.1 _ _ (hi i) (hj j)),
        redP_det_twisted_eisenstein_coset (Matrix.of fun s t : Fin r => entB (qOf P) k₀ c' n' c n 0 0 y s.1 t.1)
          (fun i j => h2.1 _ _ (hi i) (hj j))]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      rw [redP_add_twisted_eisenstein_coset (h2.1 _ _ (hi i) (hj j)) (hε1 _ _), hεr, add_zero]
  · exfalso
    apply h2
    refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' hp'' => ?_⟩
    · have h := intAt_add_of_starRing (h1.1 p p' hp hp') (intAt_neg_of_starRing (hε1 p p'))
      rwa [e, add_neg_cancel_right] at h
    · have h := intAt_add_of_starRing (h1.2 p p' hp hp' hp'') (intAt_neg_of_starRing (hεd p p'))
      rwa [e, add_div, add_neg_cancel_right] at h
  · exfalso
    apply h1
    refine ⟨fun p p' hp hp' => by rw [e]; exact intAt_add_of_starRing (h2.1 p p' hp hp') (hε1 p p'),
      fun p p' hp hp' hp'' => ?_⟩
    rw [e, add_div]
    exact intAt_add_of_starRing (h2.2 p p' hp hp' hp'') (hεd p p')
  · rfl

theorem bounded_matrix_entries : BddEntP := by
  intro E _ _ _ P R j h hb
  have hmem : ∀ x : Sp E (R.N j + cOf R j),
      x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 ↔ ∀ l, IntAt P (x l) := by
    intro x
    simp [LocE.lamY, LocE.sclLat, mem_stdAt', LocE.scE]
  have he : ∀ s, eN E (R.N j + cOf R j) s ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    intro s
    rw [hmem]
    intro l
    simp only [eN]
    split_ifs
    · simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 1
    · simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 0
  refine ⟨fun s l => ?_, fun s l => ?_⟩
  · have h1 := (hmem _).mp (hb _ (he s)).2 l
    first
      | exact h1
      | simpa using h1
  · have h1 := (hmem _).mp (hb _ (he s)).1 l
    first
      | exact h1
      | simpa using h1

end PI.TwistedEisensteinNonvanishing.W
