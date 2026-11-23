import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

noncomputable section

namespace GlobalTheory.FrobInt

section Tilt

open Ideal

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def sharpRoot (x : PreTilt O p) (n : ℕ) : O :=
  (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] x).untilt

theorem sharpRoot_pow_succ (x : PreTilt O p) (n : ℕ) :
    sharpRoot x (n + 1) ^ p = sharpRoot x n := by
  rw [sharpRoot, sharpRoot, Function.iterate_succ_apply', ← map_pow, ← frobenius_def,
    frobenius_apply_frobeniusEquiv_symm]

theorem mk_sharpRoot (x : PreTilt O p) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (sharpRoot x n) = PreTilt.coeff n x := by
  rw [sharpRoot, PreTilt.mk_untilt_eq_coeff_zero]
  have := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at this
  exact this

theorem dvd_of_sharpRoot_dvd [IsDomain O] (a b : PreTilt O p) (ha : ∀ n, sharpRoot a n ≠ 0)
    (h : ∀ n, sharpRoot a n ∣ sharpRoot b n) : a ∣ b := by
  choose e he using h
  have hcomp : ∀ n, e (n + 1) ^ p = e n := by
    intro n
    have h2 := sharpRoot_pow_succ b n
    rw [he (n + 1), he n, mul_pow, sharpRoot_pow_succ] at h2
    exact mul_left_cancel₀ (ha n) h2
  let c : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (e n), fun n => by
    show (Ideal.Quotient.mk (span {(p : O)}) (e (n + 1))) ^ p = _
    rw [← map_pow, hcomp]⟩
  refine ⟨c, Perfection.ext fun n => ?_⟩
  show PreTilt.coeff n b = PreTilt.coeff n (a * c)
  rw [map_mul, ← mk_sharpRoot, ← mk_sharpRoot, he n, map_mul]
  rfl

theorem sharpRoot_ne_zero (a : PreTilt O p) [IsDomain O] (ha : a ≠ 0) (n : ℕ) :
    sharpRoot a n ≠ 0 := by
  intro h0
  apply ha
  have hall : ∀ k, sharpRoot a (n + k) = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      have := sharpRoot_pow_succ a (n + k)
      rw [ih] at this
      exact pow_eq_zero_iff hp.out.ne_zero |>.1 this
  have hlow : ∀ k m, sharpRoot a (m + k) = 0 → sharpRoot a m = 0 := by
    intro k
    induction k with
    | zero => intro m h; exact h
    | succ k ih =>
      intro m h
      apply ih
      rw [← sharpRoot_pow_succ, add_assoc, h, zero_pow hp.out.ne_zero]
  refine Perfection.ext fun m => ?_
  show PreTilt.coeff m a = PreTilt.coeff m 0
  rw [map_zero, ← mk_sharpRoot, hlow n m (by rw [add_comm]; exact hall m), map_zero]

theorem dvd_total_tilt [IsDomain O] [ValuationRing O] (a b : PreTilt O p) : a ∣ b ∨ b ∣ a := by
  by_cases ha : a = 0
  · right; rw [ha]; exact dvd_zero _
  by_cases hb : b = 0
  · left; rw [hb]; exact dvd_zero _
  have key : ∀ a b : PreTilt O p, sharpRoot a 0 ∣ sharpRoot b 0 →
      ∀ n, sharpRoot a n ∣ sharpRoot b n := by
    intro a b h n
    induction n with
    | zero => exact h
    | succ n ih =>
      rw [← sharpRoot_pow_succ a, ← sharpRoot_pow_succ b] at ih
      exact (IsIntegrallyClosed.pow_dvd_pow_iff hp.out.ne_zero).1 ih
  rcases ValuationRing.dvd_total (sharpRoot a 0) (sharpRoot b 0) with h | h
  · exact Or.inl (dvd_of_sharpRoot_dvd a b (sharpRoot_ne_zero a ha) (key a b h))
  · exact Or.inr (dvd_of_sharpRoot_dvd b a (sharpRoot_ne_zero b hb) (key b a h))

end Tilt

theorem valuationRing_tilt (l : ℕ) [Fact l.Prime] : ValuationRing (OCb l) := by
  have : IsAdicComplete (Ideal.span {((l : ℕ) : OC l)}) (OC l) :=
    GlobalTheory.PadicComplexHost.isAdicComplete l
  exact ValuationRing.iff_dvd_total.2 ⟨fun a b => dvd_total_tilt a b⟩

section General

variable {l : ℕ} [hl : Fact l.Prime] {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {p q : Type} [Fintype p] [Fintype q]

theorem residue_integral (z : Matrix p q K) (s : Matrix p p R) (s' : Matrix q q R)
    (y : Matrix p q R)
    (h : z.map (· ^ l) = s.map (algebraMap R K) * z * s'.map (algebraMap R K) + y.map (algebraMap R K))
    (a : p) (b : q) : ∃ r : R, algebraMap R K r = z a b := by
  classical
  let v := ValuationRing.valuation R K
  have hint : ∀ x : K, v x ≤ 1 ↔ ∃ r : R, algebraMap R K r = x := fun x =>
    ValuationRing.mem_integer_iff R K x
  have hR : ∀ r : R, v (algebraMap R K r) ≤ 1 := fun r => (hint _).2 ⟨r, rfl⟩
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset (p × q))
    (fun c => v (z c.1 c.2)) ⟨(a, b), Finset.mem_univ _⟩
  rw [← hint]
  refine le_trans (hc (a, b) (Finset.mem_univ _)) ?_
  by_contra hlt
  push Not at hlt
  have h1 := congrFun (congrFun h c.1) c.2
  have h2 : v (z c.1 c.2 ^ l) ≤ v (z c.1 c.2) := by
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply] at h1
    rw [h1]
    refine v.map_add_le ?_ (le_trans (hR _) hlt.le)
    refine v.map_sum_le fun j _ => ?_
    rw [map_mul]
    refine le_trans (mul_le_of_le_one_right' (hR _)) ?_
    refine v.map_sum_le fun i _ => ?_
    rw [map_mul]
    exact le_trans (mul_le_of_le_one_left' (hR _)) (hc (i, j) (Finset.mem_univ _))
  rw [map_pow] at h2
  have h3 : v (z c.1 c.2) ^ 1 < v (z c.1 c.2) ^ l := pow_lt_pow_right₀ hlt hl.out.one_lt
  rw [pow_one] at h3
  exact absurd h2 (not_le.2 h3)

variable [CharP R l] [CharP K l] [PerfectRing R l] [PerfectRing K l]

omit [IsDomain R] [ValuationRing R] in
theorem exists_p_mul {k : Type} [CommRing k] [CharP k l] [PerfectRing k l] (x : WittVector l k)
    (hx : x.coeff 0 = 0) : ∃ w, x = (l : WittVector l k) * w := by
  have := (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero x 1).2 (fun m hm => by
    obtain rfl : m = 0 := by omega
    exact hx)
  rw [pow_one, Ideal.mem_span_singleton] at this
  exact this

theorem step (S : Matrix p p (WittVector l R)) (S' : Matrix q q (WittVector l R))
    (Z : Matrix p q (WittVector l K)) (Y : Matrix p q (WittVector l R))
    (h : Z.map (WittVector.map (frobenius K l)) =
      S.map (WittVector.map (algebraMap R K)) * Z * S'.map (WittVector.map (algebraMap R K)) +
        Y.map (WittVector.map (algebraMap R K))) :
    ∃ (Z₀ : Matrix p q (WittVector l R)) (Z' : Matrix p q (WittVector l K))
      (Y' : Matrix p q (WittVector l R)),
      Z = Z₀.map (WittVector.map (algebraMap R K)) + (l : WittVector l K) • Z' ∧
      Z'.map (WittVector.map (frobenius K l)) =
      S.map (WittVector.map (algebraMap R K)) * Z' * S'.map (WittVector.map (algebraMap R K)) +
        Y'.map (WittVector.map (algebraMap R K)) := by
  set ι : WittVector l R →+* WittVector l K := WittVector.map (algebraMap R K) with hι
  set φ : WittVector l K →+* WittVector l K := WittVector.map (frobenius K l) with hφ
  set φ' : WittVector l R →+* WittVector l R := WittVector.map (frobenius R l) with hφ'
  have hcomm : ∀ x, φ (ι x) = ι (φ' x) := by
    intro x
    ext n
    simp [hι, hφ, hφ', WittVector.map_coeff, frobenius_def]
  have h0 := residue_integral (l := l) (Z.map WittVector.constantCoeff)
    (S.map WittVector.constantCoeff) (S'.map WittVector.constantCoeff)
    (Y.map WittVector.constantCoeff) (by
      ext a b
      have h1 := congrArg WittVector.constantCoeff (congrFun (congrFun h a) b)
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum,
        map_mul] at h1 ⊢
      simpa [hι, hφ, WittVector.map_coeff, frobenius_def] using h1)
  choose r hr using h0
  let Z₀ : Matrix p q (WittVector l R) := fun a b => WittVector.teichmuller l (r a b)
  have h2 : ∀ a b, ∃ w, Z a b - ι (Z₀ a b) = (l : WittVector l K) * w := by
    intro a b
    apply exists_p_mul
    show WittVector.constantCoeff (Z a b - ι (Z₀ a b)) = 0
    rw [map_sub, sub_eq_zero]
    have := hr a b
    simp only [Matrix.map_apply] at this
    rw [← this]
    simp [hι, Z₀, WittVector.map_coeff]
  choose Z' hZ' using h2
  have hZ : Z = Z₀.map ι + (l : WittVector l K) • Matrix.of Z' := by
    ext1 a b
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hZ']; ring
  let B : Matrix p q (WittVector l R) := S * Z₀ * S' + Y - Z₀.map φ'
  have hB : B.map ι = (l : WittVector l K) •
      ((Matrix.of Z').map φ - S.map ι * Matrix.of Z' * S'.map ι) := by
    have e1 : (Z₀.map φ').map ι = (Z₀.map ι).map φ := by
      ext1 a b; simp [hcomm]
    have e2 : Z.map φ = (Z₀.map ι).map φ + (l : WittVector l K) • (Matrix.of Z').map φ := by
      rw [hZ]; ext1 a b; simp
    have e3 : B.map ι = S.map ι * Z₀.map ι * S'.map ι + Y.map ι - (Z₀.map ι).map φ := by
      rw [← e1]
      ext1 a b; simp [B, Matrix.mul_apply]
    rw [e2] at h
    rw [e3]
    conv at h => rhs; rw [hZ]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] at h
    rw [smul_sub]
    have := eq_sub_of_add_eq h
    rw [this]; abel
  have h3 : ∀ a b, ∃ w, B a b = (l : WittVector l R) * w := by
    intro a b
    apply exists_p_mul
    apply IsFractionRing.injective R K
    have h4 := congrArg WittVector.constantCoeff (congrFun (congrFun hB a) b)
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast,
      CharP.cast_eq_zero, zero_mul] at h4
    simpa [hι, WittVector.map_coeff] using h4
  choose Y' hY' using h3
  refine ⟨Z₀, Matrix.of Z', Matrix.of Y', hZ, ?_⟩
  ext1 a b
  have h5 := congrFun (congrFun hB a) b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hY', map_mul, map_natCast,
    Matrix.sub_apply] at h5
  have h6 := mul_left_cancel₀ (WittVector.p_nonzero l K) h5
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.of_apply] at h6 ⊢
  rw [h6]; ring

theorem approx (S : Matrix p p (WittVector l R)) (S' : Matrix q q (WittVector l R)) (n : ℕ) :
    ∀ (Z : Matrix p q (WittVector l K)) (Y : Matrix p q (WittVector l R)),
    Z.map (WittVector.map (frobenius K l)) =
      S.map (WittVector.map (algebraMap R K)) * Z * S'.map (WittVector.map (algebraMap R K)) +
        Y.map (WittVector.map (algebraMap R K)) →
    ∀ a b, ∃ A w, Z a b = WittVector.map (algebraMap R K) A + (l : WittVector l K) ^ n * w := by
  induction n with
  | zero => intro Z Y _ a b; exact ⟨0, Z a b, by simp⟩
  | succ n ih =>
    intro Z Y h a b
    obtain ⟨Z₀, Z', Y', h1, h2⟩ := step S S' Z Y h
    obtain ⟨A, w, hA⟩ := ih Z' Y' h2 a b
    refine ⟨Z₀ a b + l * A, w, ?_⟩
    rw [h1]
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hA, map_add,
      map_mul, map_natCast]
    ring

theorem integral_of_frobenius (S : Matrix p p (WittVector l R)) (S' : Matrix q q (WittVector l R))
    (Z : Matrix p q (WittVector l K)) (Y : Matrix p q (WittVector l R))
    (h : Z.map (WittVector.map (frobenius K l)) =
      S.map (WittVector.map (algebraMap R K)) * Z * S'.map (WittVector.map (algebraMap R K)) +
        Y.map (WittVector.map (algebraMap R K))) (a : p) (b : q) :
    Z a b ∈ Set.range (WittVector.map (p := l) (algebraMap R K)) := by
  have hc : ∀ n, ∃ r : R, algebraMap R K r = (Z a b).coeff n := by
    intro n
    obtain ⟨A, w, hA⟩ := approx S S' (n + 1) Z Y h a b
    refine ⟨A.coeff n, ?_⟩
    have h1 : Z a b - WittVector.map (algebraMap R K) A ∈
        Ideal.span {(l : WittVector l K) ^ (n + 1)} :=
      Ideal.mem_span_singleton.2 ⟨w, by rw [hA]; ring⟩
    rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero, ← WittVector.mem_ker_truncate,
      RingHom.mem_ker, map_sub, sub_eq_zero] at h1
    have h2 := congrArg (fun x => TruncatedWittVector.coeff (⟨n, by omega⟩ : Fin (n + 1)) x) h1
    simp only [WittVector.coeff_truncate, WittVector.map_coeff] at h2
    exact h2.symm
  choose r hr using hc
  refine ⟨WittVector.mk l r, ?_⟩
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_mk, hr]

end General

theorem perfectRing_Cb (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

theorem frobenius_integrality : ∀ (l : ℕ) [Fact l.Prime] (p q : Type) [Fintype p] [Fintype q]
    (Z : Matrix p q (WCb l)) (S : Matrix p p (Ainf l)) (S' : Matrix q q (Ainf l))
    (Y : Matrix p q (Ainf l)),
    Z.map (frobW l) = S.map (inclW l) * Z * S'.map (inclW l) + Y.map (inclW l) →
    ∀ a b, Z a b ∈ Set.range (inclW l) := by
  intro l _ p q _ _ Z S S' Y h a b
  have := valuationRing_tilt l
  have := perfectRing_Cb l
  exact integral_of_frobenius S S' Z Y h a b

end GlobalTheory.FrobInt
