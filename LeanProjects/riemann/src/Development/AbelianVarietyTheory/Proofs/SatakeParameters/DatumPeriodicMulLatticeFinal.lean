import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.TopInv

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc

theorem ite_ctx {α : Type} {b c : Prop} {db : Decidable b} {dc : Decidable c} {x y u : α} (h : b ↔ c) (ht : c → x = u) :
    @ite _ b db x y = @ite _ c dc u y := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.2 hc), ht hc]
  · rw [if_neg hc, if_neg fun hb => hc (h.1 hb)]

section Local

variable {E K : Type} [Field E] [NumberField E] [Field K]

def intS (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := fun ha hb => IntAt.mul ha hb
  add_mem' := fun ha hb => IntAt.add ha hb
  one_mem' := by simpa using IntAt.coe P 1
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by simpa using IntAt.mul (IntAt.coe P (-1)) ha

theorem mem_intS {P : HeightOneSpectrum (𝓞 E)} {a : E} : a ∈ intS P ↔ IntAt P a := Iff.rfl

def redH (P : HeightOneSpectrum (𝓞 E)) : intS P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_zero' := by simpa using reduction_coe P 0
  map_mul' a b := reduction_mul a.2 b.2
  map_add' a b := reduction_add a.2 b.2

variable {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_add_iff {a z : E} (hz : IntAt P z) : IntAt P (a + z) ↔ IntAt P a :=
  ⟨fun h => by simpa using mem_intS.1 ((intS P).sub_mem h hz), fun h => h.add hz⟩

theorem intAt_nat (q : ℕ) : IntAt P (q : E) := natCast_mem (intS P) q

theorem redP_det_congr {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n E)
    (hA : ∀ i j, IntAt P (A i j)) (hB : ∀ i j, IntAt P (B i j)) (h : ∀ i j, redP P (A i j) = redP P (B i j)) :
    redP P A.det = redP P B.det := by
  have key : ∀ (C : Matrix n n E) (hC : ∀ i j, IntAt P (C i j)),
      redP P C.det = Matrix.det (Matrix.of fun i j => redP P (C i j)) := by
    intro C hC
    let C' : Matrix n n (intS P) := Matrix.of fun i j => ⟨C i j, hC i j⟩
    have h1 : C.det = ((C'.det : intS P) : E) := by
      have := (intS P).subtype.map_det C'
      exact this.symm
    rw [h1]
    exact (redH P).map_det C'
  rw [key A hA, key B hB]
  simp only [h]

theorem unitV_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) : unitV χ a = unitV χ b := by
  unfold unitV
  rw [h]

variable {q : ℕ}

theorem intAt_of_div (hq0 : (q : E) ≠ 0) {z : E} (hz : IntAt P (z / q)) : IntAt P z := by
  have := IntAt.mul (intAt_nat q) hz
  rwa [mul_div_cancel₀ _ hq0] at this

theorem redP_add_q (hq : (q : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (a : E) {z : E} (hz : IntAt P (z / q)) :
    redP P (a + z) = redP P a := by
  by_cases ha : IntAt P a
  · rw [reduction_add ha (intAt_of_div hq0 hz)]
    have h1 : redP P z = 0 := by
      have h2 : redP P (q : E) = 0 := by
        have := reduction_coe P (q : 𝓞 E)
        rw [map_natCast] at this
        rw [this, Ideal.Quotient.eq_zero_iff_mem]
        exact hq
      have := reduction_mul (intAt_nat q) hz
      rwa [mul_div_cancel₀ _ hq0, h2, zero_mul] at this
    rw [h1, add_zero]
  · rw [reduction_eq_zero_of_not_integral P ha, reduction_eq_zero_of_not_integral P fun h => ha ((intAt_add_iff (intAt_of_div hq0 hz)).1 h)]

theorem intAt_sum_div {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i, IntAt P (f i / q)) :
    IntAt P ((∑ i ∈ s, f i) / q) := by
  rw [Finset.sum_div]
  exact (intS P).sum_mem fun i _ => h i

theorem unitV_det_add (hq : (q : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ}
    (M Z : ℕ → ℕ → E) (hZ : ∀ p p', IntAt P (Z p p' / q)) (f : Fin t → ℕ) (hM : ∀ s s', IntAt P (M (f s) (f s'))) :
    unitV χ (Matrix.det (Matrix.of fun s s' : Fin t => M (f s) (f s') + Z (f s) (f s'))) =
      unitV χ (Matrix.det (Matrix.of fun s s' : Fin t => M (f s) (f s'))) :=
  unitV_congr χ (redP_det_congr _ _ (fun s s' => (hM s s').add (intAt_of_div hq0 (hZ _ _))) hM
    fun s s' => redP_add_q hq hq0 _ (hZ _ _))

theorem prod_det_add (hq : (q : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (r t j : ℕ)
    (M Z : ℕ → ℕ → E) (hZ : ∀ p p', IntAt P (Z p p' / q)) (hM : ∀ p p', p' < r + j * t → IntAt P (M p p')) :
    ∏ i ∈ Finset.range j, unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
        M (r + i * t + s.1) (r + i * t + s'.1) + Z (r + i * t + s.1) (r + i * t + s'.1))) =
      ∏ i ∈ Finset.range j, unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
        M (r + i * t + s.1) (r + i * t + s'.1))) := by
  refine Finset.prod_congr rfl fun i hi => ?_
  refine unitV_det_add hq hq0 (χ i) M Z hZ (fun s => r + i * t + s.1) fun s s' => hM _ _ ?_
  have h1 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t (Finset.mem_range.1 hi)
  have := s'.2
  rw [add_mul, one_mul] at h1
  omega

theorem atN_add {N : ℕ} (v w : Fin N → E) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  unfold atN
  split_ifs <;> simp

theorem entB_add {N' N : ℕ} (k₀ c' n' c n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E N' N) :
    entB q k₀ c' n' c n ex' ex (x + z) = fun p p' => entB q k₀ c' n' c n ex' ex x p p' + entB q k₀ c' n' c n ex' ex z p p' := by
  funext p p'
  simp only [entB, LinearMap.add_apply, atN_add, add_mul]

theorem fIdx_zero (k₀ n p : ℕ) : fIdx k₀ 0 n p = p := by
  unfold fIdx
  split_ifs <;> omega

theorem entB_row {n' c' n : ℕ} (k₀ : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E (n' + c') (n + 0)) {p : ℕ} (p' : ℕ) (hp : ¬ p < n + 0) :
    entB q k₀ c' n' 0 n ex' ex x p p' = 0 := by
  simp only [entB, fIdx_zero, atN, dif_neg hp, zero_mul]

theorem eN_out {N p : ℕ} (hp : ¬ p < N) : eN E N p = 0 := by
  funext l
  have := l.2
  simp only [eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem entB_col {n' n : ℕ} (k₀ : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0)) (p : ℕ) {p' : ℕ} (hp : ¬ p' < n' + 0) :
    entB q k₀ 0 n' 0 n ex' ex x p p' = 0 := by
  simp only [entB, fIdx_zero, eN_out hp, map_zero, atN]
  split_ifs <;> simp

theorem entB_int {n' n : ℕ} (k₀ : ℕ) (ex' ex : ℕ → ℕ) (z : HomE E (n' + 0) (n + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / q)) (p p' : ℕ) : IntAt P (entB q k₀ 0 n' 0 n ex' ex z p p' / q) := by
  by_cases hp : p < n + 0
  · by_cases hp' : p' < n' + 0
    · have e : eN E (n' + 0) p' = Pi.single ⟨p', hp'⟩ 1 := by
        funext l
        simp [eN, Pi.single_apply, Fin.ext_iff]
      simp only [entB, fIdx_zero, atN, dif_pos hp, scE, e]
      rw [if_pos (by omega), if_pos (by omega)]
      simpa using hz ⟨p', hp'⟩ ⟨p, hp⟩
    · rw [entB_col k₀ ex' ex z p hp', zero_div]
      exact zero_mem (intS P)
  · rw [entB_row k₀ ex' ex z p' hp, zero_div]
    exact zero_mem (intS P)

variable [StarRing E]

theorem PhiG_add (hq : (q : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool) (k₀ r t j c' n' n : ℕ) (hc : c' = 0) (x z : HomE E (n' + c') (n + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / q)) :
    PhiG q ψ₀ χ sharp k₀ r t j c' n' 0 n (x + z) = PhiG q ψ₀ χ sharp k₀ r t j c' n' 0 n x := by
  subst hc
  have hZ := entB_int k₀ (fun i => i + 1) (fun i => i + 1) z hz
  have h0 := fun p p' => entB_row (q := q) k₀ (fun i => i + 1) (fun i => i + 1) x (p := p) p'
  unfold PhiG lamGv
  dsimp only
  rw [entB_add]
  generalize entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) x = M at *
  generalize entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) z = Z at *
  have a1 := fun a p p' => intAt_add_iff (a := a) (hZ p p')
  have a2 := fun a p p' => intAt_add_iff (a := a) (intAt_of_div hq0 (hZ p p'))
  have a3 := fun a p p' => redP_add_q hq hq0 a (hZ p p')
  refine ite_ctx (by simp only [add_div, a1, a2, a3]) fun h => ?_
  beta_reduce
  · have hM : ∀ p p', p' < r + (j - 1) * t → IntAt P (M p p') := fun p p' hp' => by
      by_cases hp : p < n + 0
      · exact h.1 p p' hp hp'
      · rw [h0 p p' hp]; exact zero_mem (intS P)
    rw [prod_det_add hq hq0 χ r t (j - 1) M Z hZ hM,
      unitV_det_add hq hq0 _ M Z hZ (fun s : Fin (r + (j - 1) * t) => s.1) fun s s' => hM _ _ s'.2,
      Finset.sum_add_distrib, redP_add_q hq hq0 _ (intAt_sum_div _ _ fun i => hZ _ _)]

theorem PhiGS_add (hq : (q : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS r t j c' n' n : ℕ) (hc : c' = 0) (x z : HomE E (n' + c') (n + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / q)) :
    PhiGS q ψ₀ χ k₀ rS r t j c' n' 0 n (x + z) = PhiGS q ψ₀ χ k₀ rS r t j c' n' 0 n x := by
  subst hc
  have hZ := entB_int k₀ (fun i => i + 1) (fun i => i + 1) z hz
  have h0 := fun p p' => entB_row (q := q) k₀ (fun i => i + 1) (fun i => i + 1) x (p := p) p'
  unfold PhiGS lamGvS
  dsimp only
  rw [entB_add]
  generalize entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) x = M at *
  generalize entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) z = Z at *
  have a1 := fun a p p' => intAt_add_iff (a := a) (hZ p p')
  have a2 := fun a p p' => intAt_add_iff (a := a) (intAt_of_div hq0 (hZ p p'))
  have a3 := fun a p p' => redP_add_q hq hq0 a (hZ p p')
  refine ite_ctx (by simp only [add_div, a1, a2, a3]) fun h => ?_
  beta_reduce
  · have hM : ∀ p p', p' < r + (j - 1) * t → IntAt P (M p p') := fun p p' hp' => by
      by_cases hp : p < n + 0
      · exact h.1 p p' hp hp'
      · rw [h0 p p' hp]; exact zero_mem (intS P)
    rw [prod_det_add hq hq0 χ r t (j - 1) M Z hZ hM,
      unitV_det_add hq hq0 _ M Z hZ (fun s : Fin (r + (j - 1) * t) => s.1) fun s s' => hM _ _ s'.2,
      Finset.sum_add_distrib, Finset.sum_add_distrib, add_add_add_comm, redP_add_q hq hq0]
    rw [add_div]
    exact (intAt_sum_div _ _ fun i => hZ _ _).add (intAt_sum_div _ _ fun i => hZ _ _)

theorem PhiQ_add (hq : (q : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' n : ℕ) (hc : c' = 0) (x z : HomE E (n' + c') (n + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / q)) :
    PhiQ q ξ k₀ r c' n' 0 n (x + z) = PhiQ q ξ k₀ r c' n' 0 n x := by
  subst hc
  have hZ := entB_int k₀ 0 0 z hz
  have h0 := fun p p' => entB_row (q := q) k₀ 0 0 x (p := p) p'
  have h1 := fun p p' => entB_col (q := q) k₀ 0 0 x p (p' := p')
  unfold PhiQ
  rw [entB_add]
  generalize entB q k₀ 0 n' 0 n 0 0 x = M at *
  generalize entB q k₀ 0 n' 0 n 0 0 z = Z at *
  have a1 := fun a p p' => intAt_add_iff (a := a) (hZ p p')
  have a2 := fun a p p' => intAt_add_iff (a := a) (intAt_of_div hq0 (hZ p p'))
  refine ite_ctx (by simp only [add_div, a1, a2]) fun h => ?_
  beta_reduce
  · have hM : ∀ p p', IntAt P (M p p') := fun p p' => by
      by_cases hp : p < n + 0
      · by_cases hp' : p' < n' + 0
        · exact h.1 p p' hp hp'
        · rw [h1 p p' hp']; exact zero_mem (intS P)
      · rw [h0 p p' hp]; exact zero_mem (intS P)
    rw [unitV_det_add hq hq0 _ M Z hZ (fun s : Fin r => s.1) fun s s' => hM _ _]

end Local

section Transform

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_div_pow_le (hq0 : (q : E) ≠ 0) {a b : ℕ} (h : a ≤ b) {z : E} (hz : IntAt P (z / (q : E) ^ b)) :
    IntAt P (z / (q : E) ^ a) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  have := IntAt.mul (intAt_nat (P := P) (q ^ c)) hz
  convert this using 1
  push_cast
  field_simp
  ring

theorem form_apply {n : ℕ} (f : Sp E n →ₗ[E] E) (y : Sp E n) : f y = ∑ i, y i * f (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' y]
  simp [map_sum]

theorem psi_shift (hq0 : (q : E) ≠ 0) (psi : E → K) (D a b : ℕ) (hD : a + b ≤ D)
    (hadd : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → psi (x + y) = psi x * psi y)
    (hint : ∀ x : E, IntAt P x → psi x = 1) {n : ℕ} (η ζ : Sp E n →ₗ[E] E) (y : Sp E n) (e : ℤ)
    (hη : ∀ i, IntAt P ((q : E) ^ a * η (Pi.single i 1))) (hζ : ∀ i, IntAt P (ζ (Pi.single i 1) / (q : E) ^ b))
    (hy : ∀ i, IntAt P ((q : E) ^ b * y i)) : psi ((e : E) * (η + ζ) y) = psi ((e : E) * η y) := by
  have he : IntAt P (e : E) := intCast_mem (intS P) e
  have h1 : IntAt P ((e : E) * ζ y) := by
    rw [form_apply]
    refine he.mul ((intS P).sum_mem fun i _ => ?_)
    have := (hy i).mul (hζ i)
    rw [mem_intS]
    convert this using 1
    field_simp
  have h2 : IntAt P ((q : E) ^ D * ((e : E) * η y)) := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hD
    rw [form_apply, mul_left_comm, Finset.mul_sum]
    refine he.mul ((intS P).sum_mem fun i _ => ?_)
    have := (intAt_nat (P := P) (q ^ c)).mul ((hy i).mul (hη i))
    rw [mem_intS]
    convert this using 1
    push_cast
    ring
  have h3 : IntAt P ((q : E) ^ D * ((e : E) * ζ y)) := by
    have := (intAt_nat (P := P) (q ^ D)).mul h1
    simpa using this
  rw [LinearMap.add_apply, mul_add, hadd _ _ h2 h3, hint _ h1, mul_one]

theorem qOf_ne (P : HeightOneSpectrum (𝓞 E)) : ((qOf P : ℕ) : E) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem qOf_mem (P : HeightOneSpectrum (𝓞 E)) : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _

theorem atNL_int {N : ℕ} (i : ℕ) (w : Sp E N) (c : E) (h : ∀ l, IntAt P (w l / c)) : IntAt P (atNL E N i w / c) := by
  unfold atNL
  split_ifs with hi
  · exact h _
  · rw [LinearMap.zero_apply, zero_div]
    exact zero_mem (intS P)

theorem single_int {N : ℕ} (s i : Fin N) : IntAt P ((Pi.single s 1 : Sp E N) i) := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem (intS P)
  · exact zero_mem (intS P)

end Transform

section Chain

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical in
theorem ftY_add (hc : cst.Ok) (P : rowSG Pr sel mu) (hD : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) {n : ℕ}
    (η ζ : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n)
    (hζ : ∀ i, IntAt P.1 (ζ (Pi.single i 1) / (qOf P.1 : X.E) ^ cst.B))
    (hy : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y i)) :
    ftY sel mu cst P (η + ζ) y = ftY sel mu cst P η y := by
  have hq0 := qOf_ne P.1
  have h0 : ∀ i, IntAt P.1 (ζ (Pi.single i 1)) := fun i => by
    simpa using intAt_div_pow_le hq0 (Nat.zero_le _) (hζ i)
  have h1 : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * ζ (Pi.single i 1)) := fun i => by
    simpa using (intAt_nat (P := P.1) (qOf P.1 ^ cst.M)).mul (h0 i)
  unfold ftY
  have e1 : (∀ i : Fin n, IntAt P.1 ((η + ζ) (Pi.single i 1))) ↔ ∀ i : Fin n, IntAt P.1 (η (Pi.single i 1)) := by
    exact forall_congr' fun i => intAt_add_iff (h0 i)
  have e2 : (∀ i : Fin n, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * (η + ζ) (Pi.single i 1))) ↔
      ∀ i : Fin n, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1)) := by
    refine forall_congr' fun i => ?_
    rw [LinearMap.add_apply, mul_add, intAt_add_iff (h1 i)]
  simp only [e1, e2]
  by_cases hP : P.1 ∈ Pr.vGs
  · simp only [if_pos hP] at hy ⊢
    split_ifs with h
    · exact psi_shift hq0 (cst.psi P) (cst.D P) 0 1 (by simpa using hc.D_pos P) (hc.psi_add P) (hc.psi_int P) η ζ y _
        (by simpa using h) (fun i => intAt_div_pow_le hq0 hc.B_pos (hζ i)) hy
    · rfl
  · simp only [if_neg hP] at hy ⊢
    split_ifs with h
    · rw [psi_shift hq0 (cst.psi P) (cst.D P) cst.M cst.M (by have := hD hP; omega) (hc.psi_add P) (hc.psi_int P) η ζ y _
        h (fun i => intAt_div_pow_le hq0 hc.M_le_B (hζ i)) hy]
    · rfl

open Classical in
theorem repY_mem {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (Y : Set (Sp X.E n)) (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have hmem : repY Y ∈ Y := Classical.epsilon_spec (p := fun z => z ∈ Y) ⟨y, by
    rw [hY]; simp⟩
  generalize repY Y = z at *
  rw [hY] at hmem
  have hq0 := qOf_ne P.1
  have h1 := (Submodule.mem_iInf _).1 hy P
  have h2 := (Submodule.mem_iInf _).1 hmem P
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
  by_cases hP : P.1 ∈ Pr.vGs
  · simp only [if_pos hP] at h1 h2 ⊢
    have := add_mem (Submodule.smul_mem _ ((qOf P.1 : ℕ) : 𝓞 X.E) h2) h1
    convert this using 1
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E]
    simp [smul_sub]
  · simp only [if_neg hP] at h1 h2 ⊢
    have := add_mem (Submodule.smul_mem _ ((qOf P.1 ^ (cst.M + cst.M) : ℕ) : 𝓞 X.E) h2) h1
    convert this using 1
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E, smul_smul]
    have e : ((qOf P.1 ^ (cst.M + cst.M) : ℕ) : X.E) * ((qOf P.1 : X.E) ^ (cst.M : ℤ))⁻¹ = (qOf P.1 : X.E) ^ cst.M := by
      push_cast
      rw [zpow_natCast, pow_add, mul_inv_cancel_right₀ (pow_ne_zero _ hq0)]
    rw [e]
    simp [smul_sub]

theorem PhiTop_add {R : Ranks} (Ch : Chars X Pr R.m) (sharp : Bool) (m2 : ℕ) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTop Ch mu sharp m2 P (x + z) = PhiTop Ch mu sharp m2 P x := by
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  unfold PhiTop
  split_ifs
  · exact PhiGS_add (qOf_mem P) (qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact PhiG_add (qOf_mem P) (qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact PhiQ_add (qOf_mem P) (qOf_ne P) _ _ _ _ _ _ hc x z hz

end Chain

section Hom

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG') (hd' : d'.Ok)
    (x y₀ : HomE E a b) (c : 𝓞 E) (hc : ∀ P : ST, c ∈ P.1.asIdeal)
    (hy : ∀ P : ST, ∀ v ∈ d.at P.1, y₀ v ∈ d'.at P.1) : phiT K d d' (x + c • y₀) = phiT K d d' x := by
  classical
  unfold phiT
  refine ite_ctx (forall_congr' fun P => forall_congr' fun v => forall_congr' fun hv => ?_) fun _ => rfl
  have h1 : c • y₀ v ∈ d'.at P.1 := Submodule.smul_mem _ c (hy P v hv)
  rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.add_mem_iff_left _ h1]
  refine and_congr_right fun h => ?_
  rw [hd'.f_add P _ h _ h1, hd'.f_smul P c _ (hy P v hv), Ideal.Quotient.eq_zero_iff_mem.2 (hc P), zero_mul, add_zero]

theorem inFr_add (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x y : HomE E a b) :
    inFr f f' (x + y) = inFr f f' x + inFr f f' y := by
  ext v l
  simp [inFr]

end Hom

end GlobalTheory.TopInv
