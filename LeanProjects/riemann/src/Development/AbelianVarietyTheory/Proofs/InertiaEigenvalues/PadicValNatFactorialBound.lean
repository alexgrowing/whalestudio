import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_eq_l_mul_of_natCast {A : Type} [CommRing A] (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    {m k : ℕ} (hm : m ≠ 0) (hv : padicValNat l m < padicValNat l k) {y z : A}
    (h : (m : A) * y = (k : A) * z) : ∃ w, y = l * w := by
  have hp := hl.out
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hv
  have htf' : ∀ (j : ℕ) (x : A), (l : A) ^ j * x = 0 → x = 0 := fun j => by
    induction j with
    | zero => simp
    | succ j ih => exact fun x hx => htf x (ih _ (by linear_combination hx))
  rw [← Nat.factorization_def m hp, ← Nat.factorization_def k hp] at hv
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m l
  have hk' := Nat.ordProj_mul_ordCompl_eq_self k l
  have hcop := Nat.coprime_ordCompl hp hm
  generalize m / l ^ m.factorization l = m' at hm' hcop
  generalize k / l ^ k.factorization l = k' at hk'
  generalize m.factorization l = a at hm' hv
  generalize k.factorization l = b at hk' hv
  subst hm' hk'
  push_cast at h
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have huv' : (u : A) * l + (v : A) * m' = 1 := by
    have := congrArg (Int.cast : ℤ → A) huv
    push_cast at this
    exact this
  have e : (l : A) ^ b = (l : A) ^ a * ((l : A) ^ (b - a - 1) * l) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have h1 : (m' : A) * y = (l : A) ^ (b - a - 1) * l * k' * z := by
    apply sub_eq_zero.1
    apply htf' a
    rw [e] at h
    linear_combination h
  exact ⟨u * y + v * (l : A) ^ (b - a - 1) * k' * z, by linear_combination (-y) * huv' + (v : A) * h1⟩

theorem cong_add {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a + b) = (a + b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out a b
  exact ⟨w + w' - a * b * r, by rw [map_add, hw, hw', hr]; ring⟩

theorem cong_mul {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a * b) = (a * b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  exact ⟨a ^ l * w' + w * b ^ l + (l : A) * w * w', by rw [map_mul, hw, hw']; ring⟩

theorem frobC_ainfToAcris (b : Ainf l) :
    frobC l (ainfToAcris l b) = ainfToAcris l (WittVector.frobenius b) := by
  rw [← GlobalTheory.RingBasics.φA_apply]
  exact (GlobalTheory.CrisMaps.phiA_extends l).alg b

theorem cong_ainf (b : Ainf l) :
    ∃ w, frobC l (ainfToAcris l b) = ainfToAcris l b ^ l + (l : Per.Acris l) * w := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add b
  exact ⟨ainfToAcris l c, by rw [frobC_ainfToAcris, hc, map_add, map_pow, map_mul, map_natCast]⟩

theorem frob_mem_of_theta {x : Ainf l} (hx : Per.θ l x = 0) :
    ∃ u, ainfToAcris l (WittVector.frobenius x) = (l : Per.Acris l) * u := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add x
  obtain ⟨d, hd⟩ := exists_dpow hx l
  have hf : (l.factorial : Per.Acris l) = (l : Per.Acris l) * ((l - 1).factorial : Per.Acris l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hl.out.ne_zero]
  refine ⟨((l - 1).factorial : Per.Acris l) * d + ainfToAcris l c, ?_⟩
  rw [hc, map_add, map_pow, ← hd, map_mul, map_natCast, hf]
  ring

theorem padicValNat_factorial_bound {n : ℕ} (hn : n ≠ 0) :
    l * padicValNat l n.factorial < padicValNat l n.factorial + n := by
  have h := sub_one_mul_padicValNat_factorial (p := l) n
  have hlast := Nat.getLast_digit_ne_zero l hn
  have hpos : 0 < (l.digits n).sum :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hlast) (List.le_sum_of_mem (List.getLast_mem _))
  have h2 : 2 ≤ l := hl.out.two_le
  generalize padicValNat l n.factorial = v at h ⊢
  generalize (l.digits n).sum = s at h hpos
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have e : (k + 1) * v = k * v + v := by ring
  rw [e]
  generalize k * v = t at h ⊢
  omega

theorem cong_gen {x : Ainf l} (hx : Per.θ l x = 0) {n : ℕ} {Y : Per.Acris l}
    (hY : (n.factorial : Per.Acris l) * Y = ainfToAcris l x ^ n) :
    ∃ w, frobC l Y = Y ^ l + (l : Per.Acris l) * w := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Y = 1 := by simpa using hY
    exact ⟨0, by rw [this]; simp⟩
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  obtain ⟨w1, hw1⟩ : ∃ w, frobC l Y = (l : Per.Acris l) * w := by
    have h1 := congrArg (frobC l) hY
    rw [map_mul, map_natCast, map_pow, frobC_ainfToAcris, hu, mul_pow] at h1
    refine exists_eq_l_mul_of_natCast htf (Nat.factorial_ne_zero n) (k := l ^ n) (z := u ^ n) ?_ ?_
    · rw [padicValNat.prime_pow]
      exact padicValNat_factorial_lt_of_ne_zero l hn.ne'
    · rw [h1]; push_cast; rfl
  obtain ⟨w2, hw2⟩ : ∃ w, Y ^ l = (l : Per.Acris l) * w := by
    obtain ⟨d, hd⟩ := exists_dpow hx (l * n)
    have h2 : ((n.factorial ^ l : ℕ) : Per.Acris l) * Y ^ l = ((l * n).factorial : ℕ) * d := by
      rw [hd, Nat.cast_pow, ← mul_pow, hY, ← pow_mul, mul_comm n l]
    refine exists_eq_l_mul_of_natCast htf (pow_ne_zero _ (Nat.factorial_ne_zero n)) ?_ h2
    rw [padicValNat.pow n.factorial l, padicValNat_factorial_mul]
    exact padicValNat_factorial_bound hn.ne'
  exact ⟨w1 - w2, by rw [hw1, hw2]; ring⟩

theorem cong_acris0 : ∀ (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l),
    ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) =
      (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) ^ l + (l : Per.Acris l) * w := by
  intro s hs
  let S : Subalgebra (Per.Ainf l) (Per.Acris0 l) :=
    { carrier := {t | ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) t) =
        (algebraMap (Per.Acris0 l) (Per.Acris l) t) ^ l + (l : Per.Acris l) * w}
      mul_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) ^ l + (l : Per.Acris l) * w
        rw [map_mul]
        exact cong_mul (frobC l).toRingHom hx hy
      add_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) ^ l + (l : Per.Acris l) * w
        rw [map_add]
        exact cong_add (frobC l).toRingHom hx hy
      algebraMap_mem' := fun r => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) ^ l +
            (l : Per.Acris l) * w
        rw [← GlobalTheory.RingIface.tower]
        exact cong_ainf r }
  have hle : Per.Acris0 l ≤ S.map (Per.Acris0 l).val := by
    refine GlobalTheory.RingIface.acris0_le_3 l _ fun x hx n y hy hn => ?_
    refine Subalgebra.mem_map.2 ⟨⟨y, hy⟩, ?_, rfl⟩
    refine cong_gen hx (n := n) ?_
    have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * ⟨y, hy⟩ =
        algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
    rw [map_mul, map_natCast, map_pow, ← GlobalTheory.RingIface.tower] at h2
    exact h2
  obtain ⟨t, ht, e⟩ := Subalgebra.mem_map.1 (hle hs)
  have e' : (⟨s, hs⟩ : Per.Acris0 l) = t := Subtype.ext e.symm
  rw [e']
  exact ht

theorem frobC_cong (y : Per.Acris l) : ∃ w, frobC l y = y ^ l + (l : Per.Acris l) * w := by
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 y 1
  obtain ⟨w, hw⟩ := cong_acris0 s.1 s.2
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ 1 * z)
    (algebraMap (Per.Acris0 l) (Per.Acris l) s) l
  refine ⟨w + frobC l z - z * c, ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast, hw]
  linear_combination -hc

end GlobalTheory.AcrisPrism

namespace GlobalTheory.AcrisPrism

variable (l : ℕ) [hl : Fact l.Prime]

def acrisDelta : Delta l (Per.Acris l) :=
  Delta.ofLift l (frobC l).toRingHom (GlobalTheory.MemLoc.acris_basic l).2.1 fun a => frobC_cong a

theorem isUnit_delta_l : IsUnit ((acrisDelta l).δ (l : Per.Acris l)) := by
  have h := (acrisDelta l).φ_eq (l : Per.Acris l)
  have h1 : (acrisDelta l).φ (l : Per.Acris l) = l := map_natCast _ _
  rw [h1] at h
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  have e : (l : Per.Acris l) ^ l = (l : Per.Acris l) ^ 2 * (l : Per.Acris l) ^ (l - 2) := by
    rw [← pow_add]
    congr 1
    have := hl.out.two_le
    omega
  have h2 : (acrisDelta l).δ (l : Per.Acris l) = (l : Per.Acris l) * (-(l : Per.Acris l) ^ (l - 2)) + 1 := by
    apply sub_eq_zero.1
    apply htf
    linear_combination -h - e
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  rw [h2]
  exact Ideal.mem_jacobson_bot.1
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self (l : Per.Acris l))) _

theorem l_mem_nonZeroDivisors : (l : Per.Acris l) ∈ nonZeroDivisors (Per.Acris l) := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  exact mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm, hx])⟩

def ainfPhiToAcris : Ainf l →+* Per.Acris l := (ainfToAcris l).toRingHom.comp WittVector.frobenius

theorem ainfPhiToAcris_le (F : FinExt l) :
    (ainfObj F).I ≤ (Ideal.span {(l : Per.Acris l)}).comap (ainfPhiToAcris l) := by
  intro a ha
  have hx : Per.θ l a = 0 := RingHom.mem_ker.1 ha
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  exact Ideal.mem_span_singleton'.2 ⟨u, by rw [mul_comm]; exact hu.symm⟩

def acrisObj (F : FinExt l) : Obj l ↥(OL F) :=
  Obj.ofDistinguished hl.out.pos (acrisDelta l) (l : Per.Acris l) (l_mem_nonZeroDivisors l)
    (isUnit_delta_l l) (by rw [sup_idem]; exact (GlobalTheory.MemLoc.acris_basic l).1)
    ⟨1, fun x _ => by
      have : ((l : ℕ) : Per.Acris l ⧸ Ideal.span {(l : Per.Acris l)}) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      simp [this]⟩
    ((Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l) (ainfPhiToAcris_le l F)).comp
      (ainfObj F).str)

def acrisHom (F : FinExt l) : Hom (ainfObj F) (acrisObj l F) where
  f := ainfPhiToAcris l
  f_δ := Delta.map_δ_of_map_φ (ainfObj F).D (acrisDelta l) (GlobalTheory.MemLoc.acris_basic l).2.1 _
    fun a => (frobC_ainfToAcris (WittVector.frobenius a)).symm
  f_I := fun a ha => ainfPhiToAcris_le l F ha
  f_str := fun r a h => by
    change Ideal.Quotient.mk _ (ainfPhiToAcris l a) =
      Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l)
        (ainfPhiToAcris_le l F) ((ainfObj F).str r)
    rw [← h]
    rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ (C : Obj l ↥(OL F)) (eC : C.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj F) C), C.I = Ideal.span {(l : C.A)} ∧ (∀ x, eC (C.D.φ x) = frobC l (eC x)) ∧ ∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x) :=
  fun l _ F => ⟨acrisObj l F, RingEquiv.refl _, acrisHom l F, rfl, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.AcrisPrism
