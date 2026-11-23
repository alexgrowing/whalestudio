import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQWordAdj

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

def Zl (l : ℕ) : Subring ℚ where
  carrier := {x | x.den.Coprime l}
  mul_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem mem_Zl (l : ℕ) (x : ℚ) : x ∈ Zl l ↔ x.den.Coprime l := Iff.rfl

theorem lrc_int_mem (l : ℕ) (z : ℤ) : (z : ℚ) ∈ Zl l := by
  rw [mem_Zl]; simp

theorem lrc_coprime_iff {l : ℕ} (hl : l.Prime) (m : ℕ) : m.Coprime l ↔ ¬ (l : ℤ) ∣ (m : ℤ) := by
  rw [Int.natCast_dvd_natCast, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]

theorem lrc_inv_mem {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : ((m : ℚ)⁻¹) ∈ Zl l := by
  rw [mem_Zl]
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero _)
  have h : ((m : ℚ)⁻¹).den = m.natAbs := by
    rw [Rat.inv_intCast_den, if_neg hm0]
  rw [h, lrc_coprime_iff hl, Int.dvd_natAbs]
  exact hm

theorem zl_mem_iff {l : ℕ} (hl : l.Prime) (x : ℚ) :
    x ∈ Zl l ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ ∃ z : ℤ, (m : ℚ) * x = z := by
  constructor
  · intro hx
    refine ⟨(x.den : ℤ), (lrc_coprime_iff hl _).1 hx, x.num, ?_⟩
    have := Rat.den_mul_eq_num x
    exact_mod_cast this
  · rintro ⟨m, hm, z, hz⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      intro h
      have : m = 0 := by exact_mod_cast h
      subst this
      exact hm (dvd_zero _)
    have : x = (m : ℚ)⁻¹ * (z : ℚ) := by
      rw [← hz, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
    rw [this]
    exact (Zl l).mul_mem (lrc_inv_mem hl m hm) (lrc_int_mem l z)

theorem zl_unit {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : Zl l) := by
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    subst this
    exact hm (dvd_zero _)
  refine IsUnit.of_mul_eq_one (⟨(m : ℚ)⁻¹, lrc_inv_mem hl m hm⟩ : Zl l) ?_
  apply Subtype.ext
  simp [hm0]

theorem mem_one_iff (l : ℕ) (x : ℚ) : x ∈ (1 : Submodule (Zl l) ℚ) ↔ x ∈ Zl l := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

example (l : ℕ) (V : Type) [AddCommGroup V] [Module ℚ V] : IsScalarTower (Zl l) ℚ V := inferInstance
example (l : ℕ) : Algebra (Zl l) ℚ := inferInstance

theorem lrc_smul_def (l : ℕ) {V : Type*} [AddCommGroup V] [Module ℚ V] (c : Zl l) (v : V) :
    c • v = (c : ℚ) • v := rfl

def locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) :
    Submodule (Zl l) V where
  carrier := {v | ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M}
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨m', hm', hb⟩
    refine ⟨m * m', fun h => ?_, ?_⟩
    · rcases (Nat.prime_iff_prime_int.1 hl).dvd_or_dvd h with h | h
      · exact hm h
      · exact hm' h
    · rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact M.zsmul_mem ha _
      · rw [mul_smul]
        exact M.zsmul_mem hb _
  zero_mem' := ⟨1, fun h => by
    have := Int.natCast_dvd_natCast.1 (by simpa using h : ((l : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hl.one_lt.ne' (Nat.dvd_one.1 this), by simp⟩
  smul_mem' := by
    rintro c v ⟨m, hm, hv⟩
    obtain ⟨m', hm', z, hz⟩ := (zl_mem_iff hl (c : ℚ)).1 c.2
    refine ⟨m' * m, fun h => ?_, ?_⟩
    · rcases (Nat.prime_iff_prime_int.1 hl).dvd_or_dvd h with h | h
      · exact hm' h
      · exact hm h
    · have : (m' * m) • (c • v) = z • (m • v) := by
        rw [lrc_smul_def, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ z, ← Int.cast_smul_eq_zsmul ℚ m,
          smul_smul, smul_smul, ← hz]
        congr 1
        push_cast
        ring
      rw [this]
      exact M.zsmul_mem hv _

theorem mem_locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) (v : V) :
    v ∈ locSpan l hl M ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M := Iff.rfl

theorem le_locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) {v : V}
    (hv : v ∈ M) : v ∈ locSpan l hl M :=
  ⟨1, fun h => by
    have := Int.natCast_dvd_natCast.1 (by simpa using h : ((l : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hl.one_lt.ne' (Nat.dvd_one.1 this), by simpa using hv⟩

theorem lrc_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := rfl

theorem lrc_eval_map (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) P) = ((eval (idFrame ℤ r n) P : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ r n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ r n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp only [RingHom.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun F => F P) h

theorem lrc_applyWord_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [applyWord_cons]
    exact rowDivStable R r n ν _ _ _ _ ih

theorem lrc_fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [(fockQPos σ f (g + g')).1, (fockQBilin σ g g' f 1).1, (fockQPos σ g f).1, (fockQPos σ g' f).1]

theorem lrc_fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [(fockQPos σ f (c • g)).1, (fockQBilin σ g 0 f c).2, (fockQPos σ g f).1]

theorem lrc_fock_zero_right {σ : Type} (f : MvPolynomial σ ℚ) : fockQ f 0 = 0 := by
  have := lrc_fock_smul_right (0 : ℚ) f 0
  simpa using this

theorem fock_word (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin r × Fin r) ℚ)
    (hF : F ∈ dualWeyl ℚ r r ν) (w : List (Fin r × Fin r × ℕ)) :
    fockQ F (applyWord ℚ w (hw ℚ le_rfl ν)) =
      eval (idFrame ℚ r r) (applyWord ℚ (transposeWord w) F) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  rw [(fockQPos _ F _).1, fock_space_word_adjoint,
    fock_space_highest_weight r r le_rfl ν hν _ (lrc_applyWord_mem ℚ r r ν _ F hF)]

theorem fock_int (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ dualWeyl ℤ r r ν) (y : MvPolynomial (Fin r × Fin r) ℤ) (hy : y ∈ weyl ℤ r r le_rfl ν) :
    ∃ z : ℤ, fockQ (intQ r r x) (intQ r r y) = z * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    refine ⟨eval (idFrame ℤ r r) (applyWord ℤ (transposeWord w) x), ?_⟩
    simp only [lrc_intQ_apply]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map,
      fock_word r ν hν _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r r ν x hx) w, lclosedeq_applyWord_map, lrc_eval_map]
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, lrc_fock_zero_right]
    simp
  | add y y' _ _ ih ih' =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨z', hz'⟩ := ih'
    refine ⟨z + z', ?_⟩
    rw [map_add, lrc_fock_add_right, hz, hz']
    push_cast
    ring
  | smul c y _ ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨c * z, ?_⟩
    rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ, lrc_fock_smul_right, hz]
    push_cast
    ring

theorem lrc_den_dvd_mul (x : ℚ) (m : ℕ) (h : x.den ∣ m) : ∃ z : ℤ, (m : ℚ) * x = z := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(k : ℤ) * x.num, ?_⟩
  have := Rat.den_mul_eq_num x
  push_cast
  rw [← this]
  ring

theorem dual_int_loc (hC : CoeffWord) (hL : LowerTriIntegral) (l : ℕ) (hl : l.Prime) (r : ℕ) (ν : Fin r → ℕ)
    (g : MvPolynomial (Fin r × Fin r) ℚ) (hg : g ∈ dualWeyl ℚ r r ν)
    (h : ∀ ω : List (Fin r × Fin r × ℕ), eval (idFrame ℚ r r) (applyWord ℚ ω g) ∈ Zl l) :
    ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ ∃ g' ∈ dualWeyl ℤ r r ν, (m : ℚ) • g = intQ r r g' := by
  classical
  have hhom : IsWeightedHomogeneous (colW r r) g ν := hg.1
  have h1 : ∀ e : Fin r × Fin r →₀ ℕ, LowerTri e → coeff e g ∈ Zl l := by
    intro e he
    by_cases hs : ∀ s : Fin r, ∑ a : Fin r, e (a, s) = ν s
    · rw [hC ℚ r r ν g e hhom he hs]
      exact h _
    · have : coeff e g = 0 := by
        by_contra hne
        apply hs
        intro s
        rw [← lccomp_weight_colW_apply, hhom hne]
      rw [this]
      exact (Zl l).zero_mem
  set M : ℕ := ∏ e ∈ g.support.filter (fun e => LowerTri e), (coeff e g).den with hM
  have hMc : M.Coprime l := by
    rw [hM]
    refine Nat.Coprime.prod_left fun e he => ?_
    exact h1 e (Finset.mem_filter.1 he).2
  have h2 : ∀ e : Fin r × Fin r →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e ((M : ℚ) • g) = z := by
    intro e he
    rw [coeff_smul, smul_eq_mul]
    by_cases hes : e ∈ g.support
    · exact lrc_den_dvd_mul _ _ (Finset.dvd_prod_of_mem (fun e => (coeff e g).den) (Finset.mem_filter.2 ⟨hes, he⟩))
    · rw [notMem_support_iff.1 hes]
      exact ⟨0, by simp⟩
  have hMg : (M : ℚ) • g ∈ dualWeyl ℚ r r ν := (dualWeyl ℚ r r ν).smul_mem _ hg
  obtain ⟨Q', hQ'⟩ := hL r r ν _ hMg h2
  refine ⟨(M : ℤ), (lrc_coprime_iff hl M).1 hMc, Q', ?_, ?_⟩
  · rw [dualWeylIntRat r r ν Q', ← lrc_intQ_apply, ← hQ']
    exact hMg
  · rw [← hQ']
    push_cast
    rfl

end Formalism.CohomologicalDescent.LR
