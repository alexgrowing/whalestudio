import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.ExistsDenLe

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

private theorem cT_add_twisted_operators {A : Type} [CommRing A] {m k : Type} (σ : A →+* A) (X Y : Matrix m k A) :
    Formalism.UG.cT σ (X + Y) = Formalism.UG.cT σ X + Formalism.UG.cT σ Y := by
  ext i j; simp [Formalism.UG.cT]

private theorem cT_smul_twisted_operators {A : Type} [CommRing A] {m k : Type} (σ : A →+* A) (c : A) (X : Matrix m k A) :
    Formalism.UG.cT σ (c • X) = σ c • Formalism.UG.cT σ X := by
  ext i j; simp [Formalism.UG.cT]

private theorem cT_cT_of_involutive' {A : Type} [CommRing A] {m k : Type} (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x)
    (X : Matrix m k A) : Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
  ext i j; simp [Formalism.UG.cT, hσ]

private theorem cT_mul_twisted_operators {A : Type} [CommRing A] {m k l : Type} [Fintype k] (σ : A →+* A) (X : Matrix m k A)
    (Y : Matrix k l A) : Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
  simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one_twisted_operators {A : Type} [CommRing A] {m : Type} [DecidableEq m] (σ : A →+* A) :
    Formalism.UG.cT σ (1 : Matrix m m A) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

private theorem orthogonal_idempotent_combination_mul {A : Type} [CommRing A] {m : Type} [Fintype m] {e f g : A} (he : e * e = e) (hf : f * f = f)
    (hg : g * g = g) (hef : e * f = 0) (heg : e * g = 0) (hfg : f * g = 0) (X Y Z X' Y' Z' : Matrix m m A) :
    (e • X + f • Y + g • Z) * (e • X' + f • Y' + g • Z') = e • (X * X') + f • (Y * Y') + g • (Z * Z') := by
  have hfe : f * e = 0 := by rw [mul_comm]; exact hef
  have hge : g * e = 0 := by rw [mul_comm]; exact heg
  have hgf : g * f = 0 := by rw [mul_comm]; exact hfg
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, hf, hg, hef, heg, hfg, hfe, hge, hgf,
    zero_smul, add_zero, zero_add]

private theorem cT_mul_self_eq_one_and_smul_eq_of_idempotent {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (hτ : ∀ x, τ (τ x) = x) {p : A}
    (hp : p * p = p) (hq : p * τ p = 0) (a : GL (Fin n) A) :
    Formalism.UG.cT τ (p • a.val + τ p • Formalism.UG.cT τ (a⁻¹).val + (1 - p - τ p) • 1) *
              (p • a.val + τ p • Formalism.UG.cT τ (a⁻¹).val + (1 - p - τ p) • 1) = 1 ∧
      p • (p • a.val + τ p • Formalism.UG.cT τ (a⁻¹).val + (1 - p - τ p) • 1) = p • a.val := by
  have hqq : τ p * τ p = τ p := by rw [← map_mul, hp]
  have hqp : τ p * p = 0 := by rw [mul_comm]; exact hq
  have hrr : (1 - p - τ p) * (1 - p - τ p) = 1 - p - τ p := by linear_combination hp + hqq + 2 * hq
  have hpr : p * (1 - p - τ p) = 0 := by linear_combination -hp - hq
  have hqr : τ p * (1 - p - τ p) = 0 := by linear_combination -hqq - hqp
  have hτr : τ (1 - p - τ p) = 1 - p - τ p := by simp [hτ]; ring
  refine ⟨?_, ?_⟩
  · have hc : Formalism.UG.cT τ (p • a.val + τ p • Formalism.UG.cT τ (a⁻¹).val + (1 - p - τ p) • 1) =
        p • (a⁻¹).val + τ p • Formalism.UG.cT τ a.val + (1 - p - τ p) • 1 := by
      rw [cT_add_twisted_operators, cT_add_twisted_operators, cT_smul_twisted_operators, cT_smul_twisted_operators, cT_smul_twisted_operators, cT_cT_of_involutive' τ hτ, cT_one_twisted_operators, hτ, hτr]
      abel
    rw [hc, orthogonal_idempotent_combination_mul hp hqq hrr hq hpr hqr, ← cT_mul_twisted_operators, Units.inv_mul, cT_one_twisted_operators, Matrix.mul_one,
      ← add_smul, ← add_smul, show p + τ p + (1 - p - τ p) = 1 by ring, one_smul]
  · simp only [smul_add, smul_smul, hp, hq, hpr, zero_smul, add_zero]

theorem mulVec_int (S : Subring A) {m : ℕ} (u : Matrix (Fin m) (Fin n) S) (x : Fin n → A) (hx : ∀ i, x i ∈ S) (i : Fin m) :
    (u.map S.subtype).mulVec x i ∈ S := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun k _ => S.mul_mem (u i k).2 (hx k)

theorem exists_isom (S : Subring A) (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (hS : ∀ x ∈ S, σ x ∈ S) {n' : ℕ} (h : n = n')
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n') (Fin n') A) (β : GL (Fin n) A) (β' : GL (Fin n') A)
    (u : GL (Fin n) S) (u' : GL (Fin n') S)
    (hu : Formalism.UG.cT σ (β * Formalism.UG.bc S.subtype u).val * J * (β * Formalism.UG.bc S.subtype u).val = 1)
    (hu' : Formalism.UG.cT σ (β' * Formalism.UG.bc S.subtype u').val * J' * (β' * Formalism.UG.bc S.subtype u').val = 1)
    (H : Set (Fin n → A)) (H' : Set (Fin n' → A)) (hH : ∀ x, x ∈ H ↔ ∀ i, (β⁻¹).val.mulVec x i ∈ S)
    (hH' : ∀ x, x ∈ H' ↔ ∀ i, (β'⁻¹).val.mulVec x i ∈ S) (p : S) (hp : p * p = p) (hq : (p : A) * σ p = 0) :
    ∃ (j : Matrix (Fin n') (Fin n) A) (U : Matrix (Fin n') (Fin n) S), Function.Bijective j.mulVec ∧
      Formalism.UG.cT σ j * J' * j = J ∧ j.mulVec '' H = H' ∧ β'.val * U.map S.subtype = j * β.val ∧
      ∀ a b, p * U a b = p * if a.val = b.val then 1 else 0 := by
  subst h
  obtain ⟨b, hb⟩ : ∃ b, b = β * Formalism.UG.bc S.subtype u := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = β' * Formalism.UG.bc S.subtype u' := ⟨_, rfl⟩
  rw [← hb] at hu
  rw [← hb'] at hu'
  have hbcS : ∀ (w : GL (Fin n) S) i k, (Formalism.UG.bc S.subtype w).val i k ∈ S := fun w i k => (w.val i k).2
  have hmul : ∀ X Y : Matrix (Fin n) (Fin n) A, (∀ i k, X i k ∈ S) → (∀ i k, Y i k ∈ S) → ∀ i k, (X * Y) i k ∈ S :=
    fun X Y hX hY i k => by
      rw [Matrix.mul_apply]
      exact S.sum_mem fun l _ => S.mul_mem (hX i l) (hY l k)
  have hpA : (p : A) * p = p := by rw [← Subring.coe_mul, hp]
  set a := Formalism.UG.bc S.subtype (u'⁻¹ * u) with ha
  set y := (p : A) • a.val + σ p • Formalism.UG.cT σ (a⁻¹).val + (1 - (p : A) - σ p) • 1 with hydef
  obtain ⟨hy, hpy⟩ := cT_mul_self_eq_one_and_smul_eq_of_idempotent σ hσ hpA hq a
  rw [← hydef] at hy hpy
  have hy' : y * Formalism.UG.cT σ y = 1 := mul_eq_one_comm.mp hy
  have hyS : ∀ i k, y i k ∈ S := by
    intro i k
    have hai : ∀ i k, (a⁻¹).val i k ∈ S := by
      intro i k; rw [ha, ← map_inv]; exact hbcS _ i k
    simp only [hydef, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply]
    refine S.add_mem (S.add_mem (S.mul_mem p.2 (hbcS _ i k)) (S.mul_mem (hS _ p.2) (hS _ (hai k i))))
      (S.mul_mem (S.sub_mem (S.sub_mem S.one_mem p.2) (hS _ p.2)) ?_)
    rw [Matrix.one_apply]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  have hcyS : ∀ i k, Formalism.UG.cT σ y i k ∈ S := fun i k => hS _ (hyS k i)
  have hcuS : ∀ i k, ((Formalism.UG.bc S.subtype u)⁻¹).val i k ∈ S := by
    intro i k; rw [← map_inv]; exact hbcS _ i k
  have hcuS' : ∀ i k, ((Formalism.UG.bc S.subtype u')⁻¹).val i k ∈ S := by
    intro i k; rw [← map_inv]; exact hbcS _ i k

  set U0 := (Formalism.UG.bc S.subtype u').val * y * ((Formalism.UG.bc S.subtype u)⁻¹).val with hU0
  set V0 := (Formalism.UG.bc S.subtype u).val * Formalism.UG.cT σ y * ((Formalism.UG.bc S.subtype u')⁻¹).val with hV0
  have hU0S : ∀ i k, U0 i k ∈ S := hmul _ _ (hmul _ _ (hbcS u') hyS) hcuS
  have hV0S : ∀ i k, V0 i k ∈ S := hmul _ _ (hmul _ _ (hbcS u) hcyS) hcuS'
  set j := b'.val * y * (b⁻¹).val with hj
  set j' := b.val * Formalism.UG.cT σ y * (b'⁻¹).val with hj'
  have h1 : j * j' = 1 := by
    simp only [hj, hj', Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [← Matrix.mul_assoc y, hy', Matrix.one_mul, Units.mul_inv]
  have h2 : j' * j = 1 := by
    simp only [hj, hj', Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [← Matrix.mul_assoc (Formalism.UG.cT σ y), hy, Matrix.one_mul, Units.mul_inv]
  have hjβ : j * β.val = β'.val * U0 := by
    simp only [hj, hU0, hb, hb', _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hj'β : j' * β'.val = β.val * V0 := by
    simp only [hj', hV0, hb, hb', _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hβj : (β'⁻¹).val * j = U0 * (β⁻¹).val := by
    calc (β'⁻¹).val * j = (β'⁻¹).val * (j * β.val) * (β⁻¹).val := by
          rw [Matrix.mul_assoc (β'⁻¹).val, Matrix.mul_assoc j, Units.mul_inv, Matrix.mul_one]
      _ = U0 * (β⁻¹).val := by rw [hjβ, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hβj' : (β⁻¹).val * j' = V0 * (β'⁻¹).val := by
    calc (β⁻¹).val * j' = (β⁻¹).val * (j' * β'.val) * (β'⁻¹).val := by
          rw [Matrix.mul_assoc (β⁻¹).val, Matrix.mul_assoc j', Units.mul_inv, Matrix.mul_one]
      _ = V0 * (β'⁻¹).val := by rw [hj'β, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  let US : Matrix (Fin n) (Fin n) S := Matrix.of fun i k => ⟨U0 i k, hU0S i k⟩
  let VS : Matrix (Fin n) (Fin n) S := Matrix.of fun i k => ⟨V0 i k, hV0S i k⟩
  have hUmap : US.map S.subtype = U0 := by ext i k; rfl
  have hVmap : VS.map S.subtype = V0 := by ext i k; rfl
  have hJ : J = Formalism.UG.cT σ (b⁻¹).val * (b⁻¹).val := by
    calc J = Formalism.UG.cT σ (b.val * (b⁻¹).val) * J * (b.val * (b⁻¹).val) := by
          rw [Units.mul_inv, cT_one_twisted_operators, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT σ (b⁻¹).val * (Formalism.UG.cT σ b.val * J * b.val) * (b⁻¹).val := by
          rw [cT_mul_twisted_operators]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]
  have hu2 : ∀ X : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ b'.val * (J' * (b'.val * X)) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu', Matrix.one_mul]
  have hy2 : ∀ X : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ y * (y * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hy, Matrix.one_mul]
  have hpU : (p : A) • U0 = (p : A) • 1 := by
    calc (p : A) • U0 = (Formalism.UG.bc S.subtype u').val * ((p : A) • y) * ((Formalism.UG.bc S.subtype u)⁻¹).val := by
          rw [hU0, Matrix.mul_smul, Matrix.smul_mul]
      _ = (Formalism.UG.bc S.subtype u').val * ((p : A) • a.val) * ((Formalism.UG.bc S.subtype u)⁻¹).val := by rw [hpy]
      _ = (p : A) • 1 := by
          rw [Matrix.mul_smul, Matrix.smul_mul, ha, map_mul, map_inv, Units.val_mul, ← Matrix.mul_assoc,
            Units.mul_inv, Matrix.one_mul, Units.mul_inv]
  refine ⟨j, US, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro x x' hxx
      have := congrArg j'.mulVec hxx
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.one_mulVec] at this
    · intro x'
      exact ⟨j'.mulVec x', by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]⟩
  · rw [hJ, hj, cT_mul_twisted_operators, cT_mul_twisted_operators]
    simp only [Matrix.mul_assoc]
    rw [hu2, hy2]
  · ext x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hH']
      intro i
      rw [Matrix.mulVec_mulVec, hβj, ← Matrix.mulVec_mulVec, ← hUmap]
      exact mulVec_int S US _ ((hH x).1 hx) i
    · intro hx'
      refine ⟨j'.mulVec x', ?_, ?_⟩
      · rw [hH]
        intro i
        rw [Matrix.mulVec_mulVec, hβj', ← Matrix.mulVec_mulVec, ← hVmap]
        exact mulVec_int S VS _ ((hH' x').1 hx') i
      · rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rw [hUmap, hjβ]
  · intro a' b''
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul]
    have e := congrFun (congrFun hpU a') b''
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    show (p : A) * U0 a' b'' = (p : A) * ((if a'.val = b''.val then 1 else 0 : S) : A)
    rw [e, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (congrArg Fin.val h1) h2
    · exact absurd (Fin.ext h2) h1
    · simp

end Generic

variable {D : D7}

set_option maxHeartbeats 800000 in
open GlobalTheory.IdemSupport GlobalTheory.LevSplit in

theorem exists_idem_set {T : Set (Pl D.host.E)} (hT : OnePlaceOver T) :
    ∃ p : Formalism.L2.Herm.intAf D.host.F D.host.E, p * p = p ∧
      (p : EAf D) * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p = 0 ∧ ∀ P ∈ T, resS D.host.F P p = 1 := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_comp D

  obtain ⟨z, hz0, hzs⟩ := hΦ.surj ((Formalism.L2.DIV.idemAd (F := D.host.E) (fun Q => Q ∈ T) : _) :
    FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have hzQ : ∀ Q, Φ z Q = if Q ∈ T then 1 else 0 := by
    intro Q
    rw [hzs]
    by_cases hQ : Q ∈ T
    · rw [if_pos hQ]; exact Formalism.L2.DIV.idemAd_pos hQ
    · rw [if_neg hQ]; exact Formalism.L2.DIV.idemAd_neg hQ
  have hzz : z * z = z := hΦ.ext' (by rw [map_mul, hz0, mul_zero]) (fun Q => by
    rw [ev_mul, hzQ]; split_ifs <;> simp)
  have hconjT : ∀ Q ∈ T, cP Q ∉ T := fun Q hQ hc => hT Q hQ (cP Q) hc ((isConjPl_iff Q _).2 rfl)

  have hzc : z * cA D z = 0 := by
    apply hΦ.ext' (by rw [map_mul, hz0, zero_mul, map_zero])
    intro Q
    rw [ev_mul, ev_zero, hzQ]
    split_ifs with hQ
    · obtain ⟨e, he⟩ := exists_delta hΦ Q
      have hce := delta_conj hΦ he
      have h0 : z * cA D e = 0 := hΦ.ext' (by rw [map_mul, hce.1, mul_zero, map_zero]) (fun Q' => by
        rw [ev_mul, ev_zero, hzQ]
        by_cases hQ' : Q' = cP Q
        · subst hQ'; rw [if_neg (hconjT Q hQ), zero_mul]
        · rw [hce.2.2 Q' hQ', mul_zero])
      have h1 : cA D z * e = 0 := by
        have := congrArg (cA D) h0
        rwa [map_mul, cA_cA, map_zero] at this
      have h2 := congrArg (fun w => Φ w Q) h1
      simp only [ev_mul, ev_zero, he.2.1, mul_one] at h2
      rw [one_mul]; exact h2
    · rw [zero_mul]
  have hzint : finPart D z ∈ intAE D := (hΦ.int z).2 (fun Q => by
    rw [hzQ]; split_ifs
    exacts [one_mem _, zero_mem _])
  set p : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨finSw D z, swapAE_int hzint⟩ with hpdef
  refine ⟨p, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show finSw D z * finSw D z = finSw D z
    rw [← map_mul, hzz]
  · show finSw D z * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (finSw D z) = 0
    have hsw : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (finSw D z) = finSw D (cA D z) := by
      show Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.IndefR.Lev.swapAE D (finPart D z)) =
        Formalism.IndefR.Lev.swapAE D (finPart D (cA D z))
      rw [(parts_cA z).2]
      generalize finPart D z = w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp [Formalism.UG.sigR, Formalism.IndefR.Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hsw, ← map_mul, hzc, map_zero]
  · intro P hP
    obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (hT P hP P hP)
    obtain ⟨q, hq, -, hq1⟩ := GlobalTheory.ParahoricLift.exists_idem_int he
    have hd : IsDelta Φ P e := (tie_iff hΦ he.1.1 (GlobalTheory.SplitScalar.infPart_splitIdem he.1) P).1 he.2
    have hze : z * e = e := hΦ.ext' (by rw [map_mul, hd.1, mul_zero]) (fun Q => by
      rw [ev_mul]
      by_cases hQ : Q = P
      · subst hQ; rw [hzQ, if_pos hP, one_mul]
      · rw [hd.2.2 Q hQ, mul_zero])
    have hmul : p * q = q := Subtype.ext (by
      show finSw D z * (q : EAf D) = q
      rw [hq, ← map_mul, hze])
    have := congrArg (resS D.host.F P) hmul
    rwa [map_mul, hq1, mul_one] at this

theorem sigR_sigR (z : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, CMData.sig]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

set_option maxHeartbeats 800000 in
theorem exists_latIsom (V V' : HSp D) (h : V.rank = V'.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (N N' : ℕ)
    (hβ : IsBaseFrame V β Λ N) (hβ' : IsBaseFrame V' β' Λ' N') (T : Set (Pl D.host.E)) (hT : OnePlaceOver T) :
    ∃ j, IsLatIsom V V' Λ Λ' j ∧ MatchesAt V V' β β' T j := by
  obtain ⟨p, hp, hq, hT1⟩ := exists_idem_set hT
  obtain ⟨u, hu⟩ := GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame V β Λ N hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame V' β' Λ' N' hβ'

  have hS : ∀ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro x hx
    change x ∈ Subring.closure _ at hx
    induction hx using Subring.closure_induction with
    | mem y hy =>
      show _ ∈ Subring.closure _
      apply Subring.subset_closure
      rcases hy with ⟨⟨z, hz⟩, rfl⟩ | ⟨w, rfl⟩
      · obtain ⟨r, rfl⟩ := hz
        refine Or.inl ⟨⟨algebraMap (𝓞 D.host.E) D.host.E (GlobalTheory.IdemSupport.cO D r), GlobalTheory.IdemSupport.cO D r, rfl⟩, ?_⟩
        simp [Formalism.UG.sigR, CMData.sig, GlobalTheory.IdemSupport.cO_coe]
        rfl
      · exact Or.inr ⟨w, by simp [Formalism.UG.sigR]⟩
    | zero => simp
    | one => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨j, U, hbij, hiso, himg, hU, hpU⟩ := exists_isom (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (sigR_sigR (D := D)) hS h
    (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
    (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) β β' u u' hu hu'
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _) (by intro x; exact hβ.1 x) (by intro x; exact hβ'.1 x) p hp hq
  refine ⟨j, ⟨⟨hbij, hiso⟩, himg⟩, U, hU, ?_⟩
  intro PP hPP a b
  have e := congrArg (Formalism.L2.DIV.resS D.host.F PP) (hpU a b)
  rw [map_mul, map_mul, hT1 PP hPP, one_mul, one_mul] at e
  rw [e]
  split_ifs <;> simp

theorem globalIsometry (D : D7) : GlobalIsometry D := by
  intro V V' h Λ Λ' β β' N N' hβ hβ' T hT
  obtain ⟨c, hc⟩ := hβ
  obtain ⟨c', hc'⟩ := hβ'
  exact exists_latIsom V V' h Λ Λ' β β' _ _ hc hc' T hT

theorem exists_baseFrame (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : Formalism.IndefR.Datum.IsSelfDualC V Λ) : ∃ β N, IsBaseFrame V β Λ N := by
  unfold Formalism.IndefR.Datum.IsSelfDualC at h
  obtain ⟨hlat, hsd⟩ := h
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E V.rank Λ hlat

  have hCfg : (GlobalTheory.Member.latC V).FG := V.standardTuple_isLattice.fg.map _
  have hCspan : Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [GlobalTheory.Member.latC, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact V.frame.equivFun.surjective
  obtain ⟨N1, hN1, h1⟩ := PI.SqPairW.exists_den_le hCfg hlat.span_eq_top
  obtain ⟨N2, hN2, h2⟩ := PI.SqPairW.exists_den_le hlat.fg hCspan
  have hcast : ∀ (k : ℕ) (x : Fin V.rank → D.host.E), ((k : D.host.E)) • x = (k : ℤ) • x := fun k x => by
    rw [← Int.cast_smul_eq_zsmul D.host.E]; simp
  have hsplit : ∀ x : Fin V.rank → D.host.E, ((N1 * N2 : ℕ) : D.host.E) • x = (N2 : ℤ) • ((N1 : ℤ) • x) := fun x => by
    rw [← hcast, ← hcast, ← mul_smul, ← Nat.cast_mul, mul_comm]
  have hsplit' : ∀ x : Fin V.rank → D.host.E, ((N1 * N2 : ℕ) : D.host.E) • x = (N1 : ℤ) • ((N2 : ℤ) • x) := fun x => by
    rw [← hcast, ← hcast, ← mul_smul, ← Nat.cast_mul]
  have hdual : Formalism.BasicNotions.dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram Λ = Λ := by
    ext y
    rw [SetLike.mem_coe, hsd y]
    exact Iff.rfl
  refine ⟨β, N1 * N2, hβ, ?_, Nat.mul_pos hN1 hN2, ?_, ?_⟩
  · unfold Formalism.L2.Herm.dualL
    rw [hdual, Submodule.span_eq]
  · intro x hx
    rw [hsplit]
    exact zsmul_mem (h1 x ((GlobalTheory.ParahoricLift.mem_L0c_iff_mem_intVec_of_span_frame V x).1 hx)) _
  · intro x hx
    rw [hsplit']
    exact (GlobalTheory.ParahoricLift.mem_L0c_iff_mem_intVec_of_span_frame V _).2 (zsmul_mem (h2 x hx) _)

theorem exists_inv {A : Type} [CommRing A] {m n : ℕ} {j : Matrix (Fin m) (Fin n) A} (h : Function.Bijective j.mulVec) :
    ∃ j' : Matrix (Fin n) (Fin m) A, j * j' = 1 ∧ j' * j = 1 := by
  let e := LinearEquiv.ofBijective (Matrix.mulVecLin j) h
  have he : ∀ y, j.mulVec (e.symm y) = y := fun y => e.apply_symm_apply y
  have he' : ∀ x, e.symm (j.mulVec x) = x := fun x => e.symm_apply_apply x
  refine ⟨LinearMap.toMatrix' (e.symm : (Fin m → A) →ₗ[A] (Fin n → A)), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    exact he y
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    exact he' x

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}

theorem loc_maps (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (Λ' : Submodule (𝓞 E) (Fin m → E))
    (j : Matrix (Fin m) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ, j.mulVec x ∈ Formalism.L2.Herm.hatL (F := F) Λ') :
    ∀ x ∈ Formalism.L2.Herm.locL v Λ, (j.map (Formalism.UG.prV (E := E) v)).mulVec x ∈ Formalism.L2.Herm.locL v Λ' := by

  have hint : ∀ s ∈ Formalism.L2.Herm.intAf F E, Formalism.UG.prV (E := E) v s ∈ Formalism.BasicNotions.intV E v := by
    intro s hs
    change s ∈ Subring.closure _ at hs
    induction hs using Subring.closure_induction with
    | mem y hy =>
      show _ ∈ Subring.closure _
      apply Subring.subset_closure
      rcases hy with ⟨z, rfl⟩ | ⟨w, rfl⟩
      · exact Or.inl ⟨z, by rw [Formalism.UG.P.afsplit_prV_tmul]; rfl⟩
      · exact Or.inr ⟨⟨(w : Formalism.L2.Herm.Af F) v,
          (show ∀ v', (w : Formalism.L2.Herm.Af F) v' ∈ v'.adicCompletionIntegers F from w.2) v⟩,
          by rw [Formalism.UG.P.afsplit_prV_tmul]⟩
    | zero => simp
    | one => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

  have hlat : ∀ (k : ℕ) (M : Submodule (𝓞 E) (Fin k → E)) (y : Fin k → E ⊗[F] Formalism.L2.Herm.Af F),
      y ∈ Formalism.L2.Herm.hatL (F := F) M → (fun i => Formalism.UG.prV (E := E) v (y i)) ∈ Formalism.L2.Herm.locL v M := by
    intro k M y hy
    change y ∈ Submodule.span _ _ at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      show _ ∈ Submodule.span _ _
      apply Submodule.subset_span
      exact ⟨l, hl, by funext i; simp only [Formalism.UG.P.afsplit_prV_inclE]⟩
    | zero =>
      convert (Formalism.L2.Herm.locL v M).zero_mem using 1
      funext i; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext i; simp
    | smul c x _ hx =>
      convert Submodule.smul_mem _ (⟨_, hint c c.2⟩ : Formalism.BasicNotions.intV E v) hx using 1
      funext i; simp [Subring.smul_def, map_mul]
  have hm : ∀ w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F,
      (j.map (Formalism.UG.prV (E := E) v)).mulVec (fun i => Formalism.UG.prV (E := E) v (w i)) =
        fun i => Formalism.UG.prV (E := E) v (j.mulVec w i) := fun w => by
    funext i; exact (RingHom.map_mulVec _ _ _ i).symm
  intro x hx
  change x ∈ Submodule.span _ _ at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have hg : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (l i)) =
        fun i => Formalism.UG.prV (E := E) v ((fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) i) := by
      funext i; rw [Formalism.UG.P.afsplit_prV_inclE]
    dsimp only
    rw [hg, hm]
    exact hlat _ Λ' _ (h _ (Submodule.subset_span ⟨l, hl, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ c hx

end Loc

theorem image_iff {A : Type} [CommRing A] {m n : ℕ} {j : Matrix (Fin m) (Fin n) A} {j' : Matrix (Fin n) (Fin m) A}
    (h1 : j * j' = 1) (h2 : j' * j = 1) (H : Set (Fin n → A)) (H' : Set (Fin m → A)) :
    j.mulVec '' H = H' ↔ (∀ x ∈ H, j.mulVec x ∈ H') ∧ ∀ x ∈ H', j'.mulVec x ∈ H := by
  constructor
  · rintro rfl
    refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  · rintro ⟨hf, hb⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hf x hx
    · intro hy
      exact ⟨j'.mulVec y, hb y hy, by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]⟩

theorem bij_of_inv {A : Type} [CommRing A] {m n : ℕ} {j : Matrix (Fin m) (Fin n) A} {j' : Matrix (Fin n) (Fin m) A}
    (h1 : j * j' = 1) (h2 : j' * j = 1) : Function.Bijective j.mulVec := by
  constructor
  · intro x y hxy
    have := congrArg j'.mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.one_mulVec] at this
  · intro y
    exact ⟨j'.mulVec y, by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]⟩

theorem isom_map {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (ψ : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ψ.comp σ = τ.comp ψ) {j : Matrix (Fin m) (Fin n) A} {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A}
    (hj : Formalism.UG.cT σ j * J' * j = J) : Formalism.UG.cT τ (j.map ψ) * J'.map ψ * j.map ψ = J.map ψ := by
  have hc : Formalism.UG.cT τ (j.map ψ) = (Formalism.UG.cT σ j).map ψ := by
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    exact (RingHom.congr_fun h (j b a)).symm
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hj]

theorem loc_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (Λ' : Submodule (𝓞 E) (Fin m → E))
    (G : Matrix (Fin n) (Fin n) E) (G' : Matrix (Fin m) (Fin m) E) (j : Matrix (Fin m) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hb : Function.Bijective j.mulVec)
    (hi : Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) j * G'.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * j =
      G.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
    (hl : j.mulVec '' (Formalism.L2.Herm.hatL (F := F) Λ : Set _) = (Formalism.L2.Herm.hatL (F := F) Λ' : Set _)) :
    (Function.Bijective (j.map (Formalism.UG.prV (E := E) v)).mulVec ∧
      Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (j.map (Formalism.UG.prV (E := E) v)) *
        G'.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) * j.map (Formalism.UG.prV (E := E) v) =
      G.map (Formalism.UG.inclE (F := F) (v.adicCompletion F))) ∧
    (j.map (Formalism.UG.prV (E := E) v)).mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _) := by
  obtain ⟨j', h1, h2⟩ := exists_inv hb
  have hc : (Formalism.UG.prV (E := E) v).comp (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) =
      (Formalism.UG.sigR σ (v.adicCompletion F)).comp (Formalism.UG.prV (E := E) v) := Formalism.UG.P.afsplit_prV_comp_sigR σ v
  have hG : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) E),
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))).map (Formalism.UG.prV (E := E) v) =
        M.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := fun M => by
    ext a b; simp only [Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]
  have h1v : j.map (Formalism.UG.prV (E := E) v) * j'.map (Formalism.UG.prV (E := E) v) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2v : j'.map (Formalism.UG.prV (E := E) v) * j.map (Formalism.UG.prV (E := E) v) = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨bij_of_inv h1v h2v, ?_⟩, ?_⟩
  · have := isom_map (Formalism.UG.prV (E := E) v) (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) (Formalism.UG.sigR σ (v.adicCompletion F)) hc hi
    rwa [hG, hG] at this
  · have hl' := (image_iff h1 h2 _ _).1 hl
    rw [image_iff h1v h2v]
    exact ⟨loc_maps v Λ Λ' j hl'.1, loc_maps v Λ' Λ j' hl'.2⟩

theorem isLocLatIsom_map {V V' : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} {j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)}
    (h : IsLatIsom V V' Λ Λ' j) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsLocLatIsom V V' Λ Λ' v (j.map (Formalism.UG.prV (E := D.host.E) v)) := by
  obtain ⟨⟨hb, hi⟩, hl⟩ := h
  exact loc_gen D.sp.cm.sig v Λ Λ' V.gram V'.gram j hb hi hl

end GlobalTheory.FinAdIdent

end
