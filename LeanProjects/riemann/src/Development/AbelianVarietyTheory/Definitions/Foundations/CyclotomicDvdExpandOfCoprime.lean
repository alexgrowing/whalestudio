import Mathlib
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors

noncomputable section

open PowerSeries Polynomial

namespace GlobalTheory.Col

variable (R : Type) [CommRing R]

def cyc (p m : ℕ) : PowerSeries R := (Polynomial.cyclotomic (p ^ m) R).eval₂ PowerSeries.C (1 + PowerSeries.X)

abbrev lev (p m : ℕ) : Type := PowerSeries R ⧸ Ideal.span {cyc R p m}

abbrev ev (p m : ℕ) : PowerSeries R →+* lev R p m := Ideal.Quotient.mk _

variable {R}

theorem hasSubst_om (p : ℕ) (hp : 0 < p) : PowerSeries.HasSubst (((1 + PowerSeries.X : PowerSeries R) ^ p) - 1) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  simp only [map_sub, map_pow, map_add, map_one]
  erw [PowerSeries.constantCoeff_X]
  simp

def phi (p : ℕ) (hp : 0 < p) : PowerSeries R →ₐ[R] PowerSeries R :=
  PowerSeries.substAlgHom (hasSubst_om (R := R) p hp)

def dd (h : PowerSeries R) : PowerSeries R := (1 + PowerSeries.X) * PowerSeries.derivative R h

def dlog (u : (PowerSeries R)ˣ) : PowerSeries R := dd (u : PowerSeries R) * ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)

end GlobalTheory.Col

namespace GlobalTheory.Col
variable {R : Type} [CommRing R]

theorem phi_X (p : ℕ) (hp : 0 < p) : phi (R := R) p hp PowerSeries.X = ((1 + PowerSeries.X : PowerSeries R) ^ p) - 1 := by
  unfold phi; rw [PowerSeries.substAlgHom_X]

theorem phi_one_add_X (p : ℕ) (hp : 0 < p) : phi (R := R) p hp (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ p := by
  rw [map_add, map_one, phi_X]; ring

theorem phi_eval₂ (p : ℕ) (hp : 0 < p) (P : R[X]) :
    phi (R := R) p hp (P.eval₂ PowerSeries.C (1 + PowerSeries.X)) = (Polynomial.expand R p P).eval₂ PowerSeries.C (1 + PowerSeries.X) := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp [Polynomial.eval₂_add, map_add, hf, hg]
  | monomial n a =>
    simp only [Polynomial.eval₂_monomial, Polynomial.expand_monomial, map_mul, map_pow, phi_one_add_X, ← pow_mul]
    congr 1
    · exact (phi (R := R) p hp).commutes a
    · ring

theorem phi_cyc (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m) :
    phi (R := R) p hp.out.pos (cyc R p m) = cyc R p (m + 1) := by
  unfold cyc
  rw [phi_eval₂, Polynomial.cyclotomic_expand_eq_cyclotomic hp.out (dvd_pow_self p (by omega)), pow_succ]

def up (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m) : lev R p m →+* lev R p (m + 1) :=
  Ideal.Quotient.lift _ ((ev R p (m + 1)).comp (phi (R := R) p hp.out.pos).toRingHom) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, phi_cyc p m hm]
    have h0 : ev R p (m + 1) (cyc R p (m + 1)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [h0, mul_zero])
end GlobalTheory.Col

namespace GlobalTheory.Col
variable {R : Type} [CommRing R]

def nrm (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) : lev R p (m + 1) →* lev R p m :=
  letI := (up (R := R) p m hm).toAlgebra
  Algebra.norm (lev R p m)

def normOp (p : ℕ) [hp : Fact p.Prime] (h : PowerSeries R) : PowerSeries R :=
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  Algebra.norm (PowerSeries R) h

def trOp (p : ℕ) [hp : Fact p.Prime] (h : PowerSeries R) : PowerSeries R :=
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  Algebra.trace (PowerSeries R) (PowerSeries R) h

structure FrobLift (R : Type) [CommRing R] (p : ℕ) (σ : R ≃+* R) : Prop where
  dom : IsDomain R
  prime : Prime (p : R)
  complete : IsAdicComplete (Ideal.span {(p : R)}) R
  frob : ∀ x : R, σ x - x ^ p ∈ Ideal.span {(p : R)}
  perfect : ∀ x : R, ∃ y : R, y ^ p - x ∈ Ideal.span {(p : R)}

abbrev smap (σ : R ≃+* R) : PowerSeries R →+* PowerSeries R := PowerSeries.map (σ : R →+* R)

theorem hasSubst_pow (b : ℕ) : PowerSeries.HasSubst (((1 + PowerSeries.X : PowerSeries R) ^ b) - 1) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  simp only [map_sub, map_pow, map_add, map_one]
  erw [PowerSeries.constantCoeff_X]
  simp

def sb (b : ℕ) : PowerSeries R →ₐ[R] PowerSeries R := PowerSeries.substAlgHom (hasSubst_pow (R := R) b)

end GlobalTheory.Col

namespace GlobalTheory.Col
variable {R : Type} [CommRing R]

theorem FrobLift.witt (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    FrobLift (WittVector p k) p (WittVector.frobeniusEquiv p k) where
  dom := inferInstance
  prime := (WittVector.irreducible p).prime
  complete := WittVector.isAdicCompleteIdealSpanP
  frob := by
    intro x
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : WittVector.constantCoeff (WittVector.frobeniusEquiv p k x - x ^ p) = 0 := by
      rw [map_sub, map_pow]
      simp [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]
    exact this
  perfect := by
    intro x
    refine ⟨(WittVector.frobeniusEquiv p k).symm x, ?_⟩
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : WittVector.constantCoeff (((WittVector.frobeniusEquiv p k).symm x) ^ p - x) = 0 := by
      obtain ⟨y, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective x
      rw [RingEquiv.symm_apply_apply, map_sub, map_pow]
      simp [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]
    exact this

example (p : ℕ) [Fact p.Prime] : FrobLift (WittVector p (AlgebraicClosure (ZMod p))) p
    (WittVector.frobeniusEquiv p (AlgebraicClosure (ZMod p))) := FrobLift.witt p _

def padicToWitt (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p] : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

theorem padicHom_ext (p : ℕ) [Fact p.Prime] [IsHausdorff (Ideal.span {(p : R)}) R] (f g : ℤ_[p] →+* R) : f = g := by
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : R)}) inferInstance _ fun n => ?_
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[p]) + e * (p : ℤ_[p]) ^ n := by rw [he]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f e - g e, ?_⟩
  rw [hx]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

def trLev (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) : lev R p (m + 1) →+ lev R p m :=
  letI := (up (R := R) p m hm).toAlgebra
  (Algebra.trace (lev R p m) (lev R p (m + 1))).toAddMonoidHom

def levZeta (R : Type) [CommRing R] (p m : ℕ) : lev R p m := ev R p m (1 + PowerSeries.X)

theorem ev_cyc_self (p m : ℕ) : ev R p m (cyc R p m) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

theorem cyc_dvd_level (p m : ℕ) : cyc R p m ∣ (1 + PowerSeries.X : PowerSeries R) ^ (p ^ m) - 1 := by
  obtain ⟨s, hs⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one (p ^ m) R
  refine ⟨s.eval₂ PowerSeries.C (1 + PowerSeries.X), ?_⟩
  have := congrArg (Polynomial.eval₂ (PowerSeries.C (R := R)) (1 + PowerSeries.X)) hs
  rw [Polynomial.eval₂_mul] at this
  rw [cyc, ← this]
  simp

theorem coeffMap_cyc {S : Type} [CommRing S] (τ : R →+* S) (p m : ℕ) : PowerSeries.map τ (cyc R p m) = cyc S p m := by
  unfold cyc
  rw [Polynomial.hom_eval₂, ← Polynomial.map_cyclotomic (p ^ m) τ, Polynomial.eval₂_map]
  congr 1
  · ext a : 1; simp
  · simp

def levMap {S : Type} [CommRing S] (τ : R →+* S) (p m : ℕ) : lev R p m →+* lev S p m :=
  Ideal.Quotient.lift _ ((ev S p m).comp (PowerSeries.map τ)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, coeffMap_cyc, map_mul, ev_cyc_self, mul_zero])

theorem levMap_ev {S : Type} [CommRing S] (τ : R →+* S) (p m : ℕ) (h : PowerSeries R) :
    levMap τ p m (ev R p m h) = ev S p m (PowerSeries.map τ h) := rfl

theorem levMap_id (p m : ℕ) (x : lev R p m) : levMap (RingHom.id R) p m x = x := by
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levMap_ev, PowerSeries.map_id]; rfl

theorem levMap_comp {S U : Type} [CommRing S] [CommRing U] (τ : R →+* S) (υ : S →+* U) (p m : ℕ) (x : lev R p m) :
    levMap (υ.comp τ) p m x = levMap υ p m (levMap τ p m x) := by
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levMap_ev, levMap_ev, levMap_ev, PowerSeries.map_comp]; rfl

def levF (σ : R ≃+* R) (p m : ℕ) : lev R p m ≃+* lev R p m :=
  RingEquiv.ofRingHom (levMap (σ : R →+* R) p m) (levMap (σ.symm : R →+* R) p m)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← levMap_comp, RingEquiv.comp_symm, levMap_id]; rfl)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← levMap_comp, RingEquiv.symm_comp, levMap_id]; rfl)

theorem levF_ev (σ : R ≃+* R) (p m : ℕ) (h : PowerSeries R) : levF σ p m (ev R p m h) = ev R p m (smap σ h) := rfl

section Act
open Formalism.CohomologicalDescent.HeightDescentMinors (br act hasSubst_br_padic binomialSeriesSubOne_natCast binomialAction_comp_eq_mul binomialAction_binomialSeriesSubOne constantCoeff_binomialSeriesSubOne dvd_subst_self)

variable (p : ℕ) [hp : Fact p.Prime] [Algebra ℤ_[p] R]

def sbp (b : ℤ_[p]) : PowerSeries R →ₐ[R] PowerSeries R := PowerSeries.substAlgHom (hasSubst_br_padic p R b)

theorem sbp_apply (b : ℤ_[p]) (h : PowerSeries R) : sbp p b h = act p R b h := by
  rw [sbp, PowerSeries.coe_substAlgHom]; rfl

theorem sbp_one_add_X (b : ℤ_[p]) :
    sbp p b (1 + PowerSeries.X : PowerSeries R) = PowerSeries.binomialSeries R b := by
  rw [map_add, map_one, sbp, PowerSeries.substAlgHom_X, br]; ring

theorem sbp_nat (b : ℕ) : sbp (R := R) p (b : ℤ_[p]) = sb b := by
  unfold sbp sb
  congr 1
  exact binomialSeriesSubOne_natCast p R b

theorem sbp_one (h : PowerSeries R) : sbp p 1 h = h := by
  rw [sbp_apply]; exact (Formalism.CohomologicalDescent.HeightDescentMinors.action_laws_holds p R).2.2.1 h

theorem sbp_mul (b c : ℤ_[p]) (h : PowerSeries R) : sbp p (b * c) h = sbp p b (sbp p c h) := by
  rw [sbp_apply, sbp_apply, sbp_apply, binomialAction_comp_eq_mul, mul_comm]

theorem coeffMap_sbp {S : Type} [CommRing S] [Algebra ℤ_[p] S] (τ : R →+* S)
    (hτ : τ.comp (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] S) (b : ℤ_[p]) (h : PowerSeries R) :
    PowerSeries.map τ (sbp p b h) = sbp p b (PowerSeries.map τ h) := by
  rw [sbp_apply, sbp_apply, act, act]
  have := PowerSeries.map_subst (hasSubst_br_padic p R b) (h := τ) h
  refine Eq.trans this ?_
  congr 1
  change PowerSeries.map τ _ = _
  rw [br, br, map_sub, map_one]
  congr 1
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, PowerSeries.binomialSeries_coeff,
    Algebra.smul_def, Algebra.smul_def, mul_one, mul_one, ← hτ]
  rfl

theorem smap_sbp [IsHausdorff (Ideal.span {(p : R)}) R] (σ : R ≃+* R) (b : ℤ_[p]) (h : PowerSeries R) :
    smap σ (sbp p b h) = sbp p b (smap σ h) :=
  coeffMap_sbp p _ (padicHom_ext p _ _) b h

theorem ev_binomialSeries (m : ℕ) (b : ℤ_[p]) (n : ℕ) (hn : b - n ∈ Ideal.span {(p : ℤ_[p]) ^ m}) :
    ev R p m (PowerSeries.binomialSeries R b) = levZeta R p m ^ n := by
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hn
  have hb : b = (n : ℤ_[p]) + e * ((p ^ m : ℕ) : ℤ_[p]) := by push_cast; rw [he]; ring
  have h1 : br p R ((p ^ m : ℕ) : ℤ_[p]) ∣ br p R (e * ((p ^ m : ℕ) : ℤ_[p])) := by
    rw [← binomialAction_binomialSeriesSubOne]
    exact dvd_subst_self (hasSubst_br_padic p R _) (constantCoeff_binomialSeriesSubOne p R e)
  rw [binomialSeriesSubOne_natCast] at h1
  obtain ⟨s, hs⟩ := (cyc_dvd_level (R := R) p m).trans h1
  have h2 : PowerSeries.binomialSeries R (e * ((p ^ m : ℕ) : ℤ_[p])) = 1 + cyc R p m * s := by
    rw [← hs, br]; ring
  rw [hb, PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_nat, h2, map_mul, map_add, map_mul, ev_cyc_self,
    map_pow, levZeta]
  simp

omit hp [Algebra ℤ_[p] R] in

theorem cyclotomic_dvd_expand_of_coprime (N : ℕ) : ∀ n : ℕ, n ≠ 0 → n.Coprime N →
    Polynomial.cyclotomic N R ∣ Polynomial.expand R n (Polynomial.cyclotomic N R) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simp
  | prime q hq =>
    intro _ hc
    rw [Polynomial.cyclotomic_expand_eq_cyclotomic_mul hq ((Nat.Prime.coprime_iff_not_dvd hq).1 hc)]
    exact dvd_mul_left _ _
  | mul a b iha ihb =>
    intro h0 hc
    rw [Polynomial.expand_mul]
    exact (iha (left_ne_zero_of_mul h0) (Nat.Coprime.coprime_mul_right hc)).trans
      (_root_.map_dvd (Polynomial.expand R a) (ihb (right_ne_zero_of_mul h0) (Nat.Coprime.coprime_mul_left hc)))

theorem ev_sbp_cyc (m : ℕ) (b : ℤ_[p]ˣ) : ev R p m (sbp p (b : ℤ_[p]) (cyc R p m)) = 0 := by
  set n := (b : ℤ_[p]).appr (m + 1) with hn
  have h1 := PadicInt.appr_spec (m + 1) (b : ℤ_[p])
  rw [← hn] at h1
  have hnd : ¬ p ∣ n := by
    rintro ⟨c, hc⟩
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 h1
    have : (p : ℤ_[p]) ∣ (b : ℤ_[p]) := ⟨c + e * (p : ℤ_[p]) ^ m, by
      rw [hc] at he; push_cast at he; linear_combination -he⟩
    exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit this b.isUnit)
  have h2 : (b : ℤ_[p]) - n ∈ Ideal.span {(p : ℤ_[p]) ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ m)) h1
  obtain ⟨s, hs⟩ := cyclotomic_dvd_expand_of_coprime (R := R) (p ^ m) n (by rintro h; exact hnd (h ▸ dvd_zero p))
    (Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd).symm)
  have h3 : ∀ P : R[X], ev R p m (sbp p (b : ℤ_[p]) (P.eval₂ PowerSeries.C (1 + PowerSeries.X))) =
      ev R p m ((Polynomial.expand R n P).eval₂ PowerSeries.C (1 + PowerSeries.X)) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add f g hf hg => simp only [Polynomial.eval₂_add, map_add, hf, hg]
    | monomial k a =>
      have hC : sbp p (b : ℤ_[p]) (PowerSeries.C a : PowerSeries R) = PowerSeries.C a := (sbp p (b : ℤ_[p])).commutes a
      rw [Polynomial.expand_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, map_mul, map_pow,
        sbp_one_add_X, hC, map_mul, map_mul, map_pow, map_pow, ev_binomialSeries p m _ n h2, ← pow_mul, mul_comm n k]
      rfl
  have h4 := h3 (Polynomial.cyclotomic (p ^ m) R)
  rw [hs, Polynomial.eval₂_mul, map_mul] at h4
  exact h4.trans (by rw [show Polynomial.eval₂ PowerSeries.C (1 + PowerSeries.X) (Polynomial.cyclotomic (p ^ m) R) = cyc R p m from rfl, ev_cyc_self, zero_mul])

def levActHom (m : ℕ) (b : ℤ_[p]ˣ) : lev R p m →ₐ[R] lev R p m :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (sbp p (b : ℤ_[p]))) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have h0 := ev_sbp_cyc (R := R) p m b
    rw [AlgHom.comp_apply, map_mul (sbp p (b : ℤ_[p])), Ideal.Quotient.mkₐ_eq_mk, map_mul (Ideal.Quotient.mk _), h0, mul_zero])

def levAct (m : ℕ) : ℤ_[p]ˣ →* (lev R p m ≃ₐ[R] lev R p m) :=
  (AlgEquiv.algHomUnitsEquiv R (lev R p m)).toMonoidHom.comp (MonoidHom.toHomUnits
    { toFun := levActHom p m
      map_one' := AlgHom.ext fun x => by
        obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
        change ev R p m (sbp p ((1 : ℤ_[p]ˣ) : ℤ_[p]) h) = ev R p m h
        rw [Units.val_one, sbp_one]
      map_mul' := fun b c => AlgHom.ext fun x => by
        obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
        change ev R p m (sbp p ((b * c : ℤ_[p]ˣ) : ℤ_[p]) h) = ev R p m (sbp p (b : ℤ_[p]) (sbp p (c : ℤ_[p]) h))
        rw [Units.val_mul, sbp_mul] })

theorem levAct_ev (m : ℕ) (b : ℤ_[p]ˣ) (h : PowerSeries R) :
    levAct p m b (ev R p m h) = ev R p m (sbp p (b : ℤ_[p]) h) := rfl

theorem levF_levAct [IsHausdorff (Ideal.span {(p : R)}) R] (σ : R ≃+* R) (m : ℕ) (b : ℤ_[p]ˣ) (x : lev R p m) :
    levF σ p m (levAct p m b x) = levAct p m b (levF σ p m x) := by
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levAct_ev, levF_ev, levF_ev, levAct_ev, smap_sbp]

example : sbp p (-1) (1 + PowerSeries.X : PowerSeries R) * (1 + PowerSeries.X) = 1 := by
  have h : (1 + PowerSeries.X : PowerSeries R) = PowerSeries.binomialSeries R ((1 : ℕ) : ℤ_[p]) := by
    rw [PowerSeries.binomialSeries_nat, pow_one]
  rw [sbp_one_add_X, h, ← PowerSeries.binomialSeries_add]
  simpa using (PowerSeries.binomialSeries_nat (R := ℤ_[p]) (A := R) 0)

end Act

example (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (m : ℕ) (b : ℤ_[p]ˣ)
    (x : lev (WittVector p k) p m) :
    letI := (padicToWitt p k).toAlgebra
    levF (WittVector.frobeniusEquiv p k) p m (levAct p m b x) = levAct p m b (levF (WittVector.frobeniusEquiv p k) p m x) :=
  letI := (padicToWitt p k).toAlgebra
  haveI := (FrobLift.witt p k).complete
  levF_levAct p _ m b x

example : dd (1 + PowerSeries.X : PowerSeries R) = 1 + PowerSeries.X := by simp [dd]

example : cyc R 2 1 = PowerSeries.X + 2 := by
  simp [cyc, Polynomial.cyclotomic_two]; ring

end GlobalTheory.Col
