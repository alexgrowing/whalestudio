import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LogLowOrderOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BalOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

variable {S : Type} [CommRing S] {d : ℕ}

theorem jet_subst_pair_mk {κ' : Type} (m : ℕ) (u v : Fin d → MvPolynomial κ' S) (P : MvPolynomial (Fin 2 × Fin d) S) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2)
        (Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1))
        (ev2 P (fun j => u j - C (constantCoeff (u j))) (fun j => v j - C (constantCoeff (v j)))) := by
  have hf : (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2 -
      C (constantCoeff ((![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2))) =
      fun p : Fin 2 × Fin d => (![fun j => u j - C (constantCoeff (u j)), fun j => v j - C (constantCoeff (v j))] :
        Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2 := by
    funext p
    rcases p with ⟨k, j⟩
    fin_cases k <;> rfl
  rw [jetSubstP_mk, hf]
  rfl

theorem X_sub_cc {n : ℕ} (k : Fin n) :
    (fun j => (X (k, j) : MvPolynomial (Fin n × Fin d) S) - C (constantCoeff (X (k, j) : MvPolynomial (Fin n × Fin d) S))) =
      xs S d k := by
  funext j
  simp [xs]

theorem isUnit_coeff_zero {m : ℕ} {P : MvPolynomial (Fin 2 × Fin d) S} (U : (Jet S (Fin 2 × Fin d) m)ˣ)
    (hP : Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) P = U) : IsUnit (coeff 0 P) := by
  have hker : ∀ a ∈ orig S (Fin 2 × Fin d) ^ (m + 1),
      (constantCoeff : MvPolynomial (Fin 2 × Fin d) S →+* S) a = 0 := by
    intro a ha
    have h1 : orig S (Fin 2 × Fin d) ^ (m + 1) ≤ orig S (Fin 2 × Fin d) :=
      Ideal.pow_le_self (Nat.succ_ne_zero m)
    have h2 : orig S (Fin 2 × Fin d) ≤
        RingHom.ker (constantCoeff : MvPolynomial (Fin 2 × Fin d) S →+* S) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    exact h2 (h1 ha)
  let φ := Ideal.Quotient.lift _ (constantCoeff : MvPolynomial (Fin 2 × Fin d) S →+* S) hker
  have hφP : φ (Ideal.Quotient.mk _ P) = coeff 0 P := Ideal.Quotient.lift_mk _ _ _
  have hu : IsUnit (φ (U : Jet S (Fin 2 × Fin d) m)) := U.isUnit.map φ
  rw [← hP, hφP] at hu
  exact hu

theorem bilL_neg [Algebra ℚ S] (G : FGLaw S d) (c : Fin d → Fin d → S) : bilL G (-c) = -bilL G c := by
  simp only [bilL, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

section Main

variable [Algebra ℚ S]

theorem psIn_law_sub_mem (G : FGLaw S d) {m : ℕ} (hm : 1 ≤ m) (i : Fin d) :
    psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i) - C (constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i))) - (xs S d 0 i + xs S d 1 i) ∈
      Io S (Fin 3 × Fin d) ^ 2 := by
  have hc : constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i)) = 0 := by rw [FBIdPh.cc_psIn]; exact G.const i
  have hr : (rename fun p : Fin 2 × Fin d => (((![0, 1] : Fin 2 → Fin 3) p.1), p.2) :
      MvPolynomial (Fin 2 × Fin d) S →ₐ[S] MvPolynomial (Fin 3 × Fin d) S) =
      aeval (fun p : Fin 2 × Fin d => (X (((![0, 1] : Fin 2 → Fin 3) p.1), p.2) : MvPolynomial (Fin 3 × Fin d) S)) := by
    ext p; simp
  have e : psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i) - C (constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i))) - (xs S d 0 i + xs S d 1 i) =
      aeval (fun p : Fin 2 × Fin d => (X (((![0, 1] : Fin 2 → Fin 3) p.1), p.2) : MvPolynomial (Fin 3 × Fin d) S))
        (psTrunc m (G.F i) - (X ((0 : Fin 2), i) + X ((1 : Fin 2), i))) := by
    rw [hc, map_zero, sub_zero, psIn, hr, map_sub, map_add, aeval_X, aeval_X]
    rfl
  rw [e]
  exact aeval_mem_pow _ (fun p => Ideal.subset_span ⟨_, rfl⟩) 2 (psTrunc_law_sub_mem G hm i)

private theorem constantCoeff_germEvalPair_eq_zero_lemma {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    constantCoeff (ev2 h u v) = constantCoeff h := by
  unfold ev2
  induction h using MvPolynomial.induction_on
  · simp
  · simp only [map_add, *]
  · rename_i p n _
    rcases n with ⟨i, j⟩
    fin_cases i <;> simp [hu, hv]

theorem const_one' {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hfF : ∀ i, fF i ∈ Io S (Fin 3 × Fin d))
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
  have hIo : ∀ {σ : Type} (f : MvPolynomial σ S), f ∈ Io S σ → constantCoeff f = 0 := by
    intro σ f hf
    have h2 : Io S σ ≤ RingHom.ker (constantCoeff : MvPolynomial σ S →+* S) := by
      unfold Io idealOfVars
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    exact h2 hf
  have hfF0 : ∀ i, constantCoeff (fF i) = 0 := fun i => hIo _ (hfF i)
  have hxs : ∀ (k : Fin 3) (j : Fin d), constantCoeff (xs S d k j) = 0 := by
    intro k j
    simp [xs]
  have hpow : Io S (Fin 3 × Fin d) ^ (m + 1) ≤ Io S (Fin 3 × Fin d) :=
    Ideal.pow_le_self (Nat.succ_ne_zero m)
  have h0 := hIo _ (hpow hph1)
  rw [map_sub, map_mul, constantCoeff_germEvalPair_eq_zero_lemma P fF (xs S d 2) hfF0 (hxs 2),
    constantCoeff_germEvalPair_eq_zero_lemma P (xs S d 0) (xs S d 2) (hxs 0) (hxs 2),
    constantCoeff_germEvalPair_eq_zero_lemma P (xs S d 1) (xs S d 2) (hxs 1) (hxs 2)] at h0
  have hu' : IsUnit (constantCoeff P) := hu
  have hc : constantCoeff P = 1 := by
    have h3 : constantCoeff P * (1 - constantCoeff P) = 0 := by
      rw [mul_sub, mul_one]
      exact h0
    exact (sub_eq_zero.1 ((hu'.mul_right_eq_zero).1 h3)).symm
  rw [pow_one]
  unfold Io idealOfVars
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro e he
  have hne : e ≠ 0 := by
    rintro rfl
    have hc' : coeff 0 P = 1 := hc
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_zero_one, hc', sub_self] at he
    exact he rfl
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finsupp.ext hcon)
  exact ⟨i, Set.mem_univ _, hi⟩

theorem fixExp (G : FGLaw S d) {O : Type} (act : O → Fin d → PS S 1 d)
    (hact : ∀ a i, MvPowerSeries.constantCoeff (act a i) = 0) (bar : O → O) (m : ℕ)
    (U : (Jet S (Fin 2 × Fin d) m)ˣ)
    (h1 : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m))
    (hs : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = U)
    (hb : ∀ a, jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m)) :
    ∃ c : Fin d → Fin d → S, (∀ i l, c i l = c l i) ∧
      (∀ a, Matrix.transpose (dLin (act a)) * Matrix.of c = Matrix.of c * dLin (act (bar a))) ∧
      (U : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL G c)) := by
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective (U : Jet S (Fin 2 × Fin d) m)
  have hu := isUnit_coeff_zero U hP
  set fF : Fin d → MvPolynomial (Fin 3 × Fin d) S :=
    fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F j) - C (constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F j))) with hfFdef
  have hfF : ∀ i, fF i ∈ Io S (Fin 3 × Fin d) := fun i => sub_C_mem _

  have poly1 : ∀ (V : Jet S (Fin 2 × Fin d) m) (Q : MvPolynomial (Fin 2 × Fin d) S),
      Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) Q = V →
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) V =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) V *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) V →
      ev2 Q fF (xs S d 2) - ev2 Q (xs S d 0) (xs S d 2) * ev2 Q (xs S d 1) (xs S d 2) ∈ Io S (Fin 3 × Fin d) ^ (m + 1) := by
    intro V Q hQ h
    rw [← hQ, jet_subst_pair_mk, jet_subst_pair_mk, jet_subst_pair_mk, ← map_mul, mk_eq_iff,
      X_sub_cc (k := (2 : Fin 3)), X_sub_cc (k := (0 : Fin 3)), X_sub_cc (k := (1 : Fin 3))] at h
    exact h
  have polys : ∀ (V : Jet S (Fin 2 × Fin d) m) (Q : MvPolynomial (Fin 2 × Fin d) S),
      Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) Q = V →
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) V = V →
      ev2 Q (xs S d 1) (xs S d 0) - Q ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
    intro V Q hQ h
    rw [← hQ, jet_subst_pair_mk, mk_eq_iff, X_sub_cc (k := (1 : Fin 2)), X_sub_cc (k := (0 : Fin 2))] at h
    exact h
  have hph1 := poly1 _ P hP h1
  have hsym := polys _ P hP hs
  by_cases hm2 : 2 ≤ m
  · have hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2 :=
      fun i => psIn_law_sub_mem G (by omega) i
    obtain ⟨h2, h3, hsymB⟩ := lead_bil hm2 fF hF hph1 hsym hu
    set B : Fin d → Fin d → S := fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1)) with hBdef
    have hbalB : ∀ a, Matrix.transpose (Matrix.of (dLin (act a))) * Matrix.of B =
        Matrix.of B * Matrix.of (dLin (act (bar a))) := by
      intro a
      have hba := hb a
      rw [← hP, jet_subst_pair_mk, jet_subst_pair_mk, mk_eq_iff, X_sub_cc (k := (1 : Fin 2)), X_sub_cc (k := (0 : Fin 2))]
        at hba
      exact CIndFrExp2b.bal_of hm2 B (dLin (act a)) (dLin (act (bar a))) h2 h3 _ _
        (psIn_act_sub_mem (act a) (hact a) (by omega) 0) (psIn_act_sub_mem (act (bar a)) (hact (bar a)) (by omega) 1)
        hba
    refine ⟨-B, fun i l => by show -B i l = -B l i; exact congrArg Neg.neg (hsymB i l), fun a => ?_, ?_⟩
    · have := hbalB a
      show Matrix.transpose (dLin (act a)) * (-Matrix.of B) = (-Matrix.of B) * dLin (act (bar a))
      rw [Matrix.mul_neg, Matrix.neg_mul]
      exact congrArg Neg.neg this
    · set Pinv : MvPolynomial (Fin 2 × Fin d) S := psTrunc m (expP (-bilL G B)) with hPinv
      have hEinv : Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) Pinv = psJet m (expP (-bilL G B)) := rfl
      have hQ : Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) (P * Pinv) =
          (U : Jet S (Fin 2 × Fin d) m) * psJet m (expP (-bilL G B)) := by rw [map_mul, hP, hEinv]
      have hph1Q := poly1 _ (P * Pinv) hQ (by
        rw [map_mul, map_mul, map_mul, h1, twist_mul_first_argument_jet G B m]; ring)
      have hsymQ := polys _ (P * Pinv) hQ (by rw [map_mul, hs, twist_sym_jet G B (fun i l => hsymB i l) m])
      have hPi : Pinv - (1 - bil B) ∈ Io S (Fin 2 × Fin d) ^ 3 := by
        have e2 : psTrunc 2 (expP (-bilL G B)) = 1 - bil B := by
          rw [← bilL_neg, CIndFrExp2a.psTrunc_two_twist]
          simp [bil, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        have := psTrunc_sub_mem (expP (-bilL G B)) (k := 2) hm2
        rwa [e2] at this
      have hQ3 : P * Pinv - 1 ∈ Io S (Fin 2 × Fin d) ^ 3 := by
        have e : P * Pinv - 1 = (P - 1 - bil B) * Pinv + (1 + bil B) * (Pinv - (1 - bil B)) - bil B * bil B := by ring
        rw [e]
        refine sub_mem (add_mem (Ideal.mul_mem_right _ _ h3) (Ideal.mul_mem_left _ _ hPi)) ?_
        have hbb : bil B * bil B ∈ Io S (Fin 2 × Fin d) ^ (2 + 2) := by
          rw [pow_add]; exact Ideal.mul_mem_mul (bil_mem B) (bil_mem B)
        exact Ideal.pow_le_pow_right (by omega) hbb
      have hone := eq_one_of_cube fF hF hph1Q hsymQ hQ3
      have hUE : (U : Jet S (Fin 2 × Fin d) m) * psJet m (expP (-bilL G B)) = 1 := by
        rw [← hQ, ← map_one (Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)))]
        exact (mk_eq_iff m _ _).2 hone
      have hinv : (psJet m (expP (-bilL G (-B))) : Jet S (Fin 2 × Fin d) m) * psJet m (expP (-bilL G B)) = 1 := by
        have := (twU G (-B) m).val_inv
        rw [twU_val] at this
        have e : ((twU G (-B) m)⁻¹ : (Jet S (Fin 2 × Fin d) m)ˣ).val = psJet m (expP (-bilL G B)) := by
          show psJet m (expP (-bilL G (-(-B)))) = _
          rw [neg_neg]
        rw [← e]; exact this
      calc (U : Jet S (Fin 2 × Fin d) m)
          = U * (psJet m (expP (-bilL G (-B))) * psJet m (expP (-bilL G B))) := by rw [hinv, mul_one]
        _ = (U * psJet m (expP (-bilL G B))) * psJet m (expP (-bilL G (-B))) := by ring
        _ = psJet m (expP (-bilL G (-B))) := by rw [hUE, one_mul]
  · refine ⟨0, fun _ _ => rfl, fun a => by simp, ?_⟩
    have hP1 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
      have h01 := const_one' fF hfF hph1 hu
      rcases Nat.lt_or_ge m 1 with hm0 | hm1
      · have : m = 0 := by omega
        subst this; exact h01
      · have hm1' : m = 1 := by omega
        subst hm1'
        exact stepNo2 le_rfl le_rfl (by omega) fF (fun i => psIn_law_sub_mem G le_rfl i) hph1 hsym h01
    have hU1 : (U : Jet S (Fin 2 × Fin d) m) = 1 := by
      rw [← hP, ← map_one (Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)))]
      exact (mk_eq_iff m _ _).2 hP1
    rw [hU1, twist_zero, FBIdJet.psJet_one]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
