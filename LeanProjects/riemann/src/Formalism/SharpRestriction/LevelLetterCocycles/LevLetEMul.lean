import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.DivLevR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}

theorem letE_mem (a : ZMod n) : (letE a : LetA O n) ∈ W.AΔ := by
  intro δ _
  funext i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE,
    Pi.single_apply]
  split_ifs <;> simp

theorem letE_idem (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

theorem lev_letE' (a : ZMod n) (ζ : LL) : W.lev a ζ (letE a : LetA O n) = 1 := by
  have h : W.lev a ζ (1 - letE a) = 0 := W.lev_letter a ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem lev_letE_mul (a : ZMod n) (ζ : LL) (g : LetA O n) :
    W.lev a ζ ((letE a : LetA O n) * g) = W.lev a ζ g := by
  rw [map_mul, lev_letE', one_mul]

theorem lev_q_X (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ R : PowerSeries LL, constantCoeff R ≠ 0 ∧ W.lev a ζ W.q = X * R := by
  have hζ1 : IsPrimitiveRoot ζ (PD.p ^ 1) := by rwa [pow_one]
  obtain ⟨E, hE0, hED, hE⟩ := W.lev_π a ζ ⟨1, hζ1⟩
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q, W.q₀_def]
  set F : PowerSeries LL := C ζ * E with hF
  have hL := congrArg (W.lev a ζ) hq
  simp only [map_mul, map_sub, map_pow, map_add, map_one] at hL
  rw [hE] at hL
  set P := W.lev a ζ letπ with hP
  set Lq := W.lev a ζ W.q with hLq
  have hP0 : constantCoeff P = ζ - 1 := by
    have := congrArg constantCoeff hE
    rw [map_add, map_one, map_mul, constantCoeff_C, hE0, mul_one] at this
    linear_combination this
  have hζne : ζ ≠ 1 := hζ.ne_one PD.hp.one_lt
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζne

  have h0 := congrArg constantCoeff hL
  rw [map_mul, map_sub, map_pow, map_one, hF, map_mul, constantCoeff_C, hE0, mul_one, hζp,
    sub_self, hP0] at h0
  have hLq0 : constantCoeff Lq = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hsub
    · exact h
  obtain ⟨R, hR⟩ := X_dvd_iff.mpr hLq0
  refine ⟨R, ?_, hR⟩
  intro hR0

  have hD : derivative LL F = F := by
    rw [hF, Derivation.leibniz, hED]
    simp
  have hd := congrArg (fun f => constantCoeff (derivative LL f)) hL
  rw [map_sub, Derivation.leibniz_pow, hD, Derivation.map_one_eq_zero, sub_zero] at hd
  obtain ⟨R', hR'⟩ := X_dvd_iff.mpr hR0
  have hLq2 : Lq = X ^ 2 * R' := by rw [hR, hR']; ring
  rw [hLq2, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow] at hd
  simp only [smul_eq_mul, map_add, map_mul, map_pow, map_nsmul, constantCoeff_X] at hd
  have hF0 : constantCoeff F = ζ := by rw [hF, map_mul, constantCoeff_C, hE0, mul_one]
  rw [hF0] at hd
  have hpζ : (PD.p : LL) * ζ ^ PD.p = 0 := by
    have e : (PD.p - 1) + 1 = PD.p := Nat.sub_add_cancel PD.hp.one_le
    have := hd
    simp only [nsmul_eq_mul] at this
    rw [← pow_succ, e] at this
    rw [← this]
    simp
  rw [hζp, mul_one] at hpζ
  have h2 := W.v_l
  rw [hpζ, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

section Div

variable [IsDomain O]

theorem lev_qP_X (hR : ToolsR.RingP W) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ S : PowerSeries LL, constantCoeff S ≠ 0 ∧ W.lev a ζ (qP W) = X * S := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [ToolsR.eat_qP] at hw
  obtain ⟨R, hR0, hRq⟩ := lev_q_X (W := W) a ζ hζ
  have hLw : IsUnit (W.lev a ζ (w : LetA O n)) := w.isUnit.map _
  have hcw : constantCoeff (W.lev a ζ (w : LetA O n)) ≠ 0 := (hLw.map constantCoeff).ne_zero
  have e : X * R = W.lev a ζ (w : LetA O n) * W.lev a ζ (qP W) := by rw [← hRq, hw, map_mul]
  have h0 : constantCoeff (W.lev a ζ (qP W)) = 0 := by
    have := congrArg constantCoeff e
    rw [map_mul, map_mul, constantCoeff_X, zero_mul] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hcw
    · exact h
  obtain ⟨S, hS⟩ := X_dvd_iff.mpr h0
  refine ⟨S, ?_, hS⟩
  rw [hS, mul_left_comm] at e
  have e2 := mul_left_cancel₀ X_ne_zero e
  intro hS0
  apply hR0
  rw [e2, map_mul, hS0, mul_zero]

variable [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem step (hR : ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (g : LetA O n) (hg : g ∈ W.AΔ) (h0 : coeff 0 (W.lev a ζ g) = 0) :
    ∃ h ∈ W.AΔ, (letE a : LetA O n) * g = qP W * h := by
  obtain ⟨f, hf, -⟩ := hR.2.1 g hg
  set I : Ideal O := Ideal.span {((PD.p : ℕ) : O)} with hIdef
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hIdef, Ideal.span_singleton_eq_top]; exact hpu)
  have hpI : Ideal.Quotient.mk I ((PD.p : ℕ) : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  set D : PowerSeries O := X + C ((PD.p : ℕ) : O) with hD
  have hmap : D.map (Ideal.Quotient.mk I) = X := by
    rw [hD, map_add, map_X, map_C, hpI, map_zero, add_zero]
  have hord : (D.map (Ideal.Quotient.mk I)).order.toNat = 1 := by rw [hmap, order_X]; rfl
  have hdiv : D.IsWeierstrassDivisorAt I := by
    unfold IsWeierstrassDivisorAt
    rw [hord, hD, map_add, coeff_C, if_neg one_ne_zero, add_zero]
    simp [coeff_X]
  have HD := hdiv.isWeierstrassDivisionAt_div_mod (f := f a)
  set H := hdiv.div (f a)
  set r := hdiv.mod (f a)
  have hdeg : r.degree < 1 := by
    have := HD.degree_lt
    rw [hord] at this
    exact_mod_cast this
  have heq : f a = D * H + (r : PowerSeries O) := HD.eq_mul_add
  have hr : (r : PowerSeries O) = r.coeff 0 • (1 : PowerSeries O) := by
    have hle : r.degree ≤ 0 := by
      exact Nat.WithBot.lt_one_iff_le_zero.mp hdeg
    conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hle]
    rw [Polynomial.coe_C, smul_eq_C_mul, mul_one]
  have hDn : D = X + ((PD.p : ℕ) : PowerSeries O) := by rw [hD, map_natCast]
  have ha0 : constantCoeff W.π₀₁ = 0 := ToolsR.π₀₁_cc hR
  have hs0 := HasSubst.of_constantCoeff_zero' ha0
  have hga : g a = (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) * subst W.π₀₁ H +
      r.coeff 0 • (1 : PowerSeries O) := by
    rw [hf a]
    change subst W.π₀₁ (f a) = _
    rw [heq, hr, hDn, ← coe_substAlgHom hs0, map_add, map_mul, map_add, substAlgHom_X, map_natCast,
      map_smul, map_one]
  set h : LetA O n := Pi.single a (subst W.π₀₁ H) with hh
  have key : (letE a : LetA O n) * g = qP W * h + r.coeff 0 • (letE a : LetA O n) := by
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, hh, letE, Pi.single_eq_same, one_mul,
        hga, qP, LocWach.π₀, Pi.natCast_apply]
    · simp [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, hh, letE, Pi.single_eq_of_ne hi]
  obtain ⟨S, -, hS⟩ := lev_qP_X hR a ζ hζ
  have hL := congrArg (fun x => coeff 0 (W.lev a ζ x)) key
  simp only [map_add, map_mul, map_smul, lev_letE', hS, one_mul] at hL
  rw [h0, mul_assoc, coeff_zero_X_mul, zero_add, coeff_smul, coeff_zero_eq_constantCoeff,
    map_one, Algebra.smul_def, mul_one] at hL
  have hc : r.coeff 0 = 0 := hinj (by rw [← hL, map_zero])
  rw [hc, zero_smul, add_zero] at key
  refine ⟨h, ?_, key⟩
  refine ToolsR.cancel_AΔ (ToolsR.qP_AΔ hR) (fun i hq => by
    have := congrArg constantCoeff hq
    simp only [qP, Pi.add_apply, LocWach.π₀, Pi.natCast_apply, map_add, ToolsR.π₀₁_cc hR, map_natCast,
      zero_add, map_zero] at this
    have h1 : ((PD.p : ℕ) : LL) = 0 := by
      rw [← map_natCast (algebraMap O LL), this, map_zero]
    have h2 := W.v_l
    rw [h1, AddValuation.map_zero] at h2
    exact absurd h2 (by simp)) ?_
  rw [← key]
  exact W.AΔ.mul_mem (letE_mem a) hg

theorem divLev_of (hR : ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) : LevC.DivLev (W := W) a ζ := by
  intro g hg k
  induction k generalizing g with
  | zero =>
    intro _
    exact ⟨letE a * g, W.AΔ.mul_mem (letE_mem a) hg, by simp⟩
  | succ k ih =>
    intro hv
    obtain ⟨S, hS0, hLqP⟩ := lev_qP_X hR a ζ hζ
    obtain ⟨h1, h1m, e1⟩ := step hR hpu hinj a ζ hζ g hg (hv 0 (Nat.succ_pos _))
    have hLg : W.lev a ζ g = X * (S * W.lev a ζ h1) := by
      rw [← lev_letE_mul, e1, map_mul, hLqP, mul_assoc]
    have hv1 : ∀ j < k, coeff j (W.lev a ζ h1) = 0 := by
      have hd : X ^ (k + 1) ∣ X * (S * W.lev a ζ h1) := by
        rw [← hLg]
        exact X_pow_dvd_iff.mpr hv
      rw [pow_succ', mul_dvd_mul_iff_left X_ne_zero] at hd
      have hSu : IsUnit S := by
        rw [isUnit_iff_constantCoeff]
        exact isUnit_iff_ne_zero.mpr hS0
      exact X_pow_dvd_iff.mp ((hSu.dvd_mul_left).mp hd)
    obtain ⟨h2, h2m, e2⟩ := ih h1 h1m hv1
    refine ⟨h2, h2m, ?_⟩
    have hps : ps W 0 = qP W := by
      rw [ps, pow_zero]
      rfl
    rw [hps, ← letE_idem a, mul_assoc, e1, mul_left_comm, e2, hps, ← mul_assoc, ← pow_succ']

end Div

end Formalism.MainNotions.UnusedSlot80.DivLevR
