import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SubstOfLog

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem HD.map_frobenius_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map (σ.comp σ) lam) (MvPowerSeries.map (σ.comp σ) Φ)
      (PowerSeries.map (σ.comp σ) A) a := by
  have hτa : (σ.comp σ) a = a := h.a_sq
  have e := congrArg (PowerSeries.map (σ.comp σ)) h.Alog
  rw [map_mul, PowerSeries.map_C, hτa] at e
  have e2 := congrArg (MvPowerSeries.map (σ.comp σ)) h.log
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, h.a_ne, h.a_sq⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, map_zero]
  · rw [PowerSeries.coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact (integralMv_iff_divBy_one Φ).mp h.Φint d
  · have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    unfold atX atY at e2 ⊢
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0), map_add,
      PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), MvPowerSeries.map_X,
      MvPowerSeries.map_X] at e2
    exact e2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.A0, map_zero]
  · unfold IntegralPS
    intro n
    rw [PowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact h.Aint n
  · have e' : MvPowerSeries.map (σ.comp σ) (lam.subst A) = C a * PowerSeries.map (σ.comp σ) lam := e
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h.A0)] at e'
    exact e'

theorem HD.map_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by
  induction i with
  | zero =>
    simp only [pow_zero, RingHom.one_def, MvPowerSeries.map_id, PowerSeries.map_id, RingHom.id_apply]
    exact h
  | succ i ih =>
    have h1 := HD.map_frobenius_sq hF ih
    simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
      RingHom.comp_apply]
    exact h1

theorem honF_subst_subst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem honF_integral_subst {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS (f.subst g) :=
  (integralPS_iff_mv _).mpr (integralMv_subst hf hg0 ((integralPS_iff_mv g).mp hg))

theorem hon_mu (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by
  have hl := hF.prime
  have hl1 := hF.norm_l
  have hlam' : IntegralPS (derivative K lam) := h.toLawD.deriv_integral
  have h' := h.map_frobenius_sq hF
  have Hh : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh1.g0
  have HΦ' : PowerSeries.HasSubst (MvPowerSeries.map (σ.comp σ) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h'.Φ0
  have HA' : PowerSeries.HasSubst (PowerSeries.map (σ.comp σ) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h'.A0
  have HA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' h.A0
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hXq0 : constantCoeff ((X : PowerSeries K) ^ (l ^ 2)) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have HXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXq0
  have hX0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have HX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (hX0 i)
  have hp0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (![atX hh, atY hh] i) = 0 := by
    intro i
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 0) hh hh1.g0
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 1) hh hh1.g0
  have hpI : ∀ i : Fin 2, IntegralMv (![atX hh, atY hh] i) := by
    intro i
    fin_cases i
    · exact integralMv_subst hh1.gInt (hX0 0) (integralMv_X 0)
    · exact integralMv_subst hh1.gInt (hX0 1) (integralMv_X 1)
  have Hp : MvPowerSeries.HasSubst ![atX hh, atY hh] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hp0
  refine ⟨⟨PowerSeries.constantCoeff_subst_eq_zero hh1.g0 lam h.lam0, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [derivative_subst Hh]
    exact integralPS_mul (honF_integral_subst hlam' hh1.g0 hh1.gInt) (integralPS_derivative hh1.gInt)
  · have key := qls hl hl1 lam h.lam0 hlam' (hh.subst (MvPowerSeries.map (σ.comp σ) Φ))
      (Φ.subst ![atX hh, atY hh])
      (PowerSeries.constantCoeff_subst_eq_zero h'.Φ0 hh hh1.g0)
      (MvPowerSeries.constantCoeff_subst_eq_zero Hp hp0 h.Φ0)
      (integralMv_subst hh1.gInt h'.Φ0 h'.Φint) (integralMv_subst2 h.Φint hp0 hpI) hh1.add
    have ex : atX (lam.subst hh) = lam.subst (atX hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 0) lam
    have ey : atY (lam.subst hh) = lam.subst (atY hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 1) lam
    have ax : (atX lam).subst ![atX hh, atY hh] = lam.subst (atX hh) :=
      (honF_subst_subst lam (hX0 0) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have ay : (atY lam).subst ![atX hh, atY hh] = lam.subst (atY hh) :=
      (honF_subst_subst lam (hX0 1) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have e1 : lam.subst (Φ.subst ![atX hh, atY hh]) = atX (lam.subst hh) + atY (lam.subst hh) := by
      rw [ex, ey, ← honF_subst_subst lam h.Φ0 Hp, h.log, MvPowerSeries.subst_add Hp, ax, ay]
    rw [e1] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HΦ', sub_sub]
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' (hh.subst (PowerSeries.map (σ.comp σ) A))
      (A.subst hh) (PowerSeries.constantCoeff_subst_eq_zero h'.A0 hh hh1.g0)
      (PowerSeries.constantCoeff_subst_eq_zero hh1.g0 A h.A0)
      (honF_integral_subst hh1.gInt h'.A0 h'.Aint) (honF_integral_subst h.Aint hh1.g0 hh1.gInt) hh1.eig
    rw [← PowerSeries.subst_comp_subst_apply HA Hh, h.Alog, PowerSeries.subst_mul Hh,
      PowerSeries.subst_C] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HA']
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' e (hh.subst ((X : PowerSeries K) ^ (l ^ 2))) he0
      (PowerSeries.constantCoeff_subst_eq_zero hXq0 hh hh1.g0) he
      (honF_integral_subst hh1.gInt hXq0 (integralPS_pow integralPS_X _)) hh2
    rw [hlog] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HXq]
    exact key
  · rw [Formalism.LT.PadicP.coeff_one_subst lam hh h.lam0 hh1.g0, h.lam1, one_mul]

theorem lemmaQ_tw (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) {D : PowerSeries K}
    (hD : QCls l (MvPowerSeries.map ((σ.comp σ) ^ i) Φ) (PowerSeries.map ((σ.comp σ) ^ i) A) a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
        (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * PowerSeries.map ((σ.comp σ) ^ i) lam
        - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  obtain ⟨Dp, hDp, hdiv⟩ := lemmaQ hF (HD.map_sq hF h i) hD
  refine ⟨Dp, ?_, hdiv⟩
  simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
    RingHom.comp_apply]
  exact hDp

theorem hon_series (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : ℕ → K, ‖c 0‖ = 1 ∧ (∀ i, ‖c i‖ ≤ 1) ∧ ∀ N : ℕ, ∃ R : PowerSeries K,
      constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam).subst
              ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1)))) := by
  obtain ⟨hh, hhom, hdiv, hc1⟩ := hon_shape hF h he0 he hlog
  obtain ⟨hQ, hmod, hcoef⟩ := hon_mu hF h he0 he hlog hhom hdiv
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hQ' : QCls l (MvPowerSeries.map ((σ.comp σ) ^ (0 + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (0 + 1)) A) a (lam.subst hh) := by
    simpa using hQ

  let seq : (i : ℕ) → {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D} := fun i =>
    Nat.rec (motive := fun i => {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D}) ⟨lam.subst hh, hQ'⟩
      (fun i D => ⟨Classical.choose (lemmaQ_tw hF h (i + 1) D.2),
        (Classical.choose_spec (lemmaQ_tw hF h (i + 1) D.2)).1⟩) i
  have hstep : ∀ i, DivBy (l : K) ((seq i).1 - C (coeff 1 (seq i).1) *
      PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam - (seq (i + 1)).1.subst ((X : PowerSeries K) ^ (l ^ 2))) :=
    fun i => (Classical.choose_spec (lemmaQ_tw hF h (i + 1) (seq i).2)).2

  have hsub : ∀ m : ℕ, m ≠ 0 → PowerSeries.HasSubst ((X : PowerSeries K) ^ m) := fun m hm =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hm])
  have hcomp : ∀ (f : PowerSeries K) (m q : ℕ), m ≠ 0 → q ≠ 0 →
      PowerSeries.subst ((X : PowerSeries K) ^ m) (f.subst ((X : PowerSeries K) ^ q) : PowerSeries K) =
        f.subst ((X : PowerSeries K) ^ (m * q)) := by
    intro f m q hm hq
    rw [PowerSeries.subst_comp_subst_apply (hsub q hq) (hsub m hm)]
    congr 1
    rw [← PowerSeries.coe_substAlgHom (hsub m hm), map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (hsub m hm), ← pow_mul]
  refine ⟨fun i => coeff 1 (seq i).1, ?_, fun i => (seq i).2.norm_coeff_one,
    fun N => ⟨(seq N).1, (seq N).2.D0, ?_⟩⟩
  · show ‖coeff 1 (lam.subst hh)‖ = 1
    rw [hcoef, hc1]
    exact hon_level hF h he0 he hlog hlev
  · induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, pow_one]
      exact hmod
    | succ N ih =>
      have hm : (l ^ 2) ^ (N + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl0)
      have h1 := (divBy_expand_iff (l : K) ((l ^ 2) ^ (N + 1)) hm _).2 (hstep N)
      rw [← PowerSeries.coe_substAlgHom (hsub _ hm), map_sub, map_sub, ← PowerSeries.smul_eq_C_mul,
        map_smul, PowerSeries.smul_eq_C_mul, PowerSeries.coe_substAlgHom, hcomp _ _ _ hm (pow_ne_zero _ hl0), ← pow_succ] at h1
      have := divBy_add ih h1
      convert this using 1
      simp only [Finset.sum_range_succ]
      ring

end ReciprocityTheory.ChartRestriction.L1
