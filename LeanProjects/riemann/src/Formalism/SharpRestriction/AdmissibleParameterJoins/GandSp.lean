import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSo
import Formalism.SharpRestriction.GrowthBounds.KerTies

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric

section Core

variable (p : ℕ) [Fact p.Prime]

instance : CharZero (WW p) := by
  obtain ⟨q, hq⟩ := CharP.exists (WW p)
  rcases CharP.char_is_prime_or_zero (WW p) q with h | h
  · exfalso
    have h0 : ((q : ℕ) : WW p) = 0 := CharP.cast_eq_zero (WW p) q
    have h1 : ((q : ℕ) : kb p) = 0 := by
      have := congrArg (WittVector.constantCoeff (p := p) (R := kb p)) h0
      rw [map_natCast, map_zero] at this
      exact this
    have h2 : p ∣ q := (CharP.cast_eq_zero_iff (kb p) p q).mp h1
    have h3 : p = q := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) h).mp h2
    have h4 : ((p : ℕ) : WW p) = ((q : ℕ) : WW p) := congrArg (Nat.cast) h3
    exact WittVector.p_nonzero p (kb p) (h4.trans h0)
  · subst h
    exact CharP.charP_to_charZero (WW p)

instance : CharZero (K0 p) := charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (K0 p))

theorem cc_pmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : PowerSeries A}
    (ha : PowerSeries.constantCoeff a = 0) : PowerSeries.constantCoeff (PowerSeries.map f a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, ha, map_zero]

theorem expS_eq_Ex {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : constantCoeff f = 0) : expS p f = Ex f := by
  ext n
  rw [coeff_Ex hf]
  rfl

instance : CharZero ℂ_[p] := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ℂ_[p]).injective

theorem expMv_eq_Ex {ι : Type} {f : MvPowerSeries ι ℂ_[p]} (hf : constantCoeff f = 0) : expMv f = Ex f := by
  ext n
  rw [coeff_Ex hf]
  show ∑ k ∈ Finset.range ((n.sum fun _ k => k) + 1),
      MvPowerSeries.coeff n (f ^ k) / (k.factorial : ℂ_[p]) = _
  refine Finset.sum_congr (by rfl) fun k _ => ?_
  exact div_eq_inv_mul (MvPowerSeries.coeff n (f ^ k)) (k.factorial : ℂ_[p])

theorem pmap_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) (a : PowerSeries A) :
    PowerSeries.map g (PowerSeries.map f a) = PowerSeries.map (g.comp f) a := by
  ext n
  simp [PowerSeries.coeff_map]

theorem mmap_map {ι A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B)
    (a : MvPowerSeries ι A) : map g (map f a) = map (g.comp f) a := by
  ext n
  simp [MvPowerSeries.coeff_map]

theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF]

def PhS (ι : Type) [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)) : MvPowerSeries (ι ⊕ ι) (K0 p) :=
  ∑ e : ι, sub2 p be (X (Sum.inl e)) (X (Sum.inr e))

theorem hs2 {τ R : Type} [CommRing R] {a b : MvPowerSeries τ R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    HasSubst (![a, b] : Fin 2 → MvPowerSeries τ R) :=  by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [ha, hb]
  | exact ⟨fun i => by fin_cases i <;> simp [ha, hb], fun d => Set.toFinite _⟩

variable {p}

theorem K1core {ι : Type} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (Oc : Subring Kc)
    (witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc)
    (iC : Kc →+* ℂ_[p]) (iC_int : ∀ x : Kc, x ∈ Oc ↔ ‖iC x‖ ≤ 1)
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (th_unit : IsUnit (PowerSeries.coeff 1 th))
    (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE)
    (Ph : MvPowerSeries ι (K0 p)) (hPh : constantCoeff Ph = 0) (Th : MvPowerSeries ι Kc)
    (hInt : IntegralMv (subst (diagS lgE) (map iC Th) *
      expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) Ph)))) :
    ∃ U : MvPowerSeries ι Kc, Th = map (algebraMap (K0 p) Kc) (expS p (-Ph)) * U ∧ IntR Oc (inParamK p Kc U) := by
  classical
  set φ : WW p →+* Kc := (algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)) with hφ
  set th' : PowerSeries Kc := PowerSeries.map φ th with hth'
  set lg : PowerSeries Kc := PowerSeries.map (algebraMap (K0 p) Kc) (logF p) with hlg
  have hth'0 : PowerSeries.constantCoeff th' = 0 := cc_pmap φ th_zero
  have hlg0 : PowerSeries.constantCoeff lg = 0 := cc_pmap _ (cc_logF p)
  set ps : PowerSeries (WW p) := th.substInvOfIsUnit th_unit with hps
  have hps0 : PowerSeries.constantCoeff ps = 0 := PowerSeries.constantCoeff_substInvOfIsUnit th th_unit
  have hinv0 : PowerSeries.subst ps th = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right th th_zero th_unit
  set ps' : PowerSeries Kc := PowerSeries.map φ ps with hps'
  have hps'0 : PowerSeries.constantCoeff ps' = 0 := cc_pmap φ hps0
  have hps'O : ∀ n, PowerSeries.coeff n ps' ∈ Oc := by
    intro n
    rw [hps', PowerSeries.coeff_map]
    exact witt_mem_integers_Cp _
  have hinv : PowerSeries.subst ps' th' = PowerSeries.X := by
    have h1 := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hps0) (h := φ) th
    rw [hinv0] at h1
    exact h1.symm.trans (PowerSeries.map_X φ)
  have hlgK0 : PowerSeries.constantCoeff (PowerSeries.subst th' lg) = 0 := by
    have hs : HasSubst (fun _ : Unit => th') := by
      first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hth'0
      | exact ⟨fun _ => by rw [show MvPowerSeries.constantCoeff th' = 0 from hth'0]; exact IsNilpotent.zero,
          fun d => Set.toFinite _⟩
    exact MvPowerSeries.constantCoeff_subst_eq_zero hs (fun _ => hth'0) hlg0
  have hlgE : PowerSeries.map iC (PowerSeries.subst th' lg) = lgE := by
    have h1 := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hth'0) (h := iC) lg
    refine h1.trans ?_
    rw [← th_log]
    show PowerSeries.subst (PowerSeries.map iC (PowerSeries.map φ th))
      (PowerSeries.map iC (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) = _
    rw [pmap_map, pmap_map]
  have hlgE0 : PowerSeries.constantCoeff lgE = 0 := by
    rw [← hlgE]
    exact cc_pmap iC hlgK0
  have hc : constantCoeff (map (iC.comp (algebraMap (K0 p) Kc)) Ph) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hPh, map_zero]
  have hc' := MvPowerSeries.constantCoeff_subst_eq_zero (hs_dg hlgE0) (cc_dg hlgE0) hc
  have hE : subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) (expS p Ph)) =
      expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) Ph)) := by
    rw [expS_eq_Ex p hPh, map_Ex _ hPh, subst_Ex (hs_dg hlgE0) hc, expMv_eq_Ex p hc']
  refine ⟨map (algebraMap (K0 p) Kc) (expS p Ph) * Th, ?_, ?_⟩
  · have hn : constantCoeff (-Ph) = 0 := by rw [map_neg, hPh, neg_zero]
    rw [← mul_assoc, ← map_mul, expS_eq_Ex p hn, expS_eq_Ex p hPh, Ex_neg_mul hPh, map_one, one_mul]
  · have hInt' : IntegralMv (subst (diagS lgE) (map iC (map (algebraMap (K0 p) Kc) (expS p Ph) * Th))) := by
      rw [map_mul, mmap_map, MvPowerSeries.subst_mul (hs_dg hlgE0), hE, mul_comm]
      exact hInt
    have key : map iC (subst (diagS (PowerSeries.subst th' lg))
        (map (algebraMap (K0 p) Kc) (expS p Ph) * Th)) =
        subst (diagS lgE) (map iC (map (algebraMap (K0 p) Kc) (expS p Ph) * Th)) := by
      rw [MvPowerSeries.map_subst (hs_dg hlgK0)]
      congr 1
      funext i
      rw [map_dg, hlgE]
    intro n
    refine descent Oc th' lg ps' hth'0 hps'0 hps'O hinv hlg0 _ (fun m => ?_) n
    rw [iC_int]
    have hm := hInt' m
    rw [← key, MvPowerSeries.coeff_map] at hm
    exact hm

end Core

end Formalism.MainNotions.J
