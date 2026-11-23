import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

theorem zc_mul (a b : ℤ_[p]) : zc (a * b) = zc a * zc b := by
  simp only [PI.PhNormUnits.zc, PadicInt.coe_mul, map_mul]

theorem zc_one : zc (1 : ℤ_[p]) = 1 := by
  simp only [PI.PhNormUnits.zc, PadicInt.coe_one, map_one]

theorem zc_two : zc (2 : ℤ_[p]) = 2 := by
  have h : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
    have := PadicInt.coe_natCast (p := p) 2
    simpa using this
  simp only [PI.PhNormUnits.zc, h, map_ofNat]

theorem norm_zc (a : ℤ_[p]) : ‖zc a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ = ‖a‖
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem norm_two_of (hp2 : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h2 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hp2)
  have h2' : ‖(2 : ℚ_[p])‖ = 1 := by exact_mod_cast h2
  have e : algebraMap ℚ_[p] ℂ_[p] 2 = 2 := map_ofNat _ 2
  rw [← e, norm_algebraMap', h2']

theorem zc_inv_of (n : ℤ_[p]) (h : ‖zc n‖ = 1) : ∃ m : ℤ_[p], zc n * zc m = 1 := by
  rw [norm_zc] at h
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr h
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  rw [← zc_mul, ← hu, Units.mul_inv, zc_one]

section

variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hSub hex0 hinv in

theorem simeq_subst1 {τ : Type} (w : MvPowerSeries τ ℂ_[p]) (hw0 : MvPowerSeries.constantCoeff w = 0)
    (hw : IntegralMv w) {f g : MvPowerSeries Unit ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst (fun _ => w) f) (MvPowerSeries.subst (fun _ => w) g) :=
  (hSub p Unit τ (fun _ => w) (fun _ => hw0) (fun _ => hw)).1 f g h

include hSub hex0 hinv in
theorem simeq_subst2 {τ : Type} (x y : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hx : IntegralMv x) (hy : IntegralMv y)
    {f g : MvPowerSeries (Fin 2) ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst ![x, y] f) (MvPowerSeries.subst ![x, y] g) := by
  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i
    · simpa using hx0
    · simpa using hy0
  have hsI : ∀ i, PI.PhNormUnits.IntegralMv (![x, y] i) := by
    intro i; fin_cases i
    · simpa using hx
    · simpa using hy
  exact (hSub p (Fin 2) τ ![x, y] hs0 hsI).1 f g h

include hSub hex0 hinv in

theorem norm_at {ph : PowerSeries ℂ_[p]} (c N : ℂ_[p])
    (h : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ())))
    {τ : Type} (w : MvPowerSeries τ ℂ_[p]) (hw0 : MvPowerSeries.constantCoeff w = 0) (hw : IntegralMv w) :
    Simeq (phAt ph (mulBy l ex c w)) (MvPowerSeries.C N * phAt ph w) := by
  have hs : ∀ i : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => w) i) = 0 := fun _ => hw0
  have hv : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hsm : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv c _ hv
  have eL : MvPowerSeries.subst (fun _ : Unit => w)
      (PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p]))) = PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c w) := by
    rw [sb_phAt (fun _ : Unit => w) hs ph _ hsm,
      sb_mulBy (fun _ : Unit => w) hs hex0 hinv c _ hv, sb_X (fun _ : Unit => w) hs ()]
  have eR : MvPowerSeries.subst (fun _ : Unit => w)
      (MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv () : MvPowerSeries Unit ℂ_[p])) = MvPowerSeries.C N * PI.PhNormUnits.phAt ph w := by
    rw [sb_C_mul (fun _ : Unit => w) hs N, sb_phAt (fun _ : Unit => w) hs ph _ hv,
      sb_X (fun _ : Unit => w) hs ()]
  have key := simeq_subst1 hSub hex0 hinv w hw0 hw h
  rw [eL, eR] at key
  exact key

end

section Units

variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hE hSub hex0 hinv hIA in
theorem units_i (c N : ℂ_[p])
    (hU : Simeq (phAt ph (mulBy l ex c (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C N * phAt ph (Xv ()))) :
    Simeq (be l ex ph (mulBy l ex c (Xv 0)) (mulBy l ex c (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C N * be l ex ph (Xv 0) (Xv 1)) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hA := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (constantCoeff_formalAdd hex0 hinv _ _ h0 h1) hIA
  have hX := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) h0 (int_X 0)
  have hY := norm_at hSub hex0 hinv c N hU
    (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) h1 (int_X 1)
  have hsum := sSub hE (sSub hE hA hX) hY
  have eL : PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)) =
      PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1))) - PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0))
        - PI.PhNormUnits.phAt ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)) := by
    rw [mulBy_add hex0 hinv c _ _ h0 h1]
    rfl
  have eR : MvPowerSeries.C N * PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.Xv 1) =
      MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.add l ex (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.Xv 1)) - MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv 0)
        - MvPowerSeries.C N * PI.PhNormUnits.phAt ph (PI.PhNormUnits.Xv 1) := by
    simp only [PI.PhNormUnits.be]
    ring
  rw [eL, eR]
  exact hsum

include hE hSub hC hD hex0 hinv hph hIA hB in
theorem units_ii (c d : ℂ_[p]) (n : ℤ_[p]) (hn : c * d = zc n) :
    Simeq (MvPowerSeries.C (c * d) * be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (mulBy l ex c (Xv 1)))) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hcomp : PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      PI.PhNormUnits.mulBy l ex (PI.PhNormUnits.zc n) (PI.PhNormUnits.Xv 1) := by
    rw [mulBy_mulBy hex0 hinv d c _ h1, mul_comm d c, hn]
  have key := be_zp hE hSub hex0 hinv hB hC hD hph hIA
    (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.Xv 1) h0 h1 (int_X 0) (int_X 1) n
  rw [hcomp, hn]
  exact sSymm hE key

include hE hSub hex0 hinv in
theorem units_iv (c d : ℂ_[p]) (hc : c ≠ 0)
    (hw : IntegralMv (mulBy l ex c⁻¹ (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (h : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (mulBy l ex c (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (mulBy l ex c (Xv 1))))) :
    Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))) := by
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 0
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := constantCoeff_var 1
  have hy0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h1
  have hcs0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h0
  have hcs1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ h1
  have hdc1 : MvPowerSeries.constantCoeff
      (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]))) = 0 :=
    constantCoeff_formalSMul hex0 hinv _ _ hcs1
  have hs : ∀ i, MvPowerSeries.constantCoeff (![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] i) = 0 := by
    intro i; fin_cases i
    · simp
    · simpa using hy0
  have hs0 : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = PI.PhNormUnits.Xv 0 := by
    rw [sb_X _ hs 0]; simp
  have hs1 : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)] (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1) := by
    rw [sb_X _ hs 1]; simp
  have hcc : PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) = PI.PhNormUnits.Xv 1 := by
    rw [mulBy_mulBy hex0 hinv c c⁻¹ _ h1, mul_inv_cancel₀ hc, mulBy_one hex0 hinv _ h1]
  have eL : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)]
      (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1))) =
      PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) := by
    rw [sb_be _ hs hex0 hinv ph _ _ hcs0 hcs1, sb_mulBy _ hs hex0 hinv c _ h0,
      sb_mulBy _ hs hex0 hinv c _ h1, hs0, hs1, hcc]
  have eR : MvPowerSeries.subst ![(PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]), PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)]
      (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.mulBy l ex c (PI.PhNormUnits.Xv 1)))) =
      PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex d (PI.PhNormUnits.Xv 1)) := by
    rw [sb_be _ hs hex0 hinv ph _ _ h0 hdc1, sb_mulBy _ hs hex0 hinv d _ hcs1,
      sb_mulBy _ hs hex0 hinv c _ h1, hs0, hs1, hcc]
  have key := simeq_subst2 hSub hex0 hinv (PI.PhNormUnits.Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.mulBy l ex c⁻¹ (PI.PhNormUnits.Xv 1)) h0 hy0 (int_X 0) hw h
  rw [eL, eR] at key
  exact key

end Units

end PI.PhNormUnits.UnitaryGroupMassFormula
