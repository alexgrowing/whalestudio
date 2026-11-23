import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (Rul Ix ex sec ramOverZ)
open GlobalTheory.CompanionTheory.Ar.Ref (pjSys UnifAll)

def htExp (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def latExp (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ S then htExp p + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0

def IsNormOfVal (p e : ℕ) (m : EReal) (r x : ℝ) : Prop :=
  ∀ s : ℝ, (m ≤ ((e * s : ℝ) : EReal) → (p : ℝ) ^ (-s) * r ≤ x) ∧
    (((e * s : ℝ) : EReal) ≤ m → x ≤ (p : ℝ) ^ (-s) * r)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx}

def ReadsSecFin (Fr : GenFrame Or) {p : ℕ} [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p)
    {la : HeightOneSpectrum (𝓞 c.F)} (x : (pjSys Xo c).Pt la) (t : Ix D → ℝ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ v : PadicAlgCl p, HasVal RM.y 0 (Fr.rd f) z v ∧
    IsNormOfVal p (ramOverZ la) ((pjSys Xo c).val x f) (∏ j, t j ^ ex D a n j) ‖v‖

def ReadsRootsFin (Or : RootOrigin Y S RM Fx) {p : ℕ} [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p)
    (t : Ix D → ℝ) (θ : ℝ) : Prop :=
  ∀ ρ : RootIx D, ∃ w : PadicAlgCl p, HasVal RM.y (RM.xdeg ρ) (Or.e ρ)⁻¹ z w ∧ w ≠ 0 ∧
    |Real.log (supMet (RM.xdeg ρ) z) - Real.log (‖w‖ / t (rootFrameIx D ρ) ^ HodgeCpt.rootSgn D ρ)| ≤
      θ * Real.log p

def ReadFinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (RM : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (Or : RootOrigin Y S RM Fx) (Fr : GenFrame Or),
    UnifAll Xo c → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree Or.𝔐 p) →
    ∃ u : MRing RM.ι, IsFormOff (mCoordIdeal RM.y) u ∧
      ∀ (p : ℕ) [Fact p.Prime], ∀ z ∈ algPts p (mCoordIdeal RM.y), aeval z u ≠ 0 →
        ∃ (la : HeightOneSpectrum (𝓞 c.F)) (x : (pjSys Xo c).Pt la) (t : Ix D → ℝ),
          (p : 𝓞 c.F) ∈ la.asIdeal ∧ (∀ j, 0 < t j) ∧ ReadsSecFin Fr z x t ∧ ReadsRootsFin Or z t (latExp E S p)

theorem latExp_of_notMem (E : Type) [Field E] [NumberField E] {S : Finset ℕ} {p : ℕ} (h : p ∉ S) :
    latExp E S p = 0 := if_neg h

theorem htExp_pos {p : ℕ} (hp : p.Prime) : 0 < htExp p := by
  unfold htExp
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact one_div_pos.2 (by linarith)

theorem latExp_nonneg (E : Type) [Field E] [NumberField E] (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ latExp E S p := by
  unfold latExp
  split_ifs
  · have := htExp_pos hp
    positivity
  · exact le_rfl

example : htExp 2 = 2 ∧ htExp 3 = 1 / 2 := by
  constructor <;> norm_num [htExp]

example (E : Type) [Field E] [NumberField E] :
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ (discr E).natAbs.primeFactors := fun _ hp h =>
  Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 h, Int.natAbs_ne_zero.2 (discr_ne_zero E)⟩

theorem isNormOfVal_coe {p e : ℕ} (hp : 1 ≤ p) (he : 0 < e) (m : ℝ) {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    IsNormOfVal p e (m : EReal) r x ↔ x = (p : ℝ) ^ (-(m / e)) * r := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  constructor
  · intro h
    have hm : ((e * (m / e) : ℝ) : EReal) = m := by congr 1; field_simp
    exact le_antisymm ((h _).2 hm.le) ((h _).1 hm.ge)
  · rintro rfl s
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h1 : m / e ≤ s := by rw [div_le_iff₀ he', mul_comm]; exact EReal.coe_le_coe_iff.1 h
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp' (by linarith)) hr
    · have h1 : s ≤ m / e := by rw [le_div_iff₀ he', mul_comm]; exact EReal.coe_le_coe_iff.1 h
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp' (by linarith)) hr

theorem isNormOfVal_top {p : ℕ} (hp : 2 ≤ p) (e : ℕ) {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    IsNormOfVal p e ⊤ r x ↔ x = 0 := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  constructor
  · intro h
    refine le_antisymm ?_ hx
    have h1 : Filter.Tendsto (fun s : ℝ => (p : ℝ) ^ (-s) * r) Filter.atTop (nhds (0 * r)) :=
      ((tendsto_rpow_atBot_of_base_gt_one _ hp').comp Filter.tendsto_neg_atTop_atBot).mul_const r
    rw [zero_mul] at h1
    exact ge_of_tendsto' h1 fun s => (h s).2 le_top
  · rintro rfl s
    exact ⟨fun h => absurd (top_le_iff.1 h) (EReal.coe_ne_top _), fun _ => by positivity⟩

theorem readsRootsFin_zero {p : ℕ} [Fact p.Prime] {z : (Σ k, RM.ι k) → PadicAlgCl p} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {t : Ix D → ℝ} (ht : ∀ j, 0 < t j) :
    ReadsRootsFin Or z t 0 ↔ ∀ ρ : RootIx D, ∃ w : PadicAlgCl p, HasVal RM.y (RM.xdeg ρ) (Or.e ρ)⁻¹ z w ∧
      ‖w‖ = t (rootFrameIx D ρ) ^ HodgeCpt.rootSgn D ρ * supMet (RM.xdeg ρ) z := by
  refine forall_congr' fun ρ => exists_congr fun w => and_congr_right fun _ => ?_
  have hs : 0 < supMet (RM.xdeg ρ) z := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 fun h => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h i)) _
  have htt : 0 < t (rootFrameIx D ρ) ^ HodgeCpt.rootSgn D ρ := zpow_pos (ht _) _
  rw [zero_mul, abs_nonpos_iff, sub_eq_zero]
  constructor
  · rintro ⟨hw, h⟩
    have := Real.log_injOn_pos hs (div_pos (norm_pos_iff.2 hw) htt) h
    rw [this]
    field_simp
  · intro h
    refine ⟨norm_pos_iff.1 (h ▸ mul_pos htt hs), ?_⟩
    rw [h, mul_div_cancel_left₀ _ htt.ne']

theorem pjSys_val_one {la : HeightOneSpectrum (𝓞 c.F)} (x : (pjSys Xo c).Pt la) : (pjSys Xo c).val x 1 = 0 := by
  obtain ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩ := x
  show Formalism.L2.Pj.nval T.V e (Formalism.L2.Pj.evI y 1) = 0
  have h1 : Formalism.L2.Pj.evI y 1 = 1 := by
    letI := io.toAlgebra
    exact Formalism.L2.Pj.evalAt_one _ _ _ y.2.1
  rw [h1, Formalism.L2.Pj.nval_of_ne one_ne_zero]
  simp [Formalism.L2.Pj.vV]

set_option synthInstance.maxHeartbeats 200000 in

theorem readsSecFin_prime (Fr : GenFrame Or) {p : ℕ} [hp : Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p)
    {la : HeightOneSpectrum (𝓞 c.F)} (hla : (p : 𝓞 c.F) ∈ la.asIdeal) (x : (pjSys Xo c).Pt la) (t : Ix D → ℝ) :
    ∃ v : PadicAlgCl p, HasVal RM.y 0 (Fr.rd ((p : c.F) • 1)) z v ∧
      IsNormOfVal p (ramOverZ la) ((pjSys Xo c).val x ((p : c.F) • 1)) (∏ j, t j ^ ex D 0 0 j) ‖v‖ := by
  have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra h
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd
  have hv : Ref.vl la (p : c.F) = ramOverZ la := by
    rw [← hres]
    exact Formalism.L2.Pj.Crude.crv_vLa_char la
  have he : 0 < ramOverZ la := by
    have h1 : la.valuation c.F (p : c.F) < 1 := by
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact (la.valuation_lt_one_iff_mem _).2 hla
    have h2 := (WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    have h3 : (0 : ℤ) < Ref.vl la (p : c.F) := by unfold Ref.vl; omega
    rw [hv] at h3
    exact_mod_cast h3
  have h3 : ∀ j, ex D 0 0 j = 0 := fun j => by cases j <;> rfl
  have hC : ∀ a : ℤ, IsMultiHomog (C a : MRing RM.ι) 0 := fun a m hm k => by
    classical
    have : m = 0 := by
      by_contra h
      exact mem_support_iff.1 hm (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [this]
  refine ⟨p, ⟨0, 0, C (p : ℤ), C 1, hC _, hC _, fun _ => by simp, ?_, by simp, by simp⟩, ?_⟩
  · rw [Fr.rd_smul, Fr.rd_one]
    simp
  · rw [(pjSys Xo c).val_smul x _ _ hp0, pjSys_val_one, add_zero, hv, isNormOfVal_coe hp.out.one_le he _
      (Finset.prod_nonneg fun j _ => by rw [h3, pow_zero]; exact zero_le_one)]
    have he' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp only [h3, pow_zero, Finset.prod_const_one, mul_one, Int.cast_natCast, div_self he', Real.rpow_neg_one]
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]

end GlobalTheory.CompanionTheory.Ar.Small
