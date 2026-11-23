import Mathlib
import GroundTheory.PAdicHodge.SlopeFrobenius
import GroundTheory.PAdicHodge.SlopePhiSub
import GroundTheory.PAdicHodge.SlopeCauchyBinet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Module

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

variable (K) in

def dvUnif : K := ((IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose : K)

theorem irreducible_dvUnif :
    Irreducible (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose :=
  (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose_spec

theorem norm_eq_one_of_isUnit {z : normInteger K} (hz : IsUnit z) : ‖(z : K)‖ = 1 := by
  have := (normInteger_integers (K := K)).isUnit_iff_valuation_eq_one.1 hz
  rw [NormedField.valuation_apply, ← NNReal.coe_eq_one] at this
  exact this

theorem dvUnif_ne_zero : dvUnif K ≠ 0 := by
  intro h
  have := (irreducible_dvUnif (K := K)).ne_zero
  exact this (Subtype.ext h)

theorem norm_dvUnif_pos : 0 < ‖dvUnif K‖ := norm_pos_iff.2 dvUnif_ne_zero

theorem norm_dvUnif_lt_one : ‖dvUnif K‖ < 1 := by
  have h1 : ‖dvUnif K‖ ≤ 1 := mem_normInteger.1
    (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose.2
  refine lt_of_le_of_ne h1 fun h => (irreducible_dvUnif (K := K)).not_isUnit ?_
  rw [(normInteger_integers (K := K)).isUnit_iff_valuation_eq_one, NormedField.valuation_apply,
    ← NNReal.coe_eq_one]
  exact h

theorem exists_norm_eq_zpow {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖dvUnif K‖ ^ n := by
  have key : ∀ y : K, y ≠ 0 → ‖y‖ ≤ 1 → ∃ n : ℕ, ‖y‖ = ‖dvUnif K‖ ^ n := by
    intro y hy hy1
    let z : normInteger K := ⟨y, mem_normInteger.2 hy1⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz irreducible_dvUnif
    refine ⟨n, ?_⟩
    have h2 := congrArg (fun w : normInteger K => (w : K)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h2
    rw [show y = (z : K) from rfl, h2, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, one_mul]
    rfl
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key x hx h
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := key x⁻¹ (inv_ne_zero hx) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

theorem zpow_dvUnif_injective : Function.Injective fun n : ℤ => ‖dvUnif K‖ ^ n :=
  (zpow_right_strictAnti₀ norm_dvUnif_pos norm_dvUnif_lt_one).injective

namespace Robba

def intBounded (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Subring (Robba K) where
  carrier := {f | f ∈ bounded K ∧ norm1 f ≤ 1}
  mul_mem' {f g} hf hg := ⟨(bounded K).mul_mem hf.1 hg.1, by
    rw [gaussNorm_mul_alt hf.1 hg.1]; nlinarith [gaussNorm_nonneg_alt f, gaussNorm_nonneg_alt g, hf.2, hg.2]⟩
  one_mem' := ⟨(bounded K).one_mem, by
    refine ciSup_le fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]⟩
  add_mem' {f g} hf hg := ⟨(bounded K).add_mem hf.1 hg.1,
    (gaussNorm_add_le_max_alt hf.1 hg.1).trans (max_le hf.2 hg.2)⟩
  zero_mem' := ⟨(bounded K).zero_mem, by simp [norm1]⟩
  neg_mem' {f} hf := ⟨(bounded K).neg_mem hf.1, by simpa [norm1] using hf.2⟩

theorem mem_intBounded {f : Robba K} : f ∈ intBounded K ↔ f ∈ bounded K ∧ norm1 f ≤ 1 := Iff.rfl

theorem unit_mem_bounded (u : (Robba K)ˣ) : (u : Robba K) ∈ bounded K :=
  mem_bounded_of_mul_eq_one u.mul_inv

theorem unit_ne_zero (u : (Robba K)ˣ) : (u : Robba K) ≠ 0 := u.ne_zero

theorem gaussNorm_unit_pos (u : (Robba K)ˣ) : 0 < norm1 (u : Robba K) :=
  lt_of_le_of_ne (gaussNorm_nonneg_alt _) fun h =>
    unit_ne_zero u ((gaussNorm_eq_zero_iff_alt (unit_mem_bounded u)).1 h.symm)

theorem exists_norm1_eq_zpow (u : (Robba K)ˣ) : ∃ n : ℤ, norm1 (u : Robba K) = ‖dvUnif K‖ ^ n := by
  obtain ⟨m, hm⟩ := exists_norm1_eq (unit_mem_bounded u)
  have hne : (u : Robba K).coeff m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm
    exact (gaussNorm_unit_pos u).ne' hm
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow hne
  exact ⟨n, hm.trans hn⟩

def ord (u : (Robba K)ˣ) : ℤ := (exists_norm1_eq_zpow u).choose

theorem gaussNorm_eq_zpow_ord (u : (Robba K)ˣ) : norm1 (u : Robba K) = ‖dvUnif K‖ ^ ord u :=
  (exists_norm1_eq_zpow u).choose_spec

theorem ord_eq_of_norm1_eq {u : (Robba K)ˣ} {n : ℤ} (h : norm1 (u : Robba K) = ‖dvUnif K‖ ^ n) :
    ord u = n :=
  zpow_dvUnif_injective ((gaussNorm_eq_zpow_ord u).symm.trans h)

theorem ord_mul (u w : (Robba K)ˣ) : ord (u * w) = ord u + ord w := by
  apply ord_eq_of_norm1_eq
  rw [Units.val_mul, gaussNorm_mul_alt (unit_mem_bounded u) (unit_mem_bounded w), gaussNorm_eq_zpow_ord,
    gaussNorm_eq_zpow_ord, zpow_add₀ norm_dvUnif_pos.ne']

theorem ord_nonneg_iff (u : (Robba K)ˣ) : 0 ≤ ord u ↔ norm1 (u : Robba K) ≤ 1 := by
  rw [gaussNorm_eq_zpow_ord, ← zpow_zero ‖dvUnif K‖]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ norm_dvUnif_pos norm_dvUnif_lt_one).symm

theorem ord_eq_zero_iff (u : (Robba K)ˣ) : ord u = 0 ↔ norm1 (u : Robba K) = 1 := by
  constructor
  · intro h; rw [gaussNorm_eq_zpow_ord, h, zpow_zero]
  · intro h; exact ord_eq_of_norm1_eq (by rw [h, zpow_zero])

def unitOrd (ψ : Robba K →+* Robba K)
    (hψ : ∀ u : (Robba K)ˣ, norm1 (ψ u) = norm1 (u : Robba K)) : PhiModule.UnitOrd (Robba K) ψ where
  ord := ord
  map_mul := ord_mul
  map_phi u := ord_eq_of_norm1_eq (by
    change norm1 (ψ (u : Robba K)) = _
    rw [hψ, gaussNorm_eq_zpow_ord])

end Robba

namespace Robba

def IsGaussScaling (ψ : Robba K →+* Robba K) (Q : ℕ) : Prop :=
  ∀ f : Robba K, ∀ᶠ ρ in 𝓝[<] (1 : ℝ), gaussNorm (ψ f).coeff ρ = gaussNorm f.coeff (ρ ^ Q)

theorem tendsto_pow_nhdsLT {Q : ℕ} (hQ : 0 < Q) :
    Tendsto (fun ρ : ℝ => ρ ^ Q) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_pow Q).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact pow_lt_one₀ hρ.1.le hρ.2 hQ.ne'

theorem IsGaussScaling.pow {ψ : Robba K →+* Robba K} {Q : ℕ} (h : IsGaussScaling ψ Q)
    (hQ : 0 < Q) : ∀ d : ℕ, IsGaussScaling (ψ ^ d) (Q ^ d)
  | 0 => fun f => Eventually.of_forall fun ρ => by simp
  | d + 1 => fun f => by
    have ih := (IsGaussScaling.pow h hQ d f)
    filter_upwards [h ((ψ ^ d) f), (tendsto_pow_nhdsLT hQ).eventually ih] with ρ h1 h2
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, h1, h2, ← pow_mul, pow_succ']

theorem eventually_mem_Ioo : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo 0 1 :=
  Ioo_mem_nhdsLT (by norm_num)

theorem exists_gaussNorm_pow_le (f : Robba K) {Q : ℕ} (hQ : 0 < Q) :
    ∃ n₀ : ℤ, ∀ᶠ ρ in 𝓝[<] (1 : ℝ),
      gaussNorm f.coeff (ρ ^ Q) ≤ ρ ^ (((Q : ℤ) - 1) * n₀) * gaussNorm f.coeff ρ := by
  by_cases hf : f.coeff = 0
  · exact ⟨0, Eventually.of_forall fun ρ => by simp [hf, gaussNorm_zero]⟩
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f f
  have hQ1 : (0 : ℤ) ≤ (Q : ℤ) - 1 := by omega
  refine ⟨lowIndex f.coeff r, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hr1, (tendsto_pow_nhdsLT hQ).eventually (Ioo_mem_nhdsLT hr1)]
    with ρ hρ hρQ
  have hρ0 : 0 < ρ := hr0.trans hρ.1
  have c' := (hc (ρ ^ Q) hρQ.1.le hρQ.2).1
  have c := (hc ρ hρ.1.le hρ.2).1
  have cr := (hc r le_rfl hr1).1
  have hn : lowIndex f.coeff r ≤ lowIndex f.coeff (ρ ^ Q) :=
    (lowIndex_le_highIndex hr0 cr hf).trans (highIndex_le_lowIndex hr0 hρQ.1 cr c' hf)
  have hmem : ‖f.coeff (lowIndex f.coeff (ρ ^ Q))‖ * (ρ ^ Q) ^ lowIndex f.coeff (ρ ^ Q) =
      gaussNorm f.coeff (ρ ^ Q) := lowIndex_mem (hr0.trans hρQ.1) c' hf
  set n := lowIndex f.coeff (ρ ^ Q)
  rw [← hmem]
  have h1 : ‖f.coeff n‖ * ρ ^ n ≤ gaussNorm f.coeff ρ := c.le_gaussNorm n
  have e : (ρ ^ Q) ^ n = ρ ^ n * ρ ^ (((Q : ℤ) - 1) * n) := by
    rw [← zpow_add₀ hρ0.ne', ← zpow_natCast, ← zpow_mul]; congr 1; ring
  have h2 : ρ ^ (((Q : ℤ) - 1) * n) ≤ ρ ^ (((Q : ℤ) - 1) * lowIndex f.coeff r) :=
    zpow_le_zpow_right_of_le_one₀ hρ0 hρ.2.le (mul_le_mul_of_nonneg_left hn hQ1)
  calc ‖f.coeff n‖ * (ρ ^ Q) ^ n = (‖f.coeff n‖ * ρ ^ n) * ρ ^ (((Q : ℤ) - 1) * n) := by
        rw [e]; ring
    _ ≤ gaussNorm f.coeff ρ * ρ ^ (((Q : ℤ) - 1) * lowIndex f.coeff r) :=
        mul_le_mul h1 h2 (by positivity) (gaussNorm_nonneg hρ0)
    _ = _ := mul_comm _ _

theorem exists_gaussNorm_pow_le_family {ι : Type*} [Finite ι] (x : ι → Robba K) {Q : ℕ}
    (hQ : 0 < Q) : ∃ n₀ : ℤ, ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ∀ i,
      gaussNorm (x i).coeff (ρ ^ Q) ≤ ρ ^ (((Q : ℤ) - 1) * n₀) * gaussNorm (x i).coeff ρ := by
  have := Fintype.ofFinite ι
  choose n hn using fun i => exists_gaussNorm_pow_le (x i) hQ
  have hQ1 : (0 : ℤ) ≤ (Q : ℤ) - 1 := by omega
  refine ⟨-∑ i, |n i|, ?_⟩
  filter_upwards [eventually_all.2 hn, eventually_mem_Ioo] with ρ h hρ i
  refine (h i).trans (mul_le_mul_of_nonneg_right ?_ (gaussNorm_nonneg hρ.1))
  refine zpow_le_zpow_right_of_le_one₀ hρ.1 hρ.2.le (mul_le_mul_of_nonneg_left ?_ hQ1)
  have h1 : |n i| ≤ ∑ j, |n j| :=
    Finset.single_le_sum (f := fun j => |n j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 := neg_abs_le (n i)
  linarith

theorem gaussNorm_sum_le {ι : Type*} (s : Finset ι) (y : ι → Robba K) {ρ C : ℝ} (hρ : 0 < ρ)
    (hC : 0 ≤ C) (hc : ∀ i ∈ s, ConvergesAt (y i).coeff ρ)
    (h : ∀ i ∈ s, gaussNorm (y i).coeff ρ ≤ C) :
    ConvergesAt (∑ i ∈ s, y i).coeff ρ ∧ gaussNorm (∑ i ∈ s, y i).coeff ρ ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussNorm_zero, hC, convergesAt_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨ic, ib⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ca := hc a (Finset.mem_insert_self a s)
    exact ⟨convergesAt_add hρ ca ic, (gaussNorm_add_le' hρ ca ic).trans
      (max_le (h a (Finset.mem_insert_self a s)) ib)⟩

theorem gaussNorm_le_one_of_smul_eq {ψ : Robba K →+* Robba K} {Q : ℕ} (hψ : IsGaussScaling ψ Q)
    (hQ : 0 < Q) {ι : Type*} [Fintype ι] {x : ι → Robba K} (hx : x ≠ 0)
    {B : Matrix ι ι (Robba K)} (hB : ∀ i j, B i j ∈ intBounded K) {l : Robba K}
    (hl : l ∈ bounded K) (h : ∀ i, l * x i = ∑ j, B i j * ψ (x j)) : norm1 l ≤ 1 := by
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hx
  have hne : Nonempty ι := ⟨i₁⟩
  obtain ⟨n₀, hn₀⟩ := exists_gaussNorm_pow_le_family x hQ
  have hzpow : Tendsto (fun ρ : ℝ => ρ ^ (((Q : ℤ) - 1) * n₀)) (𝓝[<] 1) (𝓝 1) := by
    have := ((continuousAt_zpow₀ (1 : ℝ) (((Q : ℤ) - 1) * n₀) (Or.inl one_ne_zero)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hBε : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ∀ i j, gaussNorm (B i j).coeff ρ < 1 + ε :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (tendsto_gaussNorm_norm1 (hB i j).1).eventually_lt_const (by linarith [(hB i j).2])
  have hbound : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), gaussNorm l.coeff ρ ≤ (1 + ε) * ρ ^ (((Q : ℤ) - 1) * n₀) := by
    filter_upwards [hn₀, hBε, eventually_mem_Ioo, eventually_all.2 fun i => (x i).eventually_convergesAt,
      eventually_all.2 fun i => eventually_all.2 fun j => (B i j).eventually_convergesAt,
      l.eventually_convergesAt, eventually_all.2 fun j => (ψ (x j)).eventually_convergesAt,
      eventually_all.2 fun j => hψ (x j)] with ρ h1 h2 hρ cx cB cl cψ hψρ
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => gaussNorm (x i).coeff ρ
    set X := gaussNorm (x i₀).coeff ρ
    have hx1 : (x i₁).coeff ≠ 0 := fun h0 => hi₁ (Robba.ext h0)
    have hX : 0 < X := lt_of_lt_of_le (gaussNorm_pos hρ.1 (cx i₁) hx1) (hi₀ i₁)
    have hz : 0 ≤ ρ ^ (((Q : ℤ) - 1) * n₀) := by have := hρ.1; positivity
    have key := gaussNorm_sum_le Finset.univ (fun j => B i₀ j * ψ (x j)) hρ.1
      (C := (1 + ε) * ρ ^ (((Q : ℤ) - 1) * n₀) * X) (by positivity)
      (fun j _ => convergesAt_mul hρ.1 (cB i₀ j) (cψ j)) (fun j _ => by
        rw [gaussNorm_mul hρ.1 (cB i₀ j) (cψ j), hψρ j]
        calc gaussNorm (B i₀ j).coeff ρ * gaussNorm (x j).coeff (ρ ^ Q)
            ≤ (1 + ε) * (ρ ^ (((Q : ℤ) - 1) * n₀) * gaussNorm (x j).coeff ρ) :=
              mul_le_mul (h2 i₀ j).le (h1 j) (gaussNorm_nonneg (by have := hρ.1; positivity))
                (by linarith)
          _ ≤ (1 + ε) * (ρ ^ (((Q : ℤ) - 1) * n₀) * X) := by gcongr; exact hi₀ j
          _ = _ := by ring)
    rw [← h i₀, gaussNorm_mul hρ.1 cl (cx i₀)] at key
    have := key.2
    rw [mul_le_mul_iff_left₀ hX] at this
    exact this
  have hlim := hzpow.const_mul (1 + ε)
  rw [mul_one] at hlim
  exact le_of_tendsto_of_tendsto (tendsto_gaussNorm_norm1 hl) hlim hbound

end Robba

theorem FrobeniusLift.isGaussScaling (F : FrobeniusLift K) : Robba.IsGaussScaling F.phi F.q :=
  fun f => FrobeniusLift.eventually_gaussNorm_phi f

namespace PhiModule

open Matrix

variable {ψ : Robba K →+* Robba K} {Q : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

theorem det_mem_of_forall_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (S : Subring R) (A : Matrix ι ι R) (h : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  let A' : Matrix ι ι S := Matrix.of fun i j => ⟨A i j, h i j⟩
  have e : A = A'.map S.subtype := by ext i j; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (A'.det).2

theorem le_deg_of_le (hψ : Robba.IsGaussScaling ψ Q) (hQ : 0 < Q)
    (hψn : ∀ u : (Robba K)ˣ, Robba.norm1 (ψ u) = Robba.norm1 (u : Robba K))
    {Φ : M →ₛₗ[ψ] M} {I N : Submodule (Robba K) M} (hIN : I ≤ N) (hI : IsStable Φ I)
    (hN : IsStable Φ N) [Module.Free (Robba K) I] [Module.Finite (Robba K) I]
    [Module.Free (Robba K) N] [Module.Finite (Robba K) N] (hIphi : IsPhiModule (restrict Φ I hI))
    (hNphi : IsPhiModule (restrict Φ N hN)) (hrank : finrank (Robba K) I = finrank (Robba K) N) :
    deg (Robba.unitOrd ψ hψn) (restrict Φ N hN) ≤ deg (Robba.unitOrd ψ hψn) (restrict Φ I hI) := by
  classical
  set r := finrank (Robba K) N
  let bN : Basis (Fin r) (Robba K) N := Module.finBasisOfFinrankEq _ _ rfl
  let bI : Basis (Fin r) (Robba K) I := Module.finBasisOfFinrankEq _ _ hrank
  obtain ⟨f, hf0, hf⟩ := exists_det_mul_eq_of_le hIN hI hN bI bN
  have uI := (isPhiModule_iff_isUnit_det bI _).1 hIphi
  have uN := (isPhiModule_iff_isUnit_det bN _).1 hNphi
  rw [deg_eq _ bN _ hNphi, deg_eq _ bI _ hIphi, degIn, degIn]
  set lu : (Robba K)ˣ := uI.unit * uN.unit⁻¹
  have hl : (lu : Robba K) * f = ψ f := by
    have : (uN.unit : Robba K) * (lu * f) = (uN.unit : Robba K) * ψ f := by
      simp only [lu, Units.val_mul, IsUnit.unit_spec]
      calc (phiMatrix bN (restrict Φ N hN)).det *
            ((phiMatrix bI (restrict Φ I hI)).det * ↑uN.unit⁻¹ * f)
          = f * (phiMatrix bI (restrict Φ I hI)).det *
              ((phiMatrix bN (restrict Φ N hN)).det * ↑uN.unit⁻¹) := by ring
        _ = f * (phiMatrix bI (restrict Φ I hI)).det := by
              rw [uN.mul_val_inv, mul_one]
        _ = _ := hf
    exact (uN.unit.isUnit.mul_left_cancel this)
  have key := Robba.gaussNorm_le_one_of_smul_eq (ι := Unit) hψ hQ (x := fun _ => f)
    (fun h0 => hf0 (congrFun h0 ())) (B := 1)
    (fun i j => by
      by_cases h : i = j
      · subst h; simp [(Robba.intBounded K).one_mem]
      · simp [Matrix.one_apply_ne h, (Robba.intBounded K).zero_mem])
    (Robba.unit_mem_bounded lu) (fun i => by simp [hl])
  have hord := (Robba.ord_nonneg_iff lu).2 key
  have hmul : Robba.ord lu = Robba.ord uI.unit - Robba.ord uN.unit := by
    simp only [lu, Robba.ord_mul]
    have := Robba.ord_mul uN.unit uN.unit⁻¹
    rw [mul_inv_cancel] at this
    have h1 : Robba.ord (1 : (Robba K)ˣ) = 0 := (Robba.ord_eq_zero_iff 1).2 (by
      rw [Units.val_one]
      refine le_antisymm (ciSup_le fun n => ?_) ?_
      · by_cases hn : n = 0
        · subst hn; simp
        · simp [hn]
      · simpa using Robba.norm_coeff_le_norm1 (Robba.bounded K).one_mem 0)
    omega
  change Robba.ord _ ≤ Robba.ord _
  omega

def IsEtale (Ψ : M →ₛₗ[ψ] M) : Prop :=
  ∃ b : Basis (Fin (finrank (Robba K) M)) (Robba K) M,
    (∀ i j, phiMatrix b Ψ i j ∈ Robba.intBounded K) ∧ Robba.norm1 (phiMatrix b Ψ).det = 1

theorem IsEtale.isUnit_det {Ψ : M →ₛₗ[ψ] M} {b : Basis (Fin (finrank (Robba K) M)) (Robba K) M}
    (hb : (∀ i j, phiMatrix b Ψ i j ∈ Robba.intBounded K) ∧ Robba.norm1 (phiMatrix b Ψ).det = 1) :
    IsUnit (phiMatrix b Ψ).det := by
  have hmem := det_mem_of_forall_mem _ _ hb.1
  refine Robba.isUnit_of_mem_bounded hmem.1 fun h0 => ?_
  have := hb.2
  rw [h0] at this
  simp [Robba.norm1] at this

theorem IsEtale.isPhiModule {Ψ : M →ₛₗ[ψ] M} (h : IsEtale Ψ) : IsPhiModule Ψ := by
  obtain ⟨b, hb⟩ := h
  exact (isPhiModule_iff_isUnit_det b Ψ).2 (IsEtale.isUnit_det hb)

theorem IsEtale.deg_eq_zero (hψn : ∀ u : (Robba K)ˣ, Robba.norm1 (ψ u) = Robba.norm1 (u : Robba K))
    {Ψ : M →ₛₗ[ψ] M} (h : IsEtale Ψ) : deg (Robba.unitOrd ψ hψn) Ψ = 0 := by
  classical
  obtain ⟨b, hb⟩ := h
  rw [deg_eq _ b _ ((isPhiModule_iff_isUnit_det b Ψ).2 (IsEtale.isUnit_det hb)), degIn]
  exact (Robba.ord_eq_zero_iff _).2 hb.2

theorem mul_map_eq_mul_phiMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Ψ : M →ₛₗ[ψ] M} (b : Basis ι (Robba K) M) {N : Submodule (Robba K) M}
    (h : IsStable Ψ N) (bN : Basis κ (Robba K) N) :
    phiMatrix b Ψ * (Matrix.of fun i j => b.repr (bN j : M) i).map ψ =
      (Matrix.of fun i j => b.repr (bN j : M) i) * phiMatrix bN (restrict Ψ N h) := by
  ext i j
  have lhs : (phiMatrix b Ψ * (Matrix.of fun i j => b.repr (bN j : M) i).map ψ) i j =
      b.repr (Ψ (bN j : M)) i := by
    rw [repr_phi]
    simp [Matrix.mul_apply, mulVec, dotProduct]
  have rhs : ((Matrix.of fun i j => b.repr (bN j : M) i) * phiMatrix bN (restrict Ψ N h)) i j =
      b.repr (Ψ (bN j : M)) i := by
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, phiMatrix_apply]
    have := congrArg (fun z : N => b.repr (z : M) i) (bN.sum_repr (restrict Ψ N h (bN j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, coe_restrict_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [lhs, rhs]

theorem deg_restrict_nonneg_of_isEtale (hψ : Robba.IsGaussScaling ψ Q) (hQ : 0 < Q)
    (hψn : ∀ u : (Robba K)ˣ, Robba.norm1 (ψ u) = Robba.norm1 (u : Robba K))
    {Ψ : M →ₛₗ[ψ] M} (hΨ : IsEtale Ψ) {N : Submodule (Robba K) M} (h : IsStable Ψ N)
    [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.Free (Robba K) N] [Module.Finite (Robba K) N] :
    0 ≤ deg (Robba.unitOrd ψ hψn) (restrict Ψ N h) := by
  classical
  obtain ⟨b, hb⟩ := hΨ
  have hNphi := isPhiModule_restrict ((isPhiModule_iff_isUnit_det b Ψ).2 (IsEtale.isUnit_det hb)) h
  set k := finrank (Robba K) N
  let bN : Basis (Fin k) (Robba K) N := Module.finBasisOfFinrankEq _ _ rfl
  set Y : Matrix (Fin (finrank (Robba K) M)) (Fin k) (Robba K) :=
    Matrix.of fun i j => b.repr (bN j : M) i
  set C := phiMatrix bN (restrict Ψ N h)
  have hrel := mul_map_eq_mul_phiMatrix b h bN
  have hx : maxMinor Y ≠ 0 := by
    rw [maxMinor_ne_zero_iff_linearIndependent]
    have hli := bN.linearIndependent.map' (b.equivFun.toLinearMap ∘ₗ N.subtype)
      (by rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_subtype])
    have hcol : Y.col = (b.equivFun.toLinearMap ∘ₗ N.subtype) ∘ bN := by
      funext j i
      simp [Y, Matrix.col, Basis.equivFun_apply]
    rw [hcol]
    exact hli
  have hC := (isPhiModule_iff_isUnit_det bN _).1 hNphi
  have key := compound_mulVec_map_maxMinor_of_mul_eq ψ (phiMatrix b Ψ) Y C hrel
  have hle := Robba.gaussNorm_le_one_of_smul_eq hψ hQ hx (B := compound k (phiMatrix b Ψ))
    (fun s t => det_mem_of_forall_mem _ _ fun i j => hb.1 _ _)
    (Robba.unit_mem_bounded hC.unit) (fun s => by
      have := congrFun key s
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [IsUnit.unit_spec, ← this])
  rw [deg_eq _ bN _ hNphi, degIn]
  exact (Robba.ord_nonneg_iff _).2 hle

end PhiModule

end GroundTheory.PAdicHodge
