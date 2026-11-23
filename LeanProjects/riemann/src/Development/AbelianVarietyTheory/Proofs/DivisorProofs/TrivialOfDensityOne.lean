import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TrivialOfDensityOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)

noncomputable section

namespace GlobalTheory.DensityOneTriv

variable {L : Type} [Field L] [NumberField L]

def xP (s : ℝ) (P : HeightOneSpectrum (𝓞 L)) : ℝ := (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)

theorem absNorm_rpow_neg_pos (s : ℝ) (P : HeightOneSpectrum (𝓞 L)) : 0 < xP s P := by
  have hN := NumberField.HeightOneSpectrum.one_lt_absNorm P
  unfold xP
  exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < Ideal.absNorm P.asIdeal)) _

theorem absNorm_rpow_neg_lt_one {s : ℝ} (hs : 1 < s) (P : HeightOneSpectrum (𝓞 L)) : xP s P < 1 := by
  have hN := NumberField.HeightOneSpectrum.one_lt_absNorm P
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by linarith)

theorem cpow_eq_xP (s : ℝ) (P : HeightOneSpectrum (𝓞 L)) :
    ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)) = ((xP s P : ℝ) : ℂ) := by
  unfold xP
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem norm_val {ψ : HChar L} (hu : ψ.IsUnitary) (P : HeightOneSpectrum (𝓞 L)) :
    ‖((ψ.val P : ℂˣ) : ℂ)‖ = 1 := hu _

theorem exp_neg_le_norm_eulerFactor {ψ : HChar L} (hu : ψ.IsUnitary) {s : ℝ} (hs : 1 < s)
    (P : HeightOneSpectrum (𝓞 L)) :
    Real.exp (-xP s P) ≤ ‖GlobalTheory.CMVal.eulerFactor ψ (s : ℂ) P‖ := by
  have h0 := absNorm_rpow_neg_pos s P
  have h1 := absNorm_rpow_neg_lt_one hs P
  unfold GlobalTheory.CMVal.eulerFactor
  split_ifs with hP
  · rw [cpow_eq_xP, norm_inv]
    set c : ℂ := ((ψ.val P : ℂˣ) : ℂ)
    have hc : ‖c‖ = 1 := norm_val hu P
    have hle : ‖1 - c * ((xP s P : ℝ) : ℂ)‖ ≤ 1 + xP s P := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul, hc, Complex.norm_real, Real.norm_of_nonneg h0.le, one_mul]
    have hge : 1 - xP s P ≤ ‖1 - c * ((xP s P : ℝ) : ℂ)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (c * ((xP s P : ℝ) : ℂ))
      rw [norm_one, norm_mul, hc, Complex.norm_real, Real.norm_of_nonneg h0.le, one_mul] at this
      exact this
    have hpos : 0 < ‖1 - c * ((xP s P : ℝ) : ℂ)‖ := by linarith
    rw [Real.exp_neg]
    have he := Real.add_one_le_exp (xP s P)
    exact inv_anti₀ hpos (by linarith)
  · rw [norm_one]
    exact Real.exp_le_one_iff.2 (by linarith)

theorem exp_le_norm_eulerFactor {ψ : HChar L} {s : ℝ} (hs : 1 < s) {P : HeightOneSpectrum (𝓞 L)}
    (hP : ψ.UnrAt P) (h1 : ψ.val P = 1) :
    Real.exp (xP s P) ≤ ‖GlobalTheory.CMVal.eulerFactor ψ (s : ℂ) P‖ := by
  have h0 := absNorm_rpow_neg_pos s P
  have hl := absNorm_rpow_neg_lt_one hs P
  unfold GlobalTheory.CMVal.eulerFactor
  rw [if_pos hP, cpow_eq_xP, h1, Units.val_one, one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (by linarith))]
  have he := Real.add_one_le_exp (-xP s P)
  calc Real.exp (xP s P) = (Real.exp (-xP s P))⁻¹ := by rw [Real.exp_neg, inv_inv]
    _ ≤ (1 - xP s P)⁻¹ := inv_anti₀ (by linarith) (by linarith)

theorem exp_le_norm_of_hasProd {ψ : HChar L} (hu : ψ.IsUnitary) {S : Set (HeightOneSpectrum (𝓞 L))}
    (hS : ∀ P ∈ S, ψ.UnrAt P ∧ ψ.val P = 1) {s : ℝ} (hs : 1 < s) {a : ℂ}
    (ha : HasProd (GlobalTheory.CMVal.eulerFactor ψ (s : ℂ)) a) :
    Real.exp (2 * NumberField.Set.primeIdealZetaSum S s -
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 L))) s) ≤ ‖a‖ := by
  classical
  have hsum : Summable (xP (L := L) s) := GlobalTheory.HeckeOne.sumN (K := L) s hs
  have hx : HasSum (xP (L := L) s)
      (NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 L))) s) := by
    rw [NumberField.Set.primeIdealZetaSum_def, tsum_univ (fun P : HeightOneSpectrum (𝓞 L) =>
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))]
    exact hsum.hasSum
  have hS' : HasSum (S.indicator (xP (L := L) s)) (NumberField.Set.primeIdealZetaSum S s) := by
    rw [NumberField.Set.primeIdealZetaSum_def, tsum_subtype S (fun P : HeightOneSpectrum (𝓞 L) =>
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))]
    exact (hsum.indicator S).hasSum
  set e : HeightOneSpectrum (𝓞 L) → ℝ := fun P => if P ∈ S then xP s P else -xP s P with he
  have he' : HasSum e (2 * NumberField.Set.primeIdealZetaSum S s -
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 L))) s) := by
    have hfun : e = fun P => 2 * S.indicator (xP s) P - xP s P := by
      funext P
      by_cases hP : P ∈ S
      · simp [he, hP]; ring
      · simp [he, hP]
    rw [hfun]
    exact (hS'.mul_left 2).sub hx
  have hE := he'.rexp
  have hN := ha.norm
  refine le_of_tendsto_of_tendsto' hE hN fun F => ?_
  refine Finset.prod_le_prod (fun P _ => (Real.exp_pos _).le) fun P _ => ?_
  simp only [Function.comp_apply, he]
  split_ifs with hP
  · exact exp_le_norm_eulerFactor hs (hS P hP).1 (hS P hP).2
  · exact exp_neg_le_norm_eulerFactor hu hs P

theorem trivialOfDensityOne : GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters.TrivialOfDensityOne := by
  intro L _ _ χ hχ hu S hS hv
  by_contra hne
  let ψ : HChar L := ⟨χ, hχ⟩
  have hψ : ψ ≠ 1 := fun h => hne (congrArg Subtype.val h)
  obtain ⟨Λ, ⟨han, hprod⟩, hΛ1⟩ := (GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds L ψ hu).2 hψ
  have hSv : ∀ P ∈ S, ψ.UnrAt P ∧ ψ.val P = 1 := fun P hP =>
    ⟨(GlobalTheory.HeckeSplit.unrAt_iff L ψ P).1 (hv P hP).1, (hv P hP).2 _ (Formalism.L2.Host.unif_spec P)⟩
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => ‖Λ s‖) (𝓝[>] 1) (𝓝 ‖Λ 1‖) :=
    (han.continuousAt.tendsto.comp hc).norm
  have hall := GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop L
  have hr : ∀ᶠ s in 𝓝[>] (1 : ℝ), 3 / 4 < NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 L))) s :=
    hS.eventually (lt_mem_nhds (by norm_num))
  have hT : Tendsto (fun s : ℝ => 2 * NumberField.Set.primeIdealZetaSum S s -
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 L))) s)
      (𝓝[>] 1) atTop := by
    refine tendsto_atTop_mono' _ ?_ (hall.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hr, hall.eventually_gt_atTop 0] with s h1 h2
    rw [lt_div_iff₀ h2] at h1
    linarith
  have hbig : Tendsto (fun s : ℝ => ‖Λ s‖) (𝓝[>] 1) atTop := by
    refine tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.comp hT)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact exp_le_norm_of_hasProd (ψ := ψ) hu hSv hs (hprod s (by simpa using hs))
  exact not_tendsto_atTop_of_tendsto_nhds hlim hbig

end GlobalTheory.DensityOneTriv
