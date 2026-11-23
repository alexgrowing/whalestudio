import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.HeckeGal.Model UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

theorem winC_of_unitary {π : CG K n} (hu : π.IsUnitary) {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    WinC 1 (Real.sqrt (normV w)) (B.map fun b : ℂˣ => (b : ℂ)) := by
  have hq : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq1 : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℕ) := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    obtain ⟨h1, h2⟩ := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound K n π hu w B hB a ha
    rw [hq, Real.sqrt_eq_rpow, mul_one]
    refine ⟨?_, h2⟩
    rw [Real.rpow_neg hq1.le, inv_lt_iff_one_lt_mul₀' (Real.rpow_pos_of_pos hq1 _)] at h1
    exact h1
  · induction π using Quotient.inductionOn with | _ π =>
    obtain ⟨ω, hω1, hω⟩ := hu
    have e := PositivityTheory.jumpWindows.PSmo.val_eq_prod (π := π) hω hB
    rw [one_pow, show (B.map fun b : ℂˣ => (b : ℂ)).prod = ((B.prod : ℂˣ) : ℂ) from (map_multiset_prod (Units.coeHom ℂ) B).symm, ← e]
    exact hω1 _

theorem unitary_twist (hn : 1 ≤ n) (π : CuspSub K n) (t : ℝ) (m : Multiset ℂ) (hm : ∀ τ, π.HasInfChar τ m)
    (hc : m.card = n) (ht : m.sum = (n : ℂ) * t) : (CG.mk (π.twist (absPow K (-t)))).IsUnitary := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary K ⟨n, π.twist (absPow K (-t))⟩ hn
  refine h2.1 (h1.1 ?_)
  rw [GlobalTheory.ResW.rexp, GlobalTheory.UnitLocWeight.cex_eq, Finset.sum_eq_zero]
  · simp
  intro τ _
  have k := (hm τ).twist (absPow K (-t))
  rw [(InfType.expo_of_infType K _).2.1 (-t) (absPow_isAbsPow K (-t)) τ] at k
  rw [CG.HasInfChar.infChar_eq (π := CG.mk _) k, Multiset.sum_map_add, Multiset.map_id', Multiset.map_const',
    Multiset.sum_replicate, hc, ht, nsmul_eq_mul]
  push_cast; ring

theorem win_algSat (hn : 1 ≤ n) (π : CuspSub K n) (m : Fin n → ℤ) (wt : ℤ) (hwt : ∀ i, m i + m i.rev = wt)
    (hm : ∀ τ, π.HasInfChar τ (infOf m)) {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (hB : (CG.mk π).HasSat w B) :
    Win (normV w) (-(wt : ℝ)) (algSat n (normV w) B) := by
  have hq : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq1 : (0 : ℝ) < (normV w : ℕ) := by
    rw [hq]; exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
  set t : ℝ := ((n : ℝ) - 1 + wt) / 2 with ht
  have hs : (infOf m).sum = (n : ℂ) * t := by
    have s2 : ∑ i : Fin n, (m i + m i.rev) = ∑ _i : Fin n, wt := Finset.sum_congr rfl fun i _ => hwt i
    have s3 : ∑ i : Fin n, m i.rev = ∑ i, m i := Equiv.sum_comp Fin.revPerm m
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, s3] at s2
    have s4 : (∑ i, (m i : ℂ)) + ∑ i, (m i : ℂ) = n * wt := by exact_mod_cast s2
    change ∑ i : Fin n, (((n : ℂ) - 1) / 2 + (m i : ℂ)) = _
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht]
    push_cast
    linear_combination s4 / 2
  obtain ⟨h1, h2⟩ := CG.HasSat.twist_absPow hB (-t)
  have W0 := winC_of_unitary (unitary_twist hn π t _ hm (by simp [infOf]) hs) h1
  set ν : ℂˣ := (absPow K (-t)).val w
  have W1 := W0.map_mul (u := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (ν : ℂ)⁻¹)
    (mul_ne_zero (by exact_mod_cast (Real.rpow_pos_of_pos hq1 _).ne') (inv_ne_zero ν.ne_zero))
  rw [norm_mul, norm_inv, h2, ← hq, Complex.norm_real, Real.norm_of_nonneg (by positivity), neg_neg, ← Real.rpow_neg hq1.le,
    ← Real.rpow_add hq1, mul_one] at W1
  unfold Win
  convert W1 using 2
  · rw [ht]; ring
  · simp only [algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul]
    field_simp

end UpperTheory.GalN.V
