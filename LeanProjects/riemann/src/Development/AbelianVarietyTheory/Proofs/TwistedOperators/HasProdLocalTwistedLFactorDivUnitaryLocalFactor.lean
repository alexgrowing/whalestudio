import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem abs_quadTerm_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) {i : ℕ} (hi : 2 ≤ i) :
    ‖-quadTerm D v i‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm v
  have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp
  rw [norm_neg, Real.norm_eq_abs, quadTerm, abs_div, abs_pow, abs_pow, hs, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)), Real.rpow_neg (by positivity),
    Real.rpow_two]
  have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i :=
    pow_le_pow_right₀ hN.le hi
  rw [one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast h2)

theorem hasProd_dLoc (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => dLoc D v.1) (dOff D Sb) ∧ dOff D Sb ≠ 0 := by
  have ht := D.R.rank_add_five_le
  set f : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV → ℝ :=
    fun p => -quadTerm D p.1.1 p.2.1 with hf
  have hsum0 := summable_rpow (K := D.host.F) (Sb : Set _) (σ := 2) (by norm_num)
  have hsum1 : Summable fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV =>
      ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 : ℝ) := by
    refine summable_mul_of_summable_norm (f := fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ))) (g := fun _ : Finset.Ioc D.R.t D.R.nV => (1 : ℝ)) ?_ ?_
    · refine hsum0.congr fun v => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact Summable.of_finite
  have hsum : Summable fun p => ‖f p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hsum1
    rw [mul_one]
    have := (Finset.mem_Ioc.1 p.2.2).1
    exact abs_quadTerm_le D p.1.1 (by omega)
  have hne : ∀ p, 1 + f p ≠ 0 := fun p => by
    have h1 := abs_quadTerm_le D p.1.1 (i := p.2.1) (by have := (Finset.mem_Ioc.1 p.2.2).1; omega)
    have hN : (1 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm p.1.1
    have h2 : ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hN (by norm_num)
    intro h0
    have : f p = -1 := by linarith
    rw [hf] at this
    simp only at this
    rw [this, norm_neg, norm_one] at h1
    linarith
  have hm := multipliable_one_add_of_summable hsum
  have hz := tprod_one_add_ne_zero_of_summable hne hsum
  have hinv : HasProd (fun p => (1 + f p)⁻¹) (∏' p, (1 + f p))⁻¹ := hm.hasProd.inv₀ hz
  have e1 : (fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV => (1 + f p)⁻¹) =
      fun p => (1 - quadTerm D p.1.1 p.2.1)⁻¹ := by
    funext p; rw [hf]; ring_nf
  rw [e1] at hinv
  have hd : dOff D Sb = (∏' p, (1 + f p))⁻¹ := hinv.tprod_eq
  refine ⟨?_, hd ▸ inv_ne_zero hz⟩
  rw [hd]
  refine hinv.prod_fiberwise fun v => ?_
  have := hasProd_fintype (fun c : Finset.Ioc D.R.t D.R.nV => (1 - quadTerm D v.1 c.1)⁻¹)
  rw [Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) (fun i => (1 - quadTerm D v.1 i)⁻¹)] at this
  exact this

theorem hasProd_LvTw_div_dLoc : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  intro D Sb B χ h
  have h1 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2)) :=
    hasProd_Lv h
  obtain ⟨h2, h3⟩ := hasProd_dLoc D Sb
  have h4 := (h2.map Complex.ofRealHom Complex.continuous_ofReal).inv₀
    (by simpa using h3 : Complex.ofRealHom (dOff D Sb) ≠ 0)
  have h5 := h1.mul h4
  simpa [div_eq_mul_inv, Function.comp_def] using h5

end GlobalTheory.FinZeta

end
