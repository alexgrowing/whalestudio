import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA (Dinv xi_mem_Dinv int_of_xi)
open GlobalTheory.FunObj.Good (char_int mem_Dinv atPl_mul inc_mul_inc mem_intAE exists_pole isEquiv_Kw valued_alg psiAt_eq_one
  trace_inc_pair cpt_pair)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

namespace CondAA

theorem valued_genAt (w : Pl D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Valued.v ((genAt w 𝔞 : (Kw w)ˣ) : Kw w) = WithZero.exp (-FractionalIdeal.count D.host.E w 𝔞) := by
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [genAt, Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

theorem exists_mem_valuation_eq (w : Pl D.host.E) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) :
    ∃ c ∈ I, w.valuation D.host.E c = WithZero.exp (-FractionalIdeal.count D.host.E w I) := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  have hIw : I * w.asIdeal ≠ 0 := mul_ne_zero hI hw0
  have hne : ¬ I ≤ I * w.asIdeal := fun h => by
    have := FractionalIdeal.count_mono D.host.E w hI h
    rw [FractionalIdeal.count_mul D.host.E w hI hw0, FractionalIdeal.count_self] at this
    omega
  obtain ⟨c, hc, hc'⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨c, hc, le_antisymm ((GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc w) ?_⟩
  by_contra hlt
  push_neg at hlt
  refine hc' ((GlobalTheory.Idele.mem_iff_valuation_le hIw c).2 fun Q => ?_)
  rw [FractionalIdeal.count_mul D.host.E Q hI hw0]
  by_cases hQ : w = Q
  · subst hQ
    rw [FractionalIdeal.count_self]
    rcases eq_or_ne (w.valuation D.host.E c) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0, WithZero.exp_lt_exp] at hlt
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  · rw [FractionalIdeal.count_maximal_coprime D.host.E Q hQ, add_zero]
    exact (GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc Q

end CondAA

open CondAA in

theorem hasConductor_psiAt_AA {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E) :
    HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar) := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have e := isEquiv_Kw w
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero hP D
  have hB : D.host.AAbar ≠ 0 := fun h => by
    have h1 := hP D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hI : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero hA hB
  set n := FractionalIdeal.count D.host.E w (D.host.AA * D.host.AAbar) with hn
  have hv : Valued.v (((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ)) : Kw w) = WithZero.exp (-n) := by
    rw [Units.val_mul, map_mul, valued_genAt, valued_genAt, ← WithZero.exp_add, hn,
      FractionalIdeal.count_mul D.host.E w hA hB, neg_add]
  have hint : ∀ y : Kw w, Valued.v y ≤ 1 → finPart D (atPl w y) ∈ intAE D := fun y hy => mem_intAE fun Q => by
    rw [(atPl_spec w y).2]
    by_cases h : Q = w
    · subst h; simpa using hy
    · simp [h]
  intro x
  rw [e x, hv]
  refine ⟨fun h => ?_, fun hx y hy => ?_⟩
  · by_contra hx
    obtain ⟨u, hu, hu1, hu2⟩ := exists_pole w
    refine hu (int_of_xi hP D fun a ha j hj => mem_Dinv.2 fun c => ?_)
    have hx1 : WithZero.exp (-n + 1) ≤ Valued.v x := by
      have h0 : Valued.v x ≠ 0 := fun h0 => hx (h0 ▸ zero_le')
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at hx
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    have haj : w.valuation D.host.E (a * j) ≤ WithZero.exp (-n) :=
      (GlobalTheory.Idele.mem_iff_valuation_le hI (a * j)).1 (FractionalIdeal.mul_mem_mul ha hj) w
    have hn' : D.host.xi0 * (a * j) * c ∈ Dinv D := by
      rw [mul_comm]
      exact (Dinv D).coeToSubmodule.smul_mem c (xi_mem_Dinv hP D ha hj)
    have h1 := (psiAt_eq_one W w _).1 (h (algebraMap D.host.E (Kw w) (a * j * c) * algebraMap D.host.E (Kw w) u) (by
      rw [e, map_mul, valued_alg, valued_alg, map_mul]
      refine le_trans ?_ hx1
      calc _ ≤ WithZero.exp (-n) * 1 * WithZero.exp (1 : ℤ) :=
            mul_le_mul' (mul_le_mul' haj (w.valuation_le_one c)) hu1
        _ = _ := by rw [mul_one, ← WithZero.exp_add]))
    rw [atPl_mul, inc_mul_inc] at h1
    have h2 := char_int W.ψ_std hn' (z := pairA D.host.F 0 1 ⊗ₜ[D.host.F] u - atPl w (algebraMap D.host.E (Kw w) u))
      (by rw [RingHom.map_sub, GlobalTheory.LatVac.infPart_pair, (atPl_spec w _).1, sub_zero]) (mem_intAE fun Q => by
        rw [RingHom.map_sub, RingHom.map_sub, cpt_pair, (atPl_spec w _).2]
        by_cases hQ : Q = w
        · subst hQ; simp
        · rw [Pi.single_eq_of_ne hQ, sub_zero, valued_alg]
          exact hu2 Q hQ)
    rw [← mul_assoc D.host.xi0, ← mul_assoc D.host.xi0] at h1
    rw [← mul_assoc D.host.xi0] at h2
    have h3 : W.ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D (D.host.xi0 * a * j * c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u))) = 1 := by
      rw [← sub_add_cancel (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u : AE D) (atPl w (algebraMap D.host.E (Kw w) u)), mul_add,
        map_add, W.ψ.map_add_eq_mul, h1, h2, one_mul]
    rw [trace_inc_pair, one_mul, GlobalTheory.LatVac.char_rat W.ψ_std] at h3
    rwa [show D.host.xi0 * (a * (j * u)) * c = D.host.xi0 * a * j * c * u by ring]
  · obtain ⟨c, hc, hcv⟩ := exists_mem_valuation_eq w hI
    have hy1 : Valued.v y ≤ WithZero.exp (-n) := ((e y x).1 hy).trans hx
    have hξc : D.host.xi0 * c ∈ Dinv D := by
      rw [show Dinv D = _ from (Formalism.L2.Pj.dual_eq hP D).symm, mul_assoc]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc
    have hvc : Valued.v (algebraMap D.host.E (Kw w) c) = WithZero.exp (-n) := by rw [valued_alg, hcv]
    have h0 : algebraMap D.host.E (Kw w) c ≠ 0 := fun h => by
      rw [h, map_zero] at hvc
      exact WithZero.exp_ne_zero hvc.symm
    rw [psiAt_eq_one, ← mul_inv_cancel_left₀ h0 y, atPl_mul, inc_mul_inc]
    refine char_int W.ψ_std hξc (atPl_spec w _).1 (hint _ ?_)
    rw [map_mul, map_inv₀, hvc]
    calc _ ≤ (WithZero.exp (-n))⁻¹ * WithZero.exp (-n) := mul_le_mul' le_rfl hy1
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.FunObj

end
