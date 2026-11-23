import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOffOfUnramPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLeStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.FlatTwisting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem wtOf_parWt_anti (w : Psi H → ℤ) (τ : E →+* ℂ) (i j : ℕ) (hij : i ≤ j) (hj : j < Dw.mult τ) :
    (wtOf Dw (parWt Dw w) 0).1 (τ, j) ≤ (wtOf Dw (parWt Dw w) 0).1 (τ, i) := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : j < Dw.p := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ j hp
    have e2 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ i (by omega)
    exact (e1.trans e2.symm).le
  · have hq : j < Dw.q := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ j hq
    have e2 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ i (by omega)
    simp only [conjEmb_conjEmb] at e1 e2
    exact (e1.trans e2.symm).le

theorem wtOf_parWt_neg (w : Psi H → ℤ) : wtOf Dw (parWt Dw (-w)) 0 = -wtOf Dw (parWt Dw w) 0 := by
  have h := wtOf_add' (Dw := Dw) (parWt Dw (-w)) (parWt Dw w)
  have h0 : parWt Dw (-w) + parWt Dw w = 0 := by funext τ i; simp [parWt]
  rw [h0, wtOf_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mul_sig_mem_cuspOn (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c} {w : Psi H → ℤ} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ}
    (s : ConstSec U x Z (parWt Dw w) δ) :
    ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s.sig ∈ cuspOn U Z (G + wtOf Dw (parWt Dw w) 0) :=
  GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ s.sig hK hU hpq (even_wtOf _ _) (wtOf_parWt_anti w) s.sig_mem
    s.sig_mem_suppOn fun σ hσ => ⟨s.cInf σ, by
      have e : goodOf c σ = σ := if_pos hσ
      have h : ∀ z ∈ framesOn (U (goodOf c σ)) Z,
          homN (U (goodOf c σ)) x (wtOf Dw (parWt Dw w) 0) s.sig z ≤ s.cInf σ := fun z hz => (s.homN_eq hz).le
      rw [e] at h
      exact h⟩

theorem exists_twSec_of_const {B : Finset ℕ} (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) (Z : Comp Xo c) (w : Psi H → ℤ)
    (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ) (hδ : (Function.support δ).Finite) :
    ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
      t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo := by
  refine ⟨TwSec.ofConst s hδ (mul_sig_mem_cuspOn hK hU hpq s) fun G hG f hf => ?_, rfl, rfl, rfl, rfl,
    intOff_of_unramPts E H Dw l Xo c r U x B hB Z _ δ s⟩
  have h := mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl) (G + wtOf Dw (parWt Dw w) 0)
    (Even.add hG (even_wtOf _ _)) f hf
  rw [wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem finite_sum_flDefect (w : Psi H → ℤ) :
    (Function.support (∑ τ, (-w τ) • flDefect_vw Dw c τ)).Finite := by
  refine (Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun la hla => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
  exact hla (by simp [Finset.sum_apply, hn])

theorem finsum_sum_flDefect (w : Psi H → ℤ) :
    ∑ᶠ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
  have h1 : ∀ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      ∑ τ, (-(w τ : ℝ)) * (flDefect_vw Dw c τ la * lw c.F la) := fun la => by
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]; push_cast; ring
  rw [finsum_congr h1, finsum_sum_comm _ _ fun τ _ =>
    (fin_mul (finite_flDefect_vw τ) (lw c.F)).subset (Function.support_mul_subset_right _ _),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← mul_finsum, sum_flDefect_vw]; ring

theorem twSec_of_flat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ) (B : Finset ℕ) (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) :
    (∀ (Z : Comp Xo c) (w : Psi H → ℤ) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ),
      (Function.support δ).Finite → ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
        t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo) ∧
    (FlatExists U x → ∀ (Z : Comp Xo c) (w : Psi H → ℤ), HasPts U Z →
      ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), IntOff B t.lo ∧
        t.degLo = (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) ∧
        (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * lrd E * (∑ τ, |(w τ : ℝ)|) ≤ t.degLo) := by
  refine ⟨exists_twSec_of_const hK hU hpq hB, fun hF Z w hp => ?_⟩
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF.nonempty Z τ).some
  have hδ := finite_sum_flDefect (Dw := Dw) (c := c) w
  obtain ⟨s, hdeg⟩ : ∃ s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ),
      s.deg = ∑ τ, (w τ : ℝ) * c1 U x τ :=
    ⟨(FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _), (hF.deg_shift hp sF w).trans (by congr; exact Subsingleton.elim _ _)⟩
  obtain ⟨t, -, h2, h3, -, h5⟩ := exists_twSec_of_const hK hU hpq hB Z w _ s hδ
  have key := lineDeg_mul (r := 1) (fun _ => one_pos) s.cInf_pos hδ s.finite_rho
  rw [one_mul] at key
  have hd : t.degLo =
      (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) := by
    have h1 : lineDeg (1 : (c.F →+* ℂ) → ℝ) (∑ τ, (-w τ) • flDefect_vw Dw c τ) =
        -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
      rw [lineDeg, finsum_sum_flDefect]; simp
    rw [TwSec.degLo, h2, h3, key, h1, ← hdeg, ConstSec.deg]; ring
  refine ⟨t, h5, hd, ?_⟩
  have hA := GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le E H
  have hs : (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ) ≤ lrd E * ∑ τ, |(w τ : ℝ)| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
  have := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) Dw.q)
  rw [hd, mul_assoc, mul_assoc]
  linarith

end GlobalTheory.FlatTwisting
