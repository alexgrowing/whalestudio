import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEllStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem powerSeries_exists_sum {O : Type} [CommRing O] (a : ℕ → PowerSeries O) :
    ∃ s : PowerSeries O, ∀ m, ∃ b,
      s = ∑ i ∈ Finset.range m, PowerSeries.X ^ i * a i + PowerSeries.X ^ m * b := by
  set s : PowerSeries O := PowerSeries.mk fun n =>
    PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1), PowerSeries.X ^ i * a i) with hs
  refine ⟨s, fun m => ?_⟩
  have hdvd : PowerSeries.X ^ m ∣ s - ∑ i ∈ Finset.range m, PowerSeries.X ^ i * a i := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, hs, PowerSeries.coeff_mk, sub_eq_zero]

    have key : ∀ d, PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1 + d), PowerSeries.X ^ i * a i)
        = PowerSeries.coeff (R := O) n (∑ i ∈ Finset.range (n + 1), PowerSeries.X ^ i * a i) := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [show n + 1 + (d + 1) = n + 1 + d + 1 by omega, Finset.sum_range_succ, map_add, ih,
          PowerSeries.coeff_X_pow_mul', if_neg (by omega), add_zero]
    have := key (m - (n + 1))
    rw [show n + 1 + (m - (n + 1)) = m by omega] at this
    exact this.symm
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨b, by rw [← hb]; ring⟩

theorem letA_exists_sum {O : Type} [CommRing O] {n : ℕ} (a : ℕ → LetA O n) :
    ∃ s : LetA O n, ∀ m, ∃ b, s = ∑ i ∈ Finset.range m, letπ ^ i * a i + letπ ^ m * b := by
  choose s hs using fun k : ZMod n => powerSeries_exists_sum (fun i => a i k)
  refine ⟨s, fun m => ?_⟩
  choose b hb using fun k => hs k m
  refine ⟨b, ?_⟩
  funext k
  rw [hb k]
  unfold letπ
  simp [Finset.sum_apply, Pi.pow_apply, Pi.mul_apply]

theorem near_closed_abstract {A E S R : Type} [CommRing A] [CommRing E] [CommRing S] [CommRing R]
    (j : A →+* E) (io : A →+* S) (ι : S →+* R) (f : E →+* R) (p : ℕ) (π : A) (t : R)
    (hext : ∀ a, f (j a) = ι (io a)) (ht : ι (io π) = t)
    (hsum : ∀ a : ℕ → A, ∃ s, ∀ m, ∃ b, s = ∑ i ∈ Finset.range m, π ^ i * a i + π ^ m * b)
    (hsep : ∀ x : R, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (hE : ∀ m e, Near ι p t m (f e) → ∃ a e', e = j (π ^ m * a) + (p : E) * e')
    (x : R) (hx : ∀ m, ∃ e, Near ι p t m (x - f e)) : ∃ e r, x - f e = (p : R) * r := by
  unfold Near at hsep hE hx
  choose e he using hx

  have hD : ∀ i, ∃ a r, f (e (i + 1) - e i) = t ^ i * ι a + (p : R) * r := by
    intro i
    obtain ⟨a0, r0, h0⟩ := he i
    obtain ⟨a1, r1, h1⟩ := he (i + 1)
    refine ⟨a0 - io π * a1, r0 - r1, ?_⟩
    have hsplit : f (e (i + 1) - e i) = (x - f (e i)) - (x - f (e (i + 1))) := by
      rw [map_sub]; ring
    rw [hsplit, h0, h1, map_sub, map_mul, ht]
    ring
  choose a e' hae using fun i => hE i _ (hD i)
  obtain ⟨s, hs⟩ := hsum a
  have hsumD : ∀ m, e m = e 0 + j (∑ i ∈ Finset.range m, π ^ i * a i) +
      (p : E) * ∑ i ∈ Finset.range m, e' i := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, map_add]
      linear_combination hae k + ih
  refine ⟨e 0 + j s, hsep _ fun m => ?_⟩
  obtain ⟨b, hb⟩ := hs m
  obtain ⟨a0, r0, h0⟩ := he m
  refine ⟨a0 - io b, r0 + f (∑ i ∈ Finset.range m, e' i), ?_⟩
  have key : f (e 0 + j s) = f (e m) - (p : R) * f (∑ i ∈ Finset.range m, e' i) + t ^ m * ι (io b) := by
    rw [hsumD m, hb]
    simp only [map_add, map_mul, map_pow, map_natCast, hext, ht]
    ring
  rw [key, map_sub]
  linear_combination h0

set_option maxHeartbeats 1000000 in
private theorem ioE_closed_lemma (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL)
    (hx : ∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) : ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  obtain ⟨hsep, -⟩ := GlobalTheory.T.nearPi_sep_complete_alt l P AI LL s
  obtain ⟨hE, -⟩ := GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell l P AI K s LL h W E
  have hext : ∀ a, E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE a) =
      inclR LL (E.tie.io a) := by
    intro a
    exact E.tie.ioE_ext a
  have ht : inclR LL (E.tie.io letπ) = piR AI LL s := by
    rw [E.tie.io_π]
    rfl

  have hN : ∀ m y, NearPi AI LL s m y ↔ Near (inclR LL : RA LL →+* RW LL) l (piR AI LL s) m y :=
    fun _ _ => Iff.rfl
  simp only [hN] at hsep hE hx
  exact near_closed_abstract (algebraMap _ W.EE) (E.tie.io : _ →+* RA LL) (inclR LL : RA LL →+* RW LL)
    (E.tie.ioE : W.EE →+* RW LL) l letπ (piR AI LL s) hext ht letA_exists_sum hsep hE x hx

theorem ioE_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  intro l _ P AI K s LL h W E x hx
  exact ioE_closed_lemma l P AI K s LL h W E x hx

end GlobalTheory.Decompl
