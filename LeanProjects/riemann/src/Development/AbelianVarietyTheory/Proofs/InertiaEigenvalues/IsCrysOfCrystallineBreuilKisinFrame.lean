import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrameStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrTop

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pow_cancel {R : Type} [CommRing R] {lr : R} (h : ∀ x : R, lr * x = 0 → x = 0) (n : ℕ) :
    ∀ x : R, lr ^ n * x = 0 → x = 0 := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; exact ih x (h _ (by rw [← mul_assoc, ← pow_succ']; exact hx))

theorem smul_cancel {R : Type} [CommRing R] {c : R} (h : ∀ x : R, c * x = 0 → x = 0) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} (hM : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun hM i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.1 (h _ (by rw [mul_sub, this, sub_self]))

theorem crys_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hcr
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, hR1, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨k, Q, Q', hQQ, hQu, hQ'u, hQφ⟩ := GlobalTheory.T.exists_frobenius_section_acris_breuilKisin l K bk N d F.A F.A' F.A_mul
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι

  have key : ∀ g : ↥(GK K), (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q := by
    intro g
    set σ := sigA (g : GQ l) with hσdef
    set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
    set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
    set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
    have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
      simp only [hfA, RingHom.comp_apply, bk.ev_frob]
    have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
    have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => by
      simp only [hσdef]
      exact GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
    have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
      obtain ⟨w, hw⟩ := bk.coeff_zero
      have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
        rw [← hw]; simp
      refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
      simp [hf0, hc]

    have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
      ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
    have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
    have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
    have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
      have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
      simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
      convert e using 3
      · rw [hfr]
      · ext i j; simp [hε']
      · ext i j; simp only [Matrix.map_apply, Function.comp_apply, RingHom.comp_apply]; rw [hσf]
      · rw [hσf]
      · ext i j; simp only [Matrix.map_apply, Function.comp_apply, RingHom.comp_apply]; rw [hfr]
      · ext i j; simp only [Matrix.map_apply, Function.comp_apply, RingHom.comp_apply, hε']; rw [hφι]
    have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
      (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2

    obtain ⟨w₀, hw₀⟩ := he₀
    set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
    have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
      rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
      congr 1
      rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]

    set u := ι (bk.ev X) with hu
    set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
    have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
      constructor
      · intro h; ext i j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
      · intro h i j
        have := congrFun (congrFun h i) j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
    have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
    have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
      rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
      exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
    have hε1 : ε'.map π = 1 := by
      have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
        obtain ⟨c, hc⟩ := hcr g i j
        have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
          simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        rw [e1, hc, map_mul, map_mul]
        exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
      rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
      exact (hz _).1 this
    have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      have hdσ : u ∣ σ u := by
        rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
      have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
        have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
            σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        obtain ⟨c, hc⟩ := hQu i j
        rw [e1, hc, map_mul]
        exact dvd_mul_of_dvd_left hdσ _
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
    have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
      refine (hz D).2 ?_
      rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
      simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
      rw [← pow_add, ← two_mul, sub_self]
    have hD0 := GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
    have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
      sub_eq_zero.1 hD0
    refine smul_cancel (pow_cancel htf (2 * k)) ?_
    have := congrArg (fun M => Q * M) hM
    simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame l K bk τ hτ N d k ρ Y Y' F.ε Q Q' hYY hR1 hQQ key
  exact GlobalTheory.T.isCrystalline_of_invariant_unit_bcris_matrix l K P AI T d ρ U hU hinv

end GlobalTheory.CrTop
