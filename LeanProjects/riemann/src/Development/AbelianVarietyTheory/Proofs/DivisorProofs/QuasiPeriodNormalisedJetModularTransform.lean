import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSl2IntSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirectionStatement

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma length_word_eq_sum {I : Type} [Fintype I] (κ : I → ℕ) :
    (_root_.GlobalTheory.HilbFam.word κ).length = ∑ i, κ i := by
  unfold _root_.GlobalTheory.HilbFam.word
  simp [List.length_flatMap, Finset.sum_toList]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma lineDeriv_const_mul_comp_smul {I : Type} (f : (I → ℂ) → ℂ) (a c : ℂ)
    (z v : I → ℂ) :
    lineDeriv ℂ (fun z => a * f (c • z)) z v = a * c * lineDeriv ℂ f (c • z) v := by
  simp only [lineDeriv]
  have h : (fun t : ℂ => a * f (c • (z + t • v))) =
      fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm c t]
  rw [h]
  calc deriv (fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t)) 0
      = a * deriv (fun t => (fun s : ℂ => f (c • z + s • v)) (c * t)) 0 := by
        rw [deriv_const_mul_field']
    _ = a * (c • deriv (fun s : ℂ => f (c • z + s • v)) (c * 0)) :=
        congrArg (a * ·) (deriv_comp_mul_left c (fun s : ℂ => f (c • z + s • v)) 0)
    _ = a * c * deriv (fun t : ℂ => f (c • z + t • v)) 0 := by
        rw [mul_zero, smul_eq_mul, mul_assoc]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_comp_smul {I : Type} [DecidableEq I] (c : ℂ)
    (u : List I) (f : (I → ℂ) → ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z => f (c • z)) z =
      c ^ u.length * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u f (c • z) := by
  induction u generalizing z with
  | nil => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | cons i u ih =>
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD, List.foldr_cons] at ih ⊢
    rw [show List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD (fun z => f (c • z)) u =
      fun z => c ^ u.length * List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD f u (c • z) from funext ih]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
    rw [lineDeriv_const_mul_comp_smul, List.length_cons, pow_succ]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma jet_mul_eq_pow_sum_mul {F : Type} [Field F] [NumberField F] (k : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (τ c t lam : ℂ) :
    _root_.GlobalTheory.HilbFam.jet k L κ τ (lam * c) (lam * t) =
      lam ^ (∑ i, κ i) * _root_.GlobalTheory.HilbFam.jet k L κ τ c t := by
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← length_word_eq_sum κ, ← smul_zero lam,
    ← iterD_comp_smul]
  congr 1
  · funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 2 <;> funext i <;> ring
  · exact smul_zero lam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.hfun_slash : _root_.GlobalTheory.LatJet.EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F), 1 ≤ s → 0 < N → _root_.GlobalTheory.HilbFam.HasLevel N L → ∀ (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', _root_.GlobalTheory.HilbFam.HasLevel N L' ∧ L' = _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → _root_.GlobalTheory.HilbFam.hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ _root_.GlobalTheory.HilbFam.wt (2 * s) κ * _root_.GlobalTheory.HilbFam.hfun (2 * s) (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  intro _ F _ _ _ _ s N L _ _ _ κ γ Ch Ch' τ _ hCh
  have hP : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [_root_.GlobalTheory.HilbFam.hfun]
  rw [_root_.GlobalTheory.HilbFam.JetModular.jet_smul F (2 * s) L κ γ τ _ _ (even_two_mul s)]
  set j : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj
  set P : ℂ := 2 * Real.pi * Complex.I with hPdef
  have hc : P ^ 2 * Ch (γ • τ) - -P * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * j =
      j ^ 2 * (P ^ 2 * Ch' τ) := by
    rw [hCh]
    field_simp
    ring
  rw [hc, show -P * j ^ 2 = j ^ 2 * -P by ring, jet_mul_eq_pow_sum_mul,
    _root_.GlobalTheory.HilbFam.wt, ← pow_mul, pow_add j]
  ring

end GlobalTheory.HilbFam
