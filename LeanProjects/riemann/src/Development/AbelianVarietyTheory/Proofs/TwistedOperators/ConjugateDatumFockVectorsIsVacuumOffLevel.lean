import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVectoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevelStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacua

open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem delta_orth {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
    {P Q : HeightOneSpectrum (𝓞 D.host.E)} {a b : AE D} (ha : IsDelta Φ P a) (hb : IsDelta Φ Q b) (h : P ≠ Q) :
    a * b = 0 := by
  refine hΦ.ext' (by rw [RingHom.map_mul, ha.1, zero_mul, RingHom.map_zero]) fun Q' => ?_
  rw [ev_mul, ev_zero]
  by_cases hQ : Q' = P
  · rw [hb.2.2 Q' (hQ ▸ h), mul_zero]
  · rw [ha.2.2 Q' hQ, zero_mul]

theorem half_orth {m n : ℕ} {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {u : Matrix (Fin m) (Fin n) (AE D)}
    (hu : IsHalf e u ∨ IsHalf (cA D e) u) :
    u.map (infPart D) = 0 ∧ ∀ (S : Finset (Pl D.host.E)) (e' : AE D), IsIdemSum e' S →
      (∀ PP ∈ S, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ i j, e' * u i j = 0 ∧ cA D e' * u i j = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := (of_isPrimeIdem hΦ h).1
  obtain ⟨Q, a, hQ, ha, hu⟩ : ∃ Q a, (Q = P ∨ Q = cP P) ∧ IsDelta Φ Q a ∧ ∀ i j, a * u i j = u i j := by
    rcases hu with hu | hu
    exacts [⟨P, e, Or.inl rfl, hd, hu⟩, ⟨cP P, cA D e, Or.inr rfl, delta_conj hΦ hd, hu⟩]
  refine ⟨Matrix.ext fun i j => ?_, ?_⟩
  · rw [Matrix.map_apply, ← hu, RingHom.map_mul, ha.1, zero_mul, Matrix.zero_apply]
  · rintro S e' ⟨⟨es, hes, rfl⟩, -⟩ hS i j
    have key : ∀ PP ∈ S, PP ≠ Q ∧ cP PP ≠ Q := fun PP hPP => by
      obtain ⟨h1, h2⟩ := hS PP hPP
      rw [isConjPl_iff] at h2
      rcases hQ with rfl | rfl
      · exact ⟨h1, Ne.symm h2⟩
      · exact ⟨fun e => h2 (by rw [e, cP_cP]), fun e => h1 (by rw [← cP_cP PP, e, cP_cP])⟩
    have k1 : (∑ PP ∈ S, es PP) * a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP => delta_orth hΦ (delta_of_isIdemAt hΦ (hes PP hPP)) ha (key PP hPP).1
    have k2 : cA D (∑ PP ∈ S, es PP) * a = 0 := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP =>
        delta_orth hΦ (delta_conj hΦ (delta_of_isIdemAt hΦ (hes PP hPP))) ha (key PP hPP).2
    rw [← hu, ← mul_assoc, ← mul_assoc, k1, k2, zero_mul]
    exact ⟨rfl, rfl⟩

theorem isVacAt_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hθ i σ f₀ f B hV P hP φ
  obtain ⟨⟨-, hvac⟩, e, he, hth⟩ := hV.vec
  obtain ⟨c, hc⟩ := hL.βV i
  obtain ⟨c', hc'⟩ := hL.βW i
  rw [one_pow] at hc hc'
  have h0 : GlobalTheory.Hk3.IsVacAt R.ψ _ _ P f₀ :=
    GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level R.ψ _ _ (R.βV i) (R.βW i) (R.ΛV i) (R.ΛW i) 1 1 hc hc' P
      (by rw [mul_one, Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)) f₀ hvac.theta hvac.lat
  refine ⟨hV.theta φ, fun e' f' h' u hu hh => ?_⟩
  obtain ⟨h1, h2⟩ := half_orth h' hh
  refine GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors R.ψ R.θ _ _ hθ _ _ _ _ f hV.theta u h1 ?_ φ
  refine GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces R.ψ _ _ _ _ _ f₀ _ f hth u (fun a b => ?_) (h0.2 e' f' h' u hu hh)
  have := h2 _ e he (fun PP hPP => hP PP (Or.inl (by simpa using hPP))) a b
  rw [cA_cA]
  exact this.symm

end GlobalTheory.ConjVacua
