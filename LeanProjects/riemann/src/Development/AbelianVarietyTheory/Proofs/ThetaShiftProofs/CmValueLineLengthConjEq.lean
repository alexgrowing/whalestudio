import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivStarStarZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmMetrisedLineLengthsEqSectionLieNormsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaNormLieNormUniqueAtEmbeddingStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem len_conj_of_lieNorm (hK : Known) {K : Type} [Field K] [NumberField K] (P : Out.PolAV (Sp K))
    (v : epsR K ⟶ P.A) (hv : IsTangent v) (ℓ : MLine K) (hℓ : ℓ.Good)
    (h : ∀ σ : K →+* ℂ, Arch.IsLieNormAt P v σ (Real.log (ℓ.n σ))) (em : K →+* ℂ) :
    ℓ.n ((starRingEnd ℂ).comp em) = ℓ.n em := by
  have h1 := (GlobalTheory.ArchConj.norms_conj hK K P em _).2 v (h em)
  have h2 := (GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding hK K P _ _ _).2 v hv (h ((starRingEnd ℂ).comp em)) h1
  exact Real.log_injOn_pos (hℓ.2 _) (hℓ.2 _) h2

theorem valLine_conj : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ) (em : K₁ →+* ℂ), (s.valLine mo n).n ((starRingEnd ℂ).comp em) = (s.valLine mo n).n em := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s mo n em
  letI := H.starRing
  have tie := GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms hK E H Dw l c K₁ a e th jj n' La c₁ s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hΨ, h', hT, -⟩ := s.good
  have hTl : s.Tl.n ((starRingEnd ℂ).comp em) = s.Tl.n em := by
    have h1 := (GlobalTheory.ArchConj.norms_conj hK K₁ a.D₀.P em _).1 a.D₀.rig th (tie em).1
    have h2 := (GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding hK K₁ a.D₀.P _ _ _).1 a.D₀.rig th a.D₀.rig_gen (tie ((starRingEnd ℂ).comp em)).1 h1
    exact (sq_eq_sq₀ (hT.2 _).le (hT.2 _).le).1 h2
  have hL : ∀ m, (s.L.ℓ m).n ((starRingEnd ℂ).comp em) = (s.L.ℓ m).n em := by
    intro m
    have hm := s.L_good.2.2.2 m
    rcases hq : s.L.src m with q | q
    · rw [hq] at hm
      have hm' : s.L.ℓ m = s.ℓΨ q.2 := hm
      rw [hm']
      exact len_conj_of_lieNorm hK s.xΨ.P (s.xΨ.v q.2) (s.xΨ.basis.1 q.2) _ (hΨ q.2).1
        (fun σ => (tie σ).2.1 q.2) em
    · rw [hq] at hm
      have hm' : s.L.ℓ m = s.ℓ' q.2 := hm
      rw [hm']
      exact len_conj_of_lieNorm hK s.x'.P (s.x'.v q.2) (s.x'.basis.1 q.2) _ (h' q.2).1
        (fun σ => (tie σ).2.2.1 q.2) em
  have hline : ∀ τ k, (s.line τ k).n ((starRingEnd ℂ).comp em) = (s.line τ k).n em := by
    intro τ k
    unfold CMIn.line
    rcases s.kind τ k with _ | m
    · rfl
    · exact hL m
  simp only [CMIn.valLine, MLine.tensor, MLine.pow, MLine.dual, MLine.prodPow, hTl, hline]

end GlobalTheory.ArcCM
