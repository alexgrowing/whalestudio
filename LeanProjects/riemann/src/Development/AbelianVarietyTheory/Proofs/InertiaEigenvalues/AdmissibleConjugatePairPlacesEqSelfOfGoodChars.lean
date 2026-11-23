import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmSelf

theorem not_mem_placesOver_of_normV {D : D7} {l M : ℕ} (hM : 0 < M) {P : Pl D.host.E}
    (h : normV P % (2 * l ^ M) = 1) : P ∉ placesOver D.host.E l := by
  intro hl
  have hmem : ((normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hl' : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hl
  have hdm := Nat.div_add_mod (normV P) (2 * l ^ M)
  rw [h] at hdm
  have hx : ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    push_cast
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hM
    rw [hk, pow_succ]
    exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ (P.asIdeal.mul_mem_left _ hl'))
  have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have : (1 : 𝓞 D.host.E) = ((normV P : ℕ) : 𝓞 D.host.E) - ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) := by
      generalize normV P / (2 * l ^ M) = q at hdm ⊢
      rw [← hdm]
      push_cast; ring
    rw [this]
    exact P.asIdeal.sub_mem hmem hx
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory.AdmSelf

namespace GlobalTheory.AdmSelf

theorem admissibleConjugatePairPlaces_eq_self_of_goodChar : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ)
    (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))),
    (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) →
    (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
    (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X i M Q d hs hc hg hl
  classical
  have hnl : ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i) := fun P hP =>
    hl.elim (fun hM => not_mem_placesOver_of_normV hM (hg P hP).2) fun h => h P hP
  have hchar : ∀ P ∈ Q, ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)),
      IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
      (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
      (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P hP => by
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hg P hP
    refine ⟨d P, h1, h2, h3, fun w a c => h4 w (fun t => t.elim a c), fun A hA x => ?_⟩
    obtain ⟨σ, hσ, hx⟩ := h5 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun P hP => ?_
  obtain ⟨P', hPP'⟩ := GlobalTheory.TwistDet.exists_isConjPl P
  have hP' : P' ∈ Q := hc P hP P' hPP'
  refine mem_admissibleConjugatePairPlaces_iff.2 ⟨hP, P', hP', hPP', fun w hw => ?_, fun w hw => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hs _ hP, hnl _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨hs _ hP', hnl _ hP'⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨⟨P', by simp, hPP'⟩, hchar _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨⟨P, by simp, GlobalTheory.GalChar.isConjPl_symm hPP'⟩, hchar _ hP'⟩

end GlobalTheory.AdmSelf
