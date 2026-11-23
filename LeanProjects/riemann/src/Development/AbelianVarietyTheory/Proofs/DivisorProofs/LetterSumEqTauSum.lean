import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TauEmbNeConjEmb
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootLetterInjective
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieLetters

theorem sum_emb_eq_sum_tau (D : D7) (O : Setup D) (h : (D.host.E →+* ℂ) → ℝ) :
    ∑ σ, h σ = ∑ τ : D.what₂.Tau, (h (DV.tauEmb D τ) + h (conjEmb (DV.tauEmb D τ))) := by
  classical
  let φ : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →+* ℂ) :=
    Sum.elim (DV.tauEmb D) (fun t => conjEmb (DV.tauEmb D t))
  have hφ : Function.Bijective φ := by
    constructor
    · rintro (a|a) (b|b) hab
      · exact congrArg Sum.inl (GlobalTheory.FirstRows.tauEmb_injective D (by simpa [φ] using hab))
      · exact (GlobalTheory.LocM.EvTrue.tauEmb_ne_conjEmb O.A a b (by simpa [φ] using hab)).elim
      · exact (GlobalTheory.LocM.EvTrue.tauEmb_ne_conjEmb O.A b a (by simpa [φ] using hab.symm)).elim
      · exact congrArg Sum.inr (GlobalTheory.FirstRows.conj_tauEmb_injective D (by simpa [φ] using hab))
    · intro σ
      rcases GlobalTheory.RootSum.eq_tau_or_conj (A := O.A) σ with ⟨_, t, ht⟩ | ⟨_, t, ht⟩
      · exact ⟨Sum.inl t, ht.symm⟩
      · exact ⟨Sum.inr t, ht.symm⟩
  rw [← hφ.sum_comp h, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

theorem sum_letters_eq_sum_tau : ∀ (D : D7) (O : Setup D) (g : (D.host.E →+* ℂ) × ℕ → ℝ),
    ∑ j : Fin (letters O.S.Dw).length, g (((letters O.S.Dw).get j).1, (((letters O.S.Dw).get j).2 : ℕ)) =
      ∑ τ : D.what₂.Tau, ((∑ i ∈ Finset.range O.j, g (DV.tauEmb D τ, i)) +
        ∑ i ∈ Finset.range (O.N - O.j), g (conjEmb (DV.tauEmb D τ), i)) := by
  intro D O g
  classical
  have hb := GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective O.S.Dw
  have h1 : (∑ j : Fin (letters O.S.Dw).length,
      g (((letters O.S.Dw).get j).1, (((letters O.S.Dw).get j).2 : ℕ))) =
      ∑ x : Pad.Letter O.S.Dw, g (x.1, (x.2 : ℕ)) :=
    hb.sum_comp (fun x : Pad.Letter O.S.Dw => g (x.1, (x.2 : ℕ)))
  have h2 : ∀ σ : D.host.E →+* ℂ, ∑ i : Fin (O.S.Dw.mult σ), g (σ, (i : ℕ)) =
      ∑ i ∈ Finset.range (O.S.Dw.mult σ), g (σ, i) :=
    fun σ => Fin.sum_univ_eq_sum_range (fun i => g (σ, i)) _
  rw [h1, Fintype.sum_sigma]
  simp only [h2]
  rw [sum_emb_eq_sum_tau D O (fun σ => ∑ i ∈ Finset.range (O.S.Dw.mult σ), g (σ, i))]
  simp only [LieGen.mult_tau, LieGen.mult_conj_tau]

end GlobalTheory.LieLetters
