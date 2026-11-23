import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqual

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.TraceConjCofinite

theorem dense_frob_outside (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) :
    Dense {σ : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ S ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} := by
  classical
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : G E Ω | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  have : IsGalois E Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  obtain ⟨v, hv, -, -, B, hB, -, σ, hσ, hU'⟩ :=
    GlobalTheory.Published.cheb_holds E Ω U.toSubgroup U.isOpen U.isNormal' g hS.toFinset
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  refine ⟨σ, this, v, fun h => hv ?_, B, hB, hσ⟩
  simpa using h

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : Weil h), (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace) → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r g * p⁻¹ := by
  intro E Ω _ _ _ _ _ l _ a r r' hr hr' hs hs' ht
  refine GlobalTheory.TraceConj.conj_of_trace_eq (G E Ω) (Qbar l) a r r' hs hs' fun g => ?_
  have hc : ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), Continuous ρ →
      Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    fun ρ hρ => (Units.continuous_val.comp hρ).matrix_trace
  have hcl : IsClosed {g : G E Ω | ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace} :=
    isClosed_eq (hc r hr) (hc r' hr')
  have hd := dense_frob_outside E Ω _ (Filter.eventually_cofinite.1 ht)
  refine closure_minimal ?_ hcl (hd.closure_eq ▸ Set.mem_univ g)
  rintro σ ⟨w, hw, B, hB, hσ⟩
  exact (not_not.1 hw) B hB ⟨σ, GlobalTheory.TraceConjWeil.frob_mem_weil hB hσ⟩

end GlobalTheory.TraceConjCofinite

end
