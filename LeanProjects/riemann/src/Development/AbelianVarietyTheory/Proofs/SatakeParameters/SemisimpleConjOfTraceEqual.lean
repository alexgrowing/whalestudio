import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceConjWeil

theorem frob_mem_weil {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {σ : G E Ω}
    (hσ : IsFrob A (normV w) σ) : σ ∈ Weil h :=
  ⟨1, 0, hσ.1, fun x hx => by simpa using hσ.2 x hx⟩

theorem dense_frob_prime_to (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] :
    Dense {σ : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} := by
  classical
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : G E Ω | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  have : IsGalois E Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  have hl : {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    have h0 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨v, hv, -, -, B, hB, -, σ, hσ, hU'⟩ :=
    GlobalTheory.Published.cheb_holds E Ω U.toSubgroup U.isOpen U.isNormal' g hl.toFinset
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  refine ⟨σ, this, v, fun h => hv ?_, B, hB, hσ⟩
  simpa using h

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : Weil h), (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace) → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r g * p⁻¹ := by
  intro E Ω _ _ _ _ _ l _ a r r' hr hr' hs hs' ht
  refine GlobalTheory.TraceConj.conj_of_trace_eq (G E Ω) (Qbar l) a r r' hs hs' fun g => ?_
  have hc : ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), Continuous ρ →
      Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    fun ρ hρ => (Units.continuous_val.comp hρ).matrix_trace
  have hcl : IsClosed {g : G E Ω | ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace} :=
    isClosed_eq (hc r hr) (hc r' hr')
  have hsub : {σ : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} ⊆
      {g : G E Ω | ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace} := by
    rintro σ ⟨w, hw, B, hB, hσ⟩
    exact ht w hw B hB ⟨σ, frob_mem_weil hB hσ⟩
  exact closure_minimal hsub hcl ((dense_frob_prime_to E Ω l).closure_eq ▸ Set.mem_univ g)

end GlobalTheory.TraceConjWeil

end
