import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import GroundTheory.PAdicHodge.AInfGalois

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs

namespace PInfInd2A

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem prod_shift (M₁ M₂ : Multiset ℂ) (z₁ z₂ u : ℂ) (r s : ℕ) :
    (((M₁.map (· + z₁)).map (u - (s : ℂ) / 2 + ·)).prod * ((M₂.map (· + z₂)).map (u + (r : ℂ) / 2 + ·)).prod) =
      ((M₁.map (· + (z₁ - (s : ℂ) / 2)) + M₂.map (· + (z₂ + (r : ℂ) / 2))).map (u + ·)).prod := by
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end PInfInd2A

open PInfInd2A in
theorem infInd2_holds : InfInd2 := by
  intro E _ _ _ r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ m hm
  obtain ⟨f, hfm, hfi, hfe⟩ := hemb
  obtain ⟨M₁, hM₁⟩ := exists_hasInfCharGL hV₁ τ
  obtain ⟨M₂, hM₂⟩ := exists_hasInfCharGL hV₂ τ
  refine ⟨M₁, M₂, hM₁, hM₂, ?_⟩
  have hW₁ := GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi hM₁ (GlobalTheory.CuspRep.Model.absC E z₁)
  have hW₂ := GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi hM₂ (GlobalTheory.CuspRep.Model.absC E z₂)
  rw [GlobalTheory.CuspRep.Model.expo_absC] at hW₁ hW₂
  refine GlobalTheory.BcSpehProof.hasInfCharGL_unique hV.ne_bot hm ⟨?_, fun u φ hφ => ?_⟩
  · simp only [Multiset.card_add, Multiset.card_map, hM₁.1, hM₂.1]
  have hI : ∀ X, ∀ φ ∈ V, lie E (r + s) X φ ∈ V := fun X φ hφ => hV.stable (.lie X) φ hφ
  have hc : cap τ u (f φ) = (((M₁.map (· + z₁)).map (u - (s : ℂ) / 2 + ·)).prod *
      ((M₂.map (· + z₂)).map (u + (r : ℂ) / 2 + ·)).prod) • f φ :=
    casimir_on_parabolic_induction (n := ![r, s]) (tw V₁ z₁) (tw V₂ z₂) τ _ _ hW₁ hW₂ u (f φ) (hfm φ hφ)
  have e1 : f (cap τ u φ) = cap τ u (f φ) := GlobalTheory.SpehInfChar.cap_comm_quot hI f hfe τ u φ hφ
  set Q := ((M₁.map (· + (z₁ - (s : ℂ) / 2)) + M₂.map (· + (z₂ + (r : ℂ) / 2))).map (u + ·)).prod with hQ
  have hmem : cap τ u φ - Q • φ ∈ V := by
    rw [hm.2 u φ hφ]
    exact V.sub_mem (V.smul_mem _ hφ) (V.smul_mem _ hφ)
  have h0 : f (cap τ u φ - Q • φ) = 0 := by
    rw [map_sub, e1, hc, map_smul, hQ, ← prod_shift]
    exact sub_self _
  exact sub_eq_zero.1 (hfi _ hmem h0)

end PositivityTheory.Rg.Rs

end
