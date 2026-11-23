import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEquationBaseChangeAlgHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdeleOfPlacesMulEqSumComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSpecialUnitarySupportedAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesTer
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp_of_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε h₁ h₂
  classical
  haveI : FiniteDimensional F E := inferInstance
  have h₁' : ∀ w : InfinitePlace F, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ (w ∈ S₁ →
      ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g =
        JR w.Completion J → ∀ i j, g i j ∈ C) := by
    intro w
    by_cases hw : w ∈ S₁
    · obtain ⟨C, hC, hC'⟩ := h₁ w hw
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hw⟩
  have h₂' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ (v ∈ S₂ →
      ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g =
        JR (Fv F v) J → ∀ i j, g i j ∈ C) := by
    intro v
    by_cases hv : v ∈ S₂
    · obtain ⟨C, hC, hC'⟩ := h₂ v hv
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hv⟩
  choose C₁ hC₁ hC₁' using h₁'
  choose C₂ hC₂ hC₂' using h₂'
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Set (AF F ⊗[F] E)), (∀ i ∈ s, IsCompact (f i)) →
      IsCompact (∑ i ∈ s, f i) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, ← Set.singleton_zero]; exact isCompact_singleton
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  set e := algebraMap (AF F) (AF F ⊗[F] E) ε with he
  let X : Set (AF F ⊗[F] E) := (fun δ => δ * (1 - e)) '' ({0, 1} : Set (AF F ⊗[F] E)) +
    (∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) '' C₁ w) +
    ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) '' C₂ v
  have hX : IsCompact X :=
    ((((Set.toFinite _).isCompact).image (continuous_id.mul continuous_const)).add
      (hsum _ _ fun w _ => (hC₁ w).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))).add (hsum _ _ fun v _ => (hC₂ v).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))
  refine GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces σ J ε X hX (GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces σ J ε) fun g hg i j => ?_
  have hu : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := by
    let g' : HR (AF F) σ J := g
    exact g'.2
  set a := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with ha
  set δ := (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with hδ
  have hfix : e * (a - δ) = a - δ := by
    have := hg.2 i j
    simpa only [Matrix.sub_apply] using this
  have hdec : a = δ * (1 - e) + e * a := by linear_combination (-1 : AF F ⊗[F] E) * hfix
  rw [hdec, GlobalTheory.T.idempotentAdeleOfPlaces_mul_eq_sum_components S₁ S₂ ε hε a, ← add_assoc]
  refine Set.add_mem_add (Set.add_mem_add ⟨δ, ?_, rfl⟩ (Set.finsetSum_mem_finsetSum _ _ _ fun w hw => ⟨_, ?_, rfl⟩))
    (Set.finsetSum_mem_finsetSum _ _ _ fun v hv => ⟨_, ?_, rfl⟩)
  · rw [hδ, Matrix.one_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact hC₁' w hw _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j
  · exact hC₂' v hv _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j

end GlobalTheory.SUSuppCompact

end
