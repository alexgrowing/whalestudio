import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCover

theorem cover : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  classical
  intro K _ _ A _ hA V hV
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let O : (𝟙_ (Over (Sp K)) ⟶ A) → A.left.Opens := fun a =>
    (𝟙 A * (toUnit A ≫ a)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a)⁻¹).left ⁻¹ᵁ V
  have key : ∀ y : 𝟙_ (Over (Sp K)) ⟶ A, ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, ∀ p, y.left p ∈ O a := by
    intro y
    have := GlobalTheory.AbelianProjective.isIso_transl_left y
    have : IsIso ((toUnit A ≫ y) * 𝟙 A).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit A ≫ y) * 𝟙 A)))
    have : IsIso (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A))))
    have h1 : ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h2 : (((ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h3 := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) h1 h2
    obtain ⟨a, ha⟩ := GlobalTheory.AbelianProjective.exists_point A
      ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V ⊓ (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V).isOpen).isLocallyClosed h3
    refine ⟨a, fun p => ?_⟩
    have e : y ≫ (𝟙 A * (toUnit A ≫ a)) = a ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have e' : y ≫ (𝟙 A * (toUnit A ≫ a)⁻¹) = a ≫ ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
      rfl
    have hp := ha p
    refine ⟨?_, ?_⟩
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)).left) p ∈ V
      rw [← Over.comp_left, e, Over.comp_left]
      exact hp.1
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)⁻¹).left) p ∈ V
      rw [← Over.comp_left, e', Over.comp_left]
      exact hp.2
  have htop : ⨆ a, O a = ⊤ := by
    by_contra hne
    have hc : ((⨆ a, O a : A.left.Opens) : Set A.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := GlobalTheory.AbelianProjective.exists_point A
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨a, ha⟩ := key y
    exact hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha _⟩)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun a => (O a : Set A.left))
    (fun a => (O a).isOpen) fun x _ => by
      have hx : x ∈ ⨆ a, O a := by rw [htop]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  refine ⟨F.card, fun i => (F.equivFin.symm i).1, top_unique fun x _ => ?_⟩
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨F.equivFin ⟨a, ha⟩, by simp only [Equiv.symm_apply_apply]; exact hx⟩

end GlobalTheory.AbCover
