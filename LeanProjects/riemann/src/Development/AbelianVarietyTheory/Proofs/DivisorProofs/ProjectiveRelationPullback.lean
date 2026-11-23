import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false

noncomputable section

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.LineQuot

theorem rel_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s →
    Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  intro k _ N S T g L Q s φ hL _ hs i j W hW t
  haveI := hL.isQuasicoherent
  beta_reduce
  set A := (Scheme.Modules.pullback g).map (s j)
  set B := (Scheme.Modules.pullback g).map (s i)

  have hsmul : ∀ (U : S.Opens) (hU : U ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i) (c : Γ(S, U))
      (u : Γ((Scheme.Modules.pullback g).obj L, U)),
      A.app U u = ProjSpace.pullRatio (g ≫ φ) U i hU j • B.app U u →
      A.app U (c • u) = ProjSpace.pullRatio (g ≫ φ) U i hU j • B.app U (c • u) := by
    intro U hU c u h
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h, smul_smul, smul_smul, mul_comm]
  have hW' : W ≤ g ⁻¹ᵁ (φ ⁻¹ᵁ ProjSpace.chart k N i) := hW
  have loc : ∀ y : W, ∃ (V : T.Opens) (e : Fin 1 → Γ(L, V)), (y : S) ∈ g ⁻¹ᵁ V ∧ V ≤ φ ⁻¹ᵁ ProjSpace.chart k N i ∧
      IsFrame e := fun y => by
    obtain ⟨V, e, -, hy, hV, he⟩ := hL.exists_affine (x := g y) (V := φ ⁻¹ᵁ ProjSpace.chart k N i) (hW' y.2)
    exact ⟨V, e, hy, hV, he⟩
  choose V e hy hV he using loc
  refine sec_ext_of_cover (fun y => W ⊓ g ⁻¹ᵁ V y) (fun _ => inf_le_left)
    (fun y hyW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyW⟩, hyW, hy _⟩) fun y => ?_
  have hU : W ⊓ g ⁻¹ᵁ V y ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i := inf_le_left.trans hW
  have hgV : g ⁻¹ᵁ V y ≤ (g ≫ φ) ⁻¹ᵁ ProjSpace.chart k N i := g.preimage_mono (hV y)

  have hpb : A.app (g ⁻¹ᵁ V y) (QCoh.pullbackSections g L (le_refl _) (e y 0)) =
      ProjSpace.pullRatio (g ≫ φ) (g ⁻¹ᵁ V y) i hgV j • B.app (g ⁻¹ᵁ V y) (QCoh.pullbackSections g L (le_refl _) (e y 0)) := by
    rw [QCoh.pullback_map_app_pullbackSections, QCoh.pullback_map_app_pullbackSections,
      hs i j (V y) (hV y) (e y 0), QCoh.pullbackSections_smul, ProjSpace.appLE_pullRatio]
  have hres : A.app (W ⊓ g ⁻¹ᵁ V y) (resM _ inf_le_right (QCoh.pullbackSections g L (le_refl _) (e y 0))) =
      ProjSpace.pullRatio (g ≫ φ) (W ⊓ g ⁻¹ᵁ V y) i hU j •
        B.app (W ⊓ g ⁻¹ᵁ V y) (resM _ inf_le_right (QCoh.pullbackSections g L (le_refl _) (e y 0))) := by
    rw [app_resM, app_resM, hpb, resM_smul, ProjSpace.resG_pullRatio]
  obtain ⟨a, ha⟩ := ((he y).pullback g (W ⊓ g ⁻¹ᵁ V y) inf_le_right).2 (resM _ inf_le_left t)
  rw [Fintype.linearCombination_apply, Fin.sum_univ_one] at ha
  rw [← app_resM, resM_smul, ← app_resM, ProjSpace.resG_pullRatio, ← ha]
  exact hsmul _ _ _ _ hres

end GlobalTheory.LineQuot

end
