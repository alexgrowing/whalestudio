import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEigenFrameLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentEigenFrameCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentFramePermutationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenFrameCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineSpaceSmoothNormalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.ShFam.Cell

theorem existsUnique_of_coords : ∀ (Q W V : Scheme.{0}) (ι : Type) (ρ : W ⟶ V) (u : ι → Γ(W, ⊤)), (∀ (x : Q ⟶ V) (a : ι → Γ(Q, ⊤)), ∃! p : Q ⟶ W, p ≫ ρ = x ∧ ∀ i, p.appTop (u i) = a i) → ∀ t : Q ⟶ 𝔸(ι; V), ∃! p : Q ⟶ W, p ≫ AffineSpace.homOfVector ρ u = t := by
  intro Q W V ι ρ u h t
  have key : ∀ p : Q ⟶ W, p ≫ AffineSpace.homOfVector ρ u = t ↔
      (p ≫ ρ = t ≫ 𝔸(ι; V) ↘ V ∧ ∀ i, p.appTop (u i) = t.appTop (AffineSpace.coord V i)) := by
    intro p
    rw [AffineSpace.comp_homOfVector]
    constructor
    · rintro rfl
      refine ⟨(AffineSpace.homOfVector_over _ _).symm, fun i => ?_⟩
      rw [AffineSpace.homOfVector_appTop_coord]
      rfl
    · rintro ⟨h1, h2⟩
      refine AffineSpace.hom_ext ?_ ?_
      · rw [AffineSpace.homOfVector_over, h1]
      · intro i
        rw [AffineSpace.homOfVector_appTop_coord]
        exact h2 i
  obtain ⟨p, hp, hu⟩ := h (t ≫ 𝔸(ι; V) ↘ V) (fun i => t.appTop (AffineSpace.coord V i))
  exact ⟨p, (key p).2 hp, fun q hq => hu q ((key q).1 hq)⟩

theorem exists_cell_nhds : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (y : (Φ.C k).Y.X), ∃ (W : (Φ.C k).Y.X.Opens) (T : Scheme.{0}) (h : W.toScheme ⟶ T) (g : T ⟶ gen s.T.Z), y ∈ W ∧ Smooth g ∧ LocallyOfFiniteType g ∧ IsIntegral T ∧ (∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) ∧ h ≫ g = W.ι ≫ (Φ.C k).π ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∃! x : Spec (.of Ω) ⟶ W.toScheme, x ≫ h = t := by
  intro D A N j S κ s Φ k y
  have hsm : Smooth (genStr s.T.Z) := SmoothOfRelativeDimension.smooth S.Dw.dim _
  obtain ⟨V, hV, φV, f₀, hyV, hVi, hstr⟩ := GlobalTheory.T.exists_affine_eigen_frame_local hsm ((Φ.C k).π y)
  obtain ⟨w, hyW⟩ := GlobalTheory.T.flag_component_eigen_frame_compat (Φ.C k) hV f₀ hstr y hyV
  obtain ⟨u, hu⟩ := GlobalTheory.T.flag_component_frame_permutation (Φ.C k) hV f₀ w
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.affine_space_smooth_normal (gen s.T.Z) _ (genStr s.T.Z) hsm V hV hVi (Coord S.Dw)
  refine ⟨cellOpen (Φ.C k) hV f₀ w, 𝔸(Coord S.Dw; V.toScheme),
    AffineSpace.homOfVector (cellMap (Φ.C k) hV f₀ w) (coordTop (Φ.C k) hV f₀ w u),
    (𝔸(Coord S.Dw; V.toScheme) ↘ V.toScheme) ≫ V.ι, hyW, h1, h2, h3, h4, ?_, ?_⟩
  · rw [← Category.assoc, AffineSpace.homOfVector_over]
    exact cellMap_ι _ _ _ _
  · intro Ω _ _ t
    refine existsUnique_of_coords _ _ _ _ _ _ (fun x a => ?_) t
    obtain ⟨p, hp, hpa⟩ := GlobalTheory.T.flag_toroidal_eigen_frame_comp Φ k hV f₀ hstr hVi w u hu y hyW Ω x a
    exact ⟨p, ⟨hp, hpa⟩, fun q ⟨hq, hqa⟩ => GlobalTheory.T.flag_toroidal_eigen_frame Φ k hV f₀ w u hu Ω q p (hq.trans hp.symm)
      fun i => (hqa i).trans (hpa i).symm⟩

end GlobalTheory.ShFam.Cell
