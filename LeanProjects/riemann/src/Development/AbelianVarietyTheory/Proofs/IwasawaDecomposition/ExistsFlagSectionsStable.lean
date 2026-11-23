import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerCoordMatrixStableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordMatrixRegularStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerFunctionRegularAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerFunctionGeneratesAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordMatrixGeneratesStatement

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.FlagAmple.exists_plk_affine : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∃ (M : GlobalTheory.FlagAmple.Step S.Dw → ℕ) (t : ∀ x : GlobalTheory.FlagAmple.Step S.Dw, Fin (M x + 1) → (((Φ.C k).Y.lb (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ))).pull ((Φ.C k).π ⁻¹ᵁ V).ι).Sec) (ht : ∀ x, ⨆ m, nonzeroLocus (t x m) = ⊤), ∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = a' ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) → (∀ x, a ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (t x) (ht x) = a' ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (t x) (ht x)) → a = a' := by
  intro D A N j S κ s Φ k V hV φ g hφ hg
  by_cases hne : genericPoint (Φ.C k).Y.X ∈ (Φ.C k).π ⁻¹ᵁ V
  · obtain ⟨B, hB⟩ := GlobalTheory.T.exists_plucker_coord_matrix_stable D A N j S κ s Φ k V hV φ g hφ hg hne
    have hfac := GlobalTheory.T.plucker_coord_matrix_regular D A N j S κ s Φ k V hV φ g hφ hg hne B hB
    have hreg : ∀ (x : GlobalTheory.FlagAmple.Step S.Dw) (q : Fin (GlobalTheory.FlagAmple.PlkLoc.plkM x + 1)) (y : (Φ.C k).Y.X),
        y ∈ (Φ.C k).π ⁻¹ᵁ V → (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ)).RegularAt y
          (GlobalTheory.FlagAmple.PlkLoc.plkFn B x q) := fun x q y hy => by
      obtain ⟨t, T, By, h1, h2, h3, -, h5⟩ := hfac y hy
      rw [GlobalTheory.FlagAmple.PlkLoc.plkFn, h5 x.1]
      exact GlobalTheory.T.plucker_function_regular_at_point _ y _ x.2.1 ((Φ.C k).gr x.1) (t x.1) (T x.1) (By x.1) (h1 x.1) (h2 x.1) (h3 x.1) q
    have hgen : ∀ (x : GlobalTheory.FlagAmple.Step S.Dw) (y : (Φ.C k).Y.X), y ∈ (Φ.C k).π ⁻¹ᵁ V →
        ∃ q : Fin (GlobalTheory.FlagAmple.PlkLoc.plkM x + 1), (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ)).GeneratesAt y
          (GlobalTheory.FlagAmple.PlkLoc.plkFn B x q) := fun x y hy => by
      obtain ⟨t, T, By, h1, h2, h3, h4, h5⟩ := hfac y hy
      simp only [GlobalTheory.FlagAmple.PlkLoc.plkFn, h5 x.1]
      exact GlobalTheory.T.plucker_function_generates_at_point _ y _ x.2.1 ((Φ.C k).gr x.1) (t x.1) (T x.1) (By x.1) (h1 x.1) (h2 x.1) (h3 x.1) (h4 x.1)
    have ht : ∀ x : GlobalTheory.FlagAmple.Step S.Dw,
        ⨆ q, nonzeroLocus (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x q) = ⊤ :=
      fun x => top_le_iff.1 fun y _ => by
        obtain ⟨q, hq⟩ := hgen x (((Φ.C k).π ⁻¹ᵁ V).ι y) y.2
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, GlobalTheory.FlagAmple.PlkLoc.mem_nonzeroLocus_secOfRat
          (fun z hz => hreg x q z hz) y hq⟩
    exact ⟨GlobalTheory.FlagAmple.PlkLoc.plkM, GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B, ht,
      GlobalTheory.T.plucker_coord_matrix_generates D A N j S κ s Φ k V hV φ g hφ hg hne B hB hreg ht⟩
  · have hU : ∀ y : ((Φ.C k).π ⁻¹ᵁ V).toScheme, False := fun y => hne (GlobalTheory.Cartier.gen_mem y.2)
    refine ⟨GlobalTheory.FlagAmple.PlkLoc.plkM, GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) 0,
      fun x => top_le_iff.1 fun y _ => (hU y).elim, fun K _ _ a a' _ _ => ?_⟩
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    exact (hU (a p)).elim
