import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedClassOfCmHostStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixOfMassFrameDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLiftInThetaGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRationalMatrixCompatibleStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem data_link : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → Theta.GA D (Wc D i)), (2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f) ∧ (G = Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm)) ∧ (∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = TH.tauE D ρ) ∧ (∀ j, h j ∈ Theta.GfC (Wc D i)) ∧ (∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((h j')⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j')) ∧ (∀ (j : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((h j)⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) := by
  intro D Tu Cl t0 hCl i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, eΨ, heΨ⟩ := GlobalTheory.T.cm_type_from_conjugate_complement D
  obtain ⟨x, p0, hx⟩ := GlobalTheory.T.gram_matrix_of_mass_frame_diagonal D i
  obtain ⟨J, s, hs⟩ := GlobalTheory.T.special_unitary_representatives_exist D Tu Cl t0 hCl i
  refine ⟨gm D i, lat Cl i, psi D, x, p0, J, s, fun j => lift D i (s j),
    ⟨(GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).1, GlobalTheory.T.unramified_class_of_cm_host D, GlobalTheory.T.self_dual_lattice_of_level_class D Tu Cl t0 hCl i, hcm, hx, hs, (GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).2⟩, rfl,
    ⟨eΨ, heΨ⟩, fun j => (GlobalTheory.T.special_unitary_lift_in_theta_group D i (s j) (hs.1 j)).1, GlobalTheory.T.special_unitary_representatives_theta_compatible D Tu Cl t0 hCl i J s hs,
    fun j g γ γr hg hm hr hd hk => GlobalTheory.T.special_unitary_rational_matrix_compatible D Tu Cl t0 hCl i (s j) (hs.1 j) g γ γr hg hm hr hd hk⟩

end GlobalTheory.MassLink
