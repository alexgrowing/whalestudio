import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagStepsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProperAffineFlagSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedProjectiveEmbeddingSepStatement

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
open scoped TensorProduct ContDiff

namespace GlobalTheory.FlagAmple

theorem isAmpleLB_rootEx : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (μ : Fin N → ℤ), StrictAnti μ → ∀ z : gen s.T.Z, ∃ V : (gen s.T.Z).Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (((Φ.C k).Y.lb (-∑ x : DV.Rt D.what₂.Tau N, μ x.2 • divOf (Φ.C k) (rootEx S.Dw (DV.tauEmb D x.1) x.2))).pull ((Φ.C k).π ⁻¹ᵁ V).ι) := by
  intro D A N j S κ s Φ k μ hμ z
  obtain ⟨w, c, hw, hE⟩ := GlobalTheory.T.divisor_decomposition_flag_steps D A N j S κ s Φ k μ hμ
  obtain ⟨V, f, hz, hV, hf, htop, M, t, ht, hsep⟩ := GlobalTheory.T.exists_proper_affine_flag_sections D A N j S κ s Φ k z
  refine ⟨V, hz, hV, ?_⟩
  rw [hE]
  exact GlobalTheory.T.weighted_projective_embedding_sep _ _ f hf _ _ (fun x => LB.isLB_pull (isLB_toLB _) _) M t ht hsep w (fun x => hw x) _
    (LB.isLB_pull (isLB_toLB _) _) (by
      show GlobalTheory.CechPic.pull _ (toPic _) = ∑ x, w x • GlobalTheory.CechPic.pull _ (toPic _)
      simp only [map_add, map_sum, map_zsmul, map_neg, htop, smul_zero, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [natCast_zsmul])

end GlobalTheory.FlagAmple
