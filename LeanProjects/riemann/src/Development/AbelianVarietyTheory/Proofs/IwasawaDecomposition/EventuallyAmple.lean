import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorLocallyAmpleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleEventuallyOfLocalStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

namespace GlobalTheory.ShFam.RelAmpleFlag

theorem eventually_ample : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (μ : Fin N → ℤ), StrictAnti μ → ∀ (H : LB s.T.Z.X) (Δ : (Φ.C k).Y.Dv), IsAmpleLB H → LBIso ((Φ.C k).Y.lb Δ) (H.pull ((Φ.C k).π ≫ genι s.T.Z)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (Φ.C k).Y.ample (n • Δ - ∑ x : DV.Rt D.what₂.Tau N, μ x.2 • divOf (Φ.C k) (rootExp S x)) := by
  intro D A N j S κ s Φ k μ hμ H Δ hH hΔ
  have hg : IsAffineHom (genι s.T.Z) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  obtain ⟨n₀, h⟩ := GlobalTheory.T.ample_eventually_of_local (Φ.C k).Y (Φ.C k).π (genι s.T.Z) hg H hH Δ _ hΔ
    (GlobalTheory.T.flag_root_divisor_locally_ample D A N j S κ s Φ k μ hμ)
  refine ⟨n₀, fun n hn => ?_⟩
  have := h n hn
  rwa [← sub_eq_add_neg] at this

end GlobalTheory.ShFam.RelAmpleFlag
