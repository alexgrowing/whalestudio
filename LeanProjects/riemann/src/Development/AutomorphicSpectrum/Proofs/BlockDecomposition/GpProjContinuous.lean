import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.BZMir

theorem continuous_gpProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  intro k _ _ _ _ m j
  have hincl : Continuous (GlobalTheory.BZMir.Leib.hgpIncl k m j) := by
    apply continuous_induced_rng.2
    have hv : Continuous (fun h : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j =>
        ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) := by
      first
        | exact continuous_subtype_val.comp continuous_subtype_val
        | fun_prop
    exact hv
  have hlevi := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ _ _
    (GlobalTheory.BZMir.Leib.eGP m j)).2.2.2.2.2.1
  have hblock := hlevi.comp hincl
  unfold GlobalTheory.BZMir.Leib.gpProj
  rw [MonoidHom.coe_prod]
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_apply false).comp hblock
  · apply continuous_induced_rng.2
    exact (continuous_apply true).comp hblock

end GlobalTheory.CompanionTheory.BZMir
