import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_half (v : HeightOneSpectrum (𝓞 F)) (x c : E) :
    compFin F E v (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] c) = (1 : Fv F v) ⊗ₜ[F] x := by
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    change evalV F v (1 : Af F) = 1; exact map_one _
  have h0 : evFin F v (pairA F 1 0) = 0 := by
    change evalV F v (0 : Af F) = 0; exact map_zero _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, add_zero]

theorem compInf_half (w : InfinitePlace F) (x : E) :
    compInf F E w (2 * (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E))) = 1 := by
  have h1 : evInf F w (pairA F 0 1) = 0 := by
    change GlobalTheory.AutFunCompare.evW w (0 : Ainf F) = 0; exact map_zero _
  have h0 : evInf F w (pairA F 1 0) = 1 := by
    change GlobalTheory.AutFunCompare.evW w (1 : Ainf F) = 1; exact map_one _
  rw [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, two_mul, map_add, map_add, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, zero_add,
    ← TensorProduct.tmul_add, add_halves, ← Algebra.TensorProduct.one_def]

theorem sigR_half (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] σ x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E) := by
  have h2 : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h2]

theorem half_add (x y : E) (h : x + y = 1) :
    (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      (1 : AF F ⊗[F] E) := by
  have hae : pairA F 0 1 + pairA F 1 0 = (1 : AF F) := Prod.ext (zero_add 1) (add_zero 1)
  rw [show (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] (x + y) + pairA F 1 0 ⊗ₜ[F] (1 / 2 + 1 / 2 : E) by
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel,
    h, add_halves, ← TensorProduct.add_tmul, hae, Algebra.TensorProduct.one_def]

end General

theorem exists_halfData : ∀ D : D7, ∃ t : AE D, HalfData t := by
  intro D
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram D.host.E D.sp.cm.cmUnram
  refine ⟨pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t₀ : D.host.E) + pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 / 2 : D.host.E),
    ?_, fun v => ?_, fun w => compInf_half w _⟩
  · exact (congrArg _ (sigR_half D.sp.cm.sig _)).trans (half_add _ _ ht₀)
  · rw [compFin_half]
    exact tmul_mem_intLoc (one_mem _) t₀

end GlobalTheory.StdUnn
