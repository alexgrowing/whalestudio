import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.EigenGenerator in

theorem GlobalTheory.TwV.DelB.dgen_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ τ, ‖ι ((t.O u μ).dgen τ)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S ι hι τ
  have h5 := hg.2.1
  have hc := hg.2.2.1
  have hk := (primeClass_eq_inert_iff D.host.toHostRaw).1 hc
  have h2 : D.what₂.places.resChar w ∉ D.host.small := hk.1
  have hq : D.what₂.places.resChar w ≠ D.host.q := hk.2.1
  obtain ⟨M, hMnf, hM, hs⟩ := J.dgen
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have h1 : ι (s : ℂ) = lamM M S.lam s := hι ⟨(s : ℂ), mem_Qbar M s⟩
  rw [t.O_dgen u μ, ← hsc, h1, lamM_apply]
  exact norm_generator_eq_one D _ S.lam h2 hq M hM τ s hsp
