import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∃ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ₁ = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  first | exact @GlobalTheory.FreeBlockTwist.vecFree_base_translate | exact GlobalTheory.FreeBlockTwist.vecFree_base_translate | (intros; apply GlobalTheory.FreeBlockTwist.vecFree_base_translate <;> assumption)
