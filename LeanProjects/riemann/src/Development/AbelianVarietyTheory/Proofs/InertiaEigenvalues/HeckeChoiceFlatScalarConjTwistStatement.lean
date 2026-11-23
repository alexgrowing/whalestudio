import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwist
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChoice_flatScalar_conj_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  first | exact @GlobalTheory.FlatConj.flat_conj | exact GlobalTheory.FlatConj.flat_conj | (intros; apply GlobalTheory.FlatConj.flat_conj <;> assumption)
