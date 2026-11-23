import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (W : HSp D) (ρ : ℕ) (β : GlobalTheory.FinPl.Frame p W (Fin W.rank)) (x : Mx D W.rank (ρ + 1))
  (ι ι' : Fin (ρ + 1) → Fin W.rank) (s t : Fin (ρ + 1) → k) (e : ℕ), 0 < e → Function.Injective ι → Function.Injective ι' →
  (∀ a b, ι' b = ι a → a = Fin.last ρ ∧ b = Fin.last ρ) →
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (x i q)) = Pi.single (ι q) 1) →
  (∀ q, t q • ((fun i => p.pr (cA D (x i q))) ᵥ* (W.gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) →
  ∀ g ∈ grpAt W (· = p.v), ∀ (u : UX D (ρ + 1)) (a : Mx D W.rank (ρ + 1)),
  (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) →
  (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e,
    (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ* (W.gram.map (fun c => p.pr (incA D c)) * β.b)) i) →
  MxOff (· = p.v) (mt W g⁻¹ ⬝ (x ⬝ u.1.1) - x - a) →
  ∃ k₀ : GL (Fin W.rank) 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e) ∧
    MxOff (· = p.v) (mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) := by
  first | exact @GlobalTheory.AscFin.OneOrbitAt.one_orbit | exact GlobalTheory.AscFin.OneOrbitAt.one_orbit | (intros; apply GlobalTheory.AscFin.OneOrbitAt.one_orbit <;> assumption)
