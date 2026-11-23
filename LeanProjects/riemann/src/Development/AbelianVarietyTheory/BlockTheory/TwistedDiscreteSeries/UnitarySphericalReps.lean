import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsPosReal (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

variable {D : D7}

abbrev Gv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Kv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) :=
  stabLoc D.sp.cm.sig V.gram (frameLat V) v

structure IsUnitarySph (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Gv V v) X) : Prop where
  irred : ρ.IsIrreducible
  adm : GlobalTheory.PRep.IsAdmissible ρ
  unitary : GlobalTheory.LGrp.IsUnitarisable ρ
  sph : GlobalTheory.LGrp.IsSpherical ρ (Kv V v)

def LConvPos (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {X : HeightOneSpectrum (𝓞 D.host.F) → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℂ (X v)]
    (π : ∀ v, Representation ℂ (Gv V v) (X v)) (μ : (Formalism.L2.Theta.AE D)ˣ →* Circle) : Prop :=
  AllSome (HasParamOff D.sp.cm.sig V.gram (frameLat V) (S : Set _) π) fun c =>
    (∀ s : ℂ, ((V.rank : ℝ) + 1) / 2 < s.re →
      Converges (above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist c (val μ)⁻¹) s) ∧
    ∀ s : ℝ, ((V.rank : ℝ) + 1) / 2 < s → IsPosReal (LSD D S c μ s)

variable (D) in

def DConvPos (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a b : ℕ) : Prop :=
  (∀ i < a, Converges (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (etaFam D.host.E (b + i))
    (2 * (((b : ℂ) - a) / 2) + a - i)) ∧
  (Summable fun v : {v // v ∉ (S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
    ‖dv D.host.E a b v.1 (((b : ℂ) - a) / 2) - 1‖) ∧
  IsPosReal (dS D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))) a b)

variable (D) in

def LPositive : Prop :=
  ∀ (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (X : HeightOneSpectrum (𝓞 D.host.F) → Type) [∀ v, AddCommGroup (X v)] [∀ v, Module ℂ (X v)]
    (σ : ∀ v, Representation ℂ (Gv V v) (X v)) (μ : (Formalism.L2.Theta.AE D)ˣ →* Circle),
    (∀ v ∉ S, IsUnitarySph V v (σ v)) →
    Formalism.L2.Theta.IsHeckeChar D μ → UnrOff μ (S : Set (HeightOneSpectrum (𝓞 D.host.F))) →
    (∃ b : ℕ, Formalism.L2.Theta.ResEta D μ b) →
      LConvPos V S σ μ ∧ LConvPos V S (fun v => GlobalTheory.LGrp.smoothDual (σ v)) μ

variable (D) in

def DPositive : Prop :=
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a t : ℕ), 1 ≤ t → DConvPos D S a (a + t)

def Statement : Prop := ∀ D : D7, LPositive D ∧ DPositive D

example (r t : ℕ) (h : r + 5 ≤ t) : ((r : ℝ) + 1) / 2 < (1 + t) / 2 := by
  have : (r : ℝ) + 5 ≤ t := by exact_mod_cast h
  linarith

example : ¬ IsPosReal 0 := fun h => lt_irrefl _ h.2

end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

end
