import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BijectiveOfSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def NmEq : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v),
    nm w = GlobalTheory.BCChar.normU v w.1

def ChsTr : Prop :=
  ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi' : Continuous i.symm)
    (s : Multiset (IrrGL k)),
    chs (s.map (GlobalTheory.SuppIne.trGL i hi')) = (chs s).map fun ξ => ξ.comp (Units.map (i.symm : k' →* k))

def SplitSupp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), (¬ ∀ u : PlacesOver L v, u = w) →
      ∃ (i : v.adicCompletion K ≃+* w.1.adicCompletion L) (hi' : Continuous i.symm), Continuous i ∧
        (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
        nm w = Units.map (i.symm : w.1.adicCompletion L →* v.adicCompletion K) ∧
        ∀ s s', SuppAt π v s → SuppAt P w.1 s' → s' = s.map (GlobalTheory.SuppIne.trGL i hi')

def RkSupp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (π : CuspSub K 1) (ψ : HChar K), CG.mk π = CG.ofChar ψ →
    ∀ v s, SuppAt π v s → chs s = {ψ.loc v}

def RkLift : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    (ψ : HChar K) (ψ' : HChar L), WeakBC (CG.ofChar ψ).HasSat (CG.ofChar ψ').HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), ψ'.loc w.1 = (ψ.loc v).comp (nm w)

def UpThru : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v)
    (s : Multiset (IrrGL (v.adicCompletion K))), (up w s).filter (Thru w) = up w s

def Spread : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) v s, SuppAt π v s →
    GlobalTheory.RoadU.Unlinked s → ∀ ξ ∈ chs s, ∀ ξ' ∈ chs s,
      ‖((ξ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ < (Ideal.absNorm v.asIdeal : ℝ) * ‖((ξ' (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖

def SplitSuppOf : Prop := NmEq → SuppFacts → UpperTheory.ConvolutionTheory.Sph.WeakStable → UpperTheory.ConvolutionTheory.T.SplitStrong → SplitSupp
def RkLiftOf : Prop := NormLoc → RkLift
def UpThruOf : Prop := ChsFacts → UpThru

theorem gamMixed_of (h1 : GamOne) (h2 : SplitSupp) (h3 : ChsTr) (h4 : RkSupp) (h5 : RkLift) (h6 : UpThru) : GamMixed := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hW v w s s' hs hs'
  by_cases hw : ∀ u : PlacesOver L v, u = w
  · rcases hn.eq_or_lt with rfl | h
    · have e : CG.mk π = CG.ofChar _ := (CG.ofChar_toChar _).symm
      have e' : CG.mk P = CG.ofChar _ := (CG.ofChar_toChar _).symm
      have hW' := hW
      rw [e, e'] at hW'
      have : chs s' = up w s := by
        rw [up, h4 K π _ e v s hs, h4 L P _ e' w.1 s' hs', h5 K L _ _ hW' v w, Multiset.map_singleton]
      rw [this, h6]
    · exact h1 K L hp n h π P hW v w hw s s' hs hs'
  · obtain ⟨i, hi', -, -, hN, H⟩ := h2 K L hp n hn π P hW v w hw
    have : chs s' = up w s := by rw [H s s' hs hs', h3, up, hN]
    rw [this, h6]

end UpperTheory.Gal.GamX
