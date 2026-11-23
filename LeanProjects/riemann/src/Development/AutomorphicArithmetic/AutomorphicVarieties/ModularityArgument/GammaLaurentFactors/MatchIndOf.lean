import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cnt (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) : ℕ :=
  (s.filter fun y => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)).card

end Loc

variable {K : Type} [Field K] [NumberField K]

def nm {L : Type} [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v) :
    (w.1.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K) : w.1.adicCompletion L →* v.adicCompletion K)

def fdeg {L : Type} [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v) : ℕ :=
  v.asIdeal.inertiaDeg' w.1.asIdeal

variable [IsTotallyComplex K] {n : ℕ}

def SuppAt (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)) (s : Multiset (IrrGL (v.adicCompletion K))) : Prop :=
  ∃ σ, π.IsLocComp v σ ∧ HasSupport σ.ρ s

def TorAt (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ, π.IsLocComp v σ → Toral (IrrGL.of σ.ρ σ.smooth σ.irred)

def AllTor (π : CuspSub K n) : Prop := ∀ v, TorAt π v

omit [IsTotallyComplex K] in

def ThruAt {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L] (P : CuspSub L n)
    {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v) : Prop :=
  ∀ s, SuppAt P w.1 s → ∀ ζ hζ, IrrGL.ofChar ζ hζ ∈ s →
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ IsUnram (ζ * χ.comp (nm w))

def GamLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V) (s : Multiset (IrrGL (v.adicCompletion K))), HasSupport π s →
    ∃ (P : ℂ[X]) (c : ℂ) (j : ℤ), P.eval 0 = 1 ∧ P.natDegree = cnt s 1 ∧ c ≠ 0 ∧
      GroundTheory.Automorphic.GodementJacquet.IsGammaFactor (v.adicCompletion K) π (GroundTheory.Automorphic.GJStandardL.localHaar n v)
        (GroundTheory.Global.localAdelicChar K v) (RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
          algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * X)))

def SuppFacts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)),
    (∃ s, SuppAt π v s) ∧ (∀ s s', SuppAt π v s → SuppAt π v s' → s = s') ∧
    (∀ s, SuppAt π v s → (TorAt π v ↔ ∀ y ∈ s, y.1 = 1) ∧ (s.map Sigma.fst).sum = n ∧ ∀ y ∈ s, 0 < y.1) ∧
    (∀ s B, SuppAt π v s → (CG.mk π).HasSat v B → ∀ y ∈ s, y.IsUnramChar) ∧
    ∀ (χ : HChar K) s, SuppAt π v s → ∃ s', SuppAt (π.twist χ) v s' ∧ (∀ θ, cnt s' θ = cnt s (χ.loc v * θ)) ∧
      s'.map Sigma.fst = s.map Sigma.fst

def LocIso : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (σ : CuspSub K n)
    (h : Cm.carrier σ ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms K n)
    (D : GroundTheory.Automorphic.AutomorphicForm.AdelicDecomposition (Cm.toRep σ h).toModule) (v : HeightOneSpectrum (𝓞 K)),
    (∀ s, SuppAt σ v s → HasSupport (D.finite.π v) s) ∧ ∀ B, (CG.mk σ).HasSat v B →
      GroundTheory.Automorphic.fixedVectors (D.finite.π v) (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion K) n) ≠ ⊥

def SideGAt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (σ : CuspSub K n) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 K)), GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ S →
    ∀ B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ, (∀ w ∉ S, (CG.mk σ).HasSat w (B w)) →
    ∀ (s : ∀ v : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (v.adicCompletion K))) (q : ℕ) (f : HeightOneSpectrum (𝓞 K) → ℕ),
      1 < q → (∀ v ∈ S, SuppAt σ v (s v) ∧ (cnt (s v) 1 ≠ 0 → Ideal.absNorm v.asIdeal = q ^ f v)) →
      ∃ β P : ℂ[X], β ≠ 0 ∧ P.eval 0 = 1 ∧ P.natDegree = ∑ v ∈ S, f v * cnt (s v) 1 ∧
        PairG (eulerL K (cx B) S) (eulerLd K (cx B) S) β q P

def SideGCen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ σ : CuspSub K n,
    Cm.carrier σ ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms K n → SideGAt K σ

def SideG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ σ : CuspSub K n, SideGAt K σ

def NormLoc : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K), ∃ ξ : HChar L,
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), ξ.loc w.1 = (χ.loc v).comp (nm w) ∧
      (χ.UnrAt v → ξ.UnrAt w.1 ∧ ξ.val w.1 = χ.val v ^ fdeg w) ∧ Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w

def NormCnt : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L], (Module.finrank K L).Prime →
    ∃ η : HChar K, (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∀ w : PlacesOver L v,
        IsPrimitiveRoot (η.val v) (fdeg w) ∧ Fintype.card (PlacesOver L v) * fdeg w = Module.finrank K L) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), (η.loc v).comp (nm w) = 1 ∧
        (∀ (w' : PlacesOver L v) (θ : (v.adicCompletion K)ˣ →* ℂˣ), IsUnram (θ.comp (nm w)) → IsUnram (θ.comp (nm w'))) ∧
        ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ → IsSmoothChar (θ.comp (nm w)) ∧ (IsUnram θ → IsUnram (θ.comp (nm w))) ∧
          (IsUnram (θ.comp (nm w)) → ((Finset.range (Module.finrank K L)).filter fun j => IsUnram (θ * (η ^ j).loc v)).card =
            ∑ w' : PlacesOver L v, fdeg w')

def GlobTw : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K))
    (θ : (v.adicCompletion K)ˣ →* ℂˣ), IsSmoothChar θ → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
    (bad : ∀ u : HeightOneSpectrum (𝓞 K), Finset ((u.adicCompletion K)ˣ →* ℂˣ))
    (bad' : ∀ w : HeightOneSpectrum (𝓞 L), Finset ((w.adicCompletion L)ˣ →* ℂˣ)),
    ∃ χ : HChar K, IsUnram (χ.loc v * θ⁻¹) ∧ ∀ u ∈ S, u ≠ v → (∀ ξ ∈ bad u, ¬ IsUnram (ξ * χ.loc u)) ∧
      ∀ w : PlacesOver L u, ∀ ζ ∈ bad' w.1, ¬ IsUnram (ζ * (χ.loc u).comp (nm w))

def RegroupBC : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (d : ℕ)
    (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L))) (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (BL : HeightOneSpectrum (𝓞 L) → Multiset ℂ) (e : HeightOneSpectrum (𝓞 K) → ℂ) (c₀ : ℝ) (r : ℕ), d.Prime →
    (∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ MainNotions) →
    (∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ (∀ b ∈ BK p,
      ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀ ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) ∧ ∀ w : PlacesOver L p,
        IsPrimitiveRoot (e p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = d ∧ BL w.1 = (BK p).map (· ^ fdeg w)) →
    ∃ c : ℝ, ∀ s : ℂ,
      (c < s.re → ∏ j ∈ Finset.range d, eulerL K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerL L BL SL s) ∧
      (s.re < -c → ∏ j ∈ Finset.range d, eulerLd K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerLd L BL SL s)

def MatchBC : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → ∀ η : HChar K,
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∀ w : PlacesOver L v,
      IsPrimitiveRoot (η.val v) (fdeg w) ∧ Fintype.card (PlacesOver L v) * fdeg w = Module.finrank K L) →
    ∀ (v : HeightOneSpectrum (𝓞 K)) s (s' : ∀ w : PlacesOver L v, Multiset (IrrGL (w.1.adicCompletion L))),
      SuppAt π v s → (∀ w, SuppAt P w.1 (s' w)) → ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      ∑ j ∈ Finset.range (Module.finrank K L), cnt s (θ * (η ^ j).loc v) = ∑ w, fdeg w * cnt (s' w) (θ.comp (nm w))

def MatchInd : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) s (s' : ∀ w : PlacesOver M v, Multiset (IrrGL (w.1.adicCompletion M))),
      SuppAt P v s → (∀ w, SuppAt π w.1 (s' w)) → ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      cnt s θ = ∑ w, fdeg w * cnt (s' w) (θ.comp (nm w))

def UpDown : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → ∀ v : HeightOneSpectrum (𝓞 K),
      (TorAt π v → ∀ w : PlacesOver L v, TorAt P w.1 ∧ ThruAt P w) ∧
      ((∀ w : PlacesOver L v, TorAt P w.1 ∧ ThruAt P w) → TorAt π v)

def IndTor : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ v : HeightOneSpectrum (𝓞 K), (∀ w : PlacesOver M v, TorAt π w.1 ∧ ThruAt π w) → TorAt P v

def SideGCenOf : Prop := GamLoc → LocIso → SideGCen
def SideGOf : Prop := PairGOps → SuppFacts → SideGCen → SideG
def MatchBCOf : Prop := PairGOps → CrossG → SideG → SuppFacts → NormLoc → GlobTw → RegroupBC → MatchBC
def MatchIndOf : Prop := PairGOps → CrossG → SideG → SuppFacts → NormLoc → GlobTw → MatchInd
def UpDownOf : Prop := SuppFacts → NormCnt → MatchBC → UpDown
def IndTorOf : Prop := SuppFacts → NormCnt → MatchInd → IndTor

end UpperTheory.V.Z.Gam
