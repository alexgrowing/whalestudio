import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def unif : kˣ := Classical.epsilon fun p : kˣ => ValuativeRel.valuation k (p : k) < 1 ∧
  ∀ x : k, ValuativeRel.valuation k x < 1 → ValuativeRel.valuation k x ≤ ValuativeRel.valuation k (p : k)

def chars (s : Multiset (IrrGL k)) : Set (kˣ →* ℂˣ) := {ξ | ∃ hξ, IrrGL.ofChar ξ hξ ∈ s}

def pol (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) : ℂ[X] :=
  (s.map fun y => if h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * χ) then
    1 - C (((h.choose * χ) (unif k) : ℂˣ) : ℂ) * X else 1).prod

def Unl (q : ℕ) (s : Multiset (IrrGL k)) : Prop :=
  ∀ ξ ∈ chars s, ∀ ξ' ∈ chars s, IsUnram (ξ * ξ'⁻¹) → (((ξ * ξ'⁻¹) (unif k) : ℂˣ) : ℂ) ≠ q

end Loc

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

def WinAt (π : CuspSub K n) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  TorAt π v ∧ ∀ s, SuppAt π v s → ∀ ξ ∈ chars s,
    (Ideal.absNorm v.asIdeal : ℝ) ^ (t - 1 / 2) < ‖((ξ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ ∧
      ‖((ξ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (t + 1 / 2)

def AllWin (π : CuspSub K n) : Prop := ∃ t, ∀ v, WinAt π t v

theorem AllWin.tor {π : CuspSub K n} (h : AllWin π) : AllTor π := fun v => (h.choose_spec v).1

def PolFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (ValuativeRel.valuation k (unif k : k) < 1 ∧
      ∀ x : k, ValuativeRel.valuation k x < 1 → ValuativeRel.valuation k x ≤ ValuativeRel.valuation k (unif k : k)) ∧
    (∀ ξ ξ' : kˣ →* ℂˣ, IsUnram (ξ * ξ'⁻¹) → ξ (unif k) = ξ' (unif k) → ξ = ξ') ∧
    (∀ ξ ξ' hξ hξ', (IrrGL.ofChar ξ hξ : IrrGL k) = IrrGL.ofChar ξ' hξ' → ξ = ξ') ∧
    ∀ (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ), (pol s χ).eval 0 = 1 ∧ (pol s χ).natDegree = cnt s χ ∧
      (∀ x : ℂ, (pol s χ).eval x = 0 ↔ ∃ ξ ∈ chars s, IsUnram (ξ * χ) ∧ (((ξ * χ) (unif k) : ℂˣ) : ℂ) * x = 1) ∧
      ∀ μ : kˣ →* ℂˣ, IsUnram μ → pol s (χ * μ) = (pol s χ).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X)

def NormVal : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v)
    (μ : (v.adicCompletion K)ˣ →* ℂˣ),
    (IsUnram μ → IsUnram (μ.comp (nm w)) ∧ μ (nm w (unif (w.1.adicCompletion L))) = μ (unif (v.adicCompletion K)) ^ fdeg w) ∧
    (IsSmoothChar μ → ‖((μ (nm w (unif (w.1.adicCompletion L))) : ℂˣ) : ℂ)‖ = ‖((μ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ ^ fdeg w) ∧
    0 < fdeg w ∧ Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w

def GamLocX : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V) (s : Multiset (IrrGL (v.adicCompletion K))), HasSupport π s →
    ∃ (c : ℂ) (j : ℤ), c ≠ 0 ∧
      GroundTheory.Automorphic.GodementJacquet.IsGammaFactor (v.adicCompletion K) π (GroundTheory.Automorphic.GJStandardL.localHaar n v)
        (GroundTheory.Global.localAdelicChar K v) (RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) (pol s 1) /
          algebraMap ℂ[X] (RatFunc ℂ) ((pol s 1).comp (C ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * X)))

def SuppTw : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K))
    (χ : HChar K) s, SuppAt π v s → ∃ s', SuppAt (π.twist χ) v s' ∧ (∀ θ, pol s' θ = pol s (χ.loc v * θ)) ∧
      (∀ ζ, ζ ∈ chars s' ↔ ∃ ξ ∈ chars s, ζ = ξ * χ.loc v) ∧ s'.map Sigma.fst = s.map Sigma.fst

def SideXAt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (σ : CuspSub K n) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 K)), GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ S →
    ∀ B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ, (∀ w ∉ S, (CG.mk σ).HasSat w (B w)) →
    ∀ (s : ∀ v : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (v.adicCompletion K))) (q : ℕ) (f : HeightOneSpectrum (𝓞 K) → ℕ),
      1 < q → (∀ v ∈ S, SuppAt σ v (s v) ∧ (cnt (s v) 1 ≠ 0 → Ideal.absNorm v.asIdeal = q ^ f v)) →
      ∃ β : ℂ[X], β ≠ 0 ∧ PairG (eulerL K (cx B) S) (eulerLd K (cx B) S) β q (∏ v ∈ S, (pol (s v) 1).comp (X ^ f v))

def SideXCen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ σ : CuspSub K n,
    Cm.carrier σ ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms K n → SideXAt K σ

def SideX : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ σ : CuspSub K n, SideXAt K σ

def MatchBCX : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → ∀ η : HChar K,
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∀ w : PlacesOver L v,
      IsPrimitiveRoot (η.val v) (fdeg w) ∧ Fintype.card (PlacesOver L v) * fdeg w = Module.finrank K L) →
    ∀ (v : HeightOneSpectrum (𝓞 K)) s (s' : ∀ w : PlacesOver L v, Multiset (IrrGL (w.1.adicCompletion L))),
      SuppAt π v s → (∀ w, SuppAt P w.1 (s' w)) → ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      ∏ j ∈ Finset.range (Module.finrank K L), pol s (θ * (η ^ j).loc v) = ∏ w, (pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w)

def MatchIndX : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) s (s' : ∀ w : PlacesOver M v, Multiset (IrrGL (w.1.adicCompletion M))),
      SuppAt P v s → (∀ w, SuppAt π w.1 (s' w)) → ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      pol s θ = ∏ w, (pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w)

def UpDownX : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → ∀ (v : HeightOneSpectrum (𝓞 K)) s
      (s' : ∀ w : PlacesOver L v, Multiset (IrrGL (w.1.adicCompletion L))), SuppAt π v s → (∀ w, SuppAt P w.1 (s' w)) →
      (TorAt π v → ∀ w, ∀ ζ ∈ chars (s' w), ∃ ξ ∈ chars s, ζ = ξ.comp (nm w)) ∧
      ∀ ξ ∈ chars s, ∃ w, ξ.comp (nm w) ∈ chars (s' w)

def IndX : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) s (s' : ∀ w : PlacesOver M v, Multiset (IrrGL (w.1.adicCompletion M))),
      SuppAt P v s → (∀ w, SuppAt π w.1 (s' w)) → ∀ ξ ∈ chars s, ∃ w, ξ.comp (nm w) ∈ chars (s' w)

def WinUpDown : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → ∀ (t : ℝ) (v : HeightOneSpectrum (𝓞 K)),
      (WinAt π t v → ∀ w : PlacesOver L v, WinAt P t w.1 ∧ ThruAt P w) ∧
      ((∀ w : PlacesOver L v, WinAt P t w.1 ∧ ThruAt P w) → WinAt π t v)

def WinInd : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), (∀ w : PlacesOver M v, WinAt π t w.1 ∧ ThruAt π w) → WinAt P t v

def CharAbs : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ a : ℝ, ∀ v : HeightOneSpectrum (𝓞 K), IsSmoothChar (χ.loc v) ∧
    ‖((χ.loc v (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ a

def WinTw : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (χ : HChar K), ∃ a : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (t : ℝ) v,
    WinAt π t v → WinAt (π.twist χ) (t + a) v

def SuppSmo : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ π π' : CuspSub K n,
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B ∧ (CG.mk π').HasSat v B) →
    ∀ (t : ℝ) v, WinAt π t v → WinAt π' t v

def WinUnl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (π : CuspSub K n) (t : ℝ) v, WinAt π t v →
    ∀ s, SuppAt π v s → Unl (Ideal.absNorm v.asIdeal) s

def UnlFull : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)),
    HasSupport π (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) →
    Unl (GroundTheory.LocalField.residueCard k) (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) →
    Nonempty (π.Equiv (prinSeries ω))

def WinOf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ π : CuspSub K n, ∃ t : ℝ, ∀ v,
    TorAt π v → (∀ s, SuppAt π v s → Unl (Ideal.absNorm v.asIdeal) s) → WinAt π t v

def SphUnl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) v B, (CG.mk π).HasSat v B →
    TorAt π v ∧ ∀ s, SuppAt π v s → Unl (Ideal.absNorm v.asIdeal) s

def WinSph : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (t : ℝ) v, WinAt π t v →
    (∀ s, SuppAt π v s → ∀ ξ ∈ chars s, IsUnram ξ) → ∃ B, (CG.mk π).HasSat v B

def AdSys {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (D : Ad3.Dat) (P : CuspSub K 3) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ w : PlacesOver K v,
    (CG.mk P).HasSat w.1 {D.ν v (unif (v.adicCompletion ℚ)) ^ fdeg w, 1, (D.ν v (unif (v.adicCompletion ℚ)) ^ fdeg w)⁻¹}

def lin {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ξ : kˣ →* ℂˣ) : ℂ[X] :=
  if IsUnram ξ then 1 - C ((ξ (unif k) : ℂˣ) : ℂ) * X else 1

def MatchAd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ D : Ad3.Dat, Ad3.An D →
    ∀ P : CuspSub K 3, AdSys D P → ∃ η : HChar ℚ, ∀ (v : HeightOneSpectrum (𝓞 ℚ)), (∀ w : PlacesOver K v, (η.loc v).comp (nm w) = 1) ∧
      (∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ → ∀ w : PlacesOver K v, IsUnram (θ.comp (nm w)) →
        ((Finset.range 2).filter fun j => IsUnram (θ * (η ^ j).loc v)).card = ∑ w' : PlacesOver K v, fdeg w') ∧
      ∀ s' : ∀ w : PlacesOver K v, Multiset (IrrGL (w.1.adicCompletion K)), (∀ w, SuppAt P w.1 (s' w)) →
        ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ →
          ∏ j ∈ Finset.range 2, lin (D.ν v * (θ * (η ^ j).loc v)) * lin (θ * (η ^ j).loc v) * lin ((D.ν v)⁻¹ * (θ * (η ^ j).loc v)) =
            ∏ w, (pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w)

def AdK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ D : Ad3.Dat, Ad3.An D →
    ∀ P : CuspSub K 3, AdSys D P → ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (w : PlacesOver K v), WinAt P 0 w.1 ∧
      ∀ s, SuppAt P w.1 s → ∀ ζ ∈ chars s, ζ = (D.ν v).comp (nm w) ∨ ζ = 1 ∨ ζ = ((D.ν v).comp (nm w))⁻¹

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
