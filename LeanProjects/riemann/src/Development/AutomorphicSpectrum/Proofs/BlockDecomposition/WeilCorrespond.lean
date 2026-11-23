import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralsAgreeOf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO

namespace GlobalTheory.CompanionTheory.AgreeO.Read

def BaseChars : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle),
    IsTriple W W₁ X α β → ∀ (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w)
      (τ : InfinitePlace D.host.F → D.what₂.Tau), Function.Bijective τ → (∀ w x, (emb w).1 x = conj (tauE D (τ w) x)) →
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E),
      Bs.ψ = ψ ∧ Bs.emb = emb ∧ Xc.α = α ∧ Xc.β = β ∧ Bs.IsGood D.sp.cm.sig ∧ Xc.IsGood Bs W.rank W₁.rank ∧
        ∀ w, ((W.rank + W₁.rank : ℕ) : ℤ) < Bs.mα w - Bs.mβ w

def SkewSpace : Prop :=
  ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (τ : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (Bs.emb w).1 x = conj (tauE D (τ w) x)) → ∀ (X : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
      (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ) (q d : ℕ) (e : Fin X.rank ≃ Fin d), IsSelfDualC X Λ →
      (∀ τ', IsCartanInv (gramAt D X τ') (s τ')) → (∀ τ', Formalism.UG.HasSignature (gramAt D X τ') (X.rank - q) q) → q ≤ X.rank →
      ∃ Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d, Z.J = skewJ X e ∧ (∀ w, Z.θ w = (reindex e e (s (τ w))).map conj) ∧
        Z.IsSkew D.sp.cm.sig Bs (d - q) q

def ConjDomain : Prop :=
  ∀ (D : D7) (M : HSp D) (J : Matrix (Fin M.rank) (Fin M.rank) D.host.E) (c : D.host.E) (h : J = c • M.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 →
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h))

def ThetaBij : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.ψ = ψ →
    Bs.IsGood D.sp.cm.sig → ∀ (ε : Bool) (M X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      Y.IsHerm D.sp.cm.sig Bs r s → Z.IsSkew D.sp.cm.sig Bs r' s' →
      Y.J = (if ε then (1 : D.host.E) else -1) • M.gram → Z.J = skewJ X e →
      ∀ Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z, Mo.IsGood ψ →
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), IsThetaFunO ψ (sgn ε M) X (thetaOf (ε := ε) e Mo ψ Φ)) ∧
      (∀ f, IsThetaFunO ψ (sgn ε M) X f → ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), thetaOf (ε := ε) e Mo ψ Φ = f) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d),
        thetaOf (ε := ε) e Mo ψ Φ = thetaOf (ε := ε) e Mo ψ Φ' → Φ = Φ'

def WeilCorrespond : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.ψ = ψ →
    Bs.IsGood D.sp.cm.sig → ∀ (ε : Bool) (M X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      0 < M.rank → 0 < d → Y.IsHerm D.sp.cm.sig Bs r s → Z.IsSkew D.sp.cm.sig Bs r' s' →
      ∀ (c : D.host.E) (hc : c = if ε then (1 : D.host.E) else -1) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
        (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z), Mo.IsGood ψ →
      ∀ (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z),
        IsWeil ψ ε M X χ χ' ω → Mo.IsWeil ψ χ χ' om →
        ∀ g h, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d),
          thetaOf (ε := ε) e Mo ψ (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hY g, skewU X e hZ h) Φ) = ω (g, h) (thetaOf (ε := ε) e Mo ψ Φ)

end GlobalTheory.CompanionTheory.AgreeO.Read

end
