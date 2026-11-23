import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralsAgreeOf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc Model Rep Base Geo Chars RealMaps FinMaps pure PolMatch IsMatched Decay OneConst Coinv IsConst)
open GlobalTheory.WeilM (SB schA)

variable {D : D7}

def polSpan {n d : ℕ} {Y : Spc D.host.F D.host.E n} {Z : Spc D.host.F D.host.E d} (Mo : Model D.sp.cm.sig Y Z)
    (Bs : Base D.host.F D.host.E) : Submodule ℂ ((Fin n × Fin d → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) ∧
    f ∈ Mo.Pol Bs.ψ Bs.emb ∧ Φ = pure f φ}

structure PairSit (ε : Bool) {M X : HSp D} (θ : InfFam D) (A : Fr M) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) {Y : Spc D.host.F D.host.E M.rank} {Z : Spc D.host.F D.host.E d}
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X) : Prop where

  fam : IsInfFam θ

  base : Bs.IsGood D.sp.cm.sig

  good : Mo.IsGood Bs.ψ

  weilD : Mo.IsWeil Bs.ψ χ₁ χ₂ om

  weil : IsWeil Bs.ψ ε M X χ₁ χ₂ ω

  dict : IsDict (ε := ε) e Bs.ψ ω Mo om c hY hZ

  herm : ∃ r s, Y.IsHerm D.sp.cm.sig Bs r s

  skew : ∃ r s, Z.IsSkew D.sp.cm.sig Bs r s

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Y.θ w = (if ε then (1 : ℂ) else -1) • A.cart τ ∧
    Z.θ w = (reindex e e (B.cart τ)).map conj

structure Sit {W W₁ X : HSp D} (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank) : Prop where

  fam : IsInfFam θ

  tri : IsTriple W W₁ X α β

  hν : IsHaarFD W ν 𝓕

  hν₁ : IsHaarFD W₁ ν₁ 𝓕₁

  weilA : IsWeil Bs.ψ true W X β (β / α) ωA

  weilB : IsWeil Bs.ψ false W₁ X α (α / β) ωB

  read : IsReading Bs.ψ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ Bs Γ Xc

  dictA : IsDict (ε := true) e Bs.ψ ωA Γ.M om 1 read.JW read.JX

  dictB : IsDict (ε := false) e Bs.ψ ωB Γ.M' om' (-1) read.JW₁ read.JX

  matched : IsMatched Bs Γ Xc om om' R Rf

  decay : Decay Bs Γ om om'

  const : OneConst Bs Γ Xc om om' R Rf

  coinv : Coinv Bs Γ Xc om om' Rf

def ThetaLin : Prop :=
  ∀ (D : D7) (ε : Bool) (M X : HSp D) (θ : InfFam D) (A : Fr M) (B : Fr X) (d : ℕ) (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E d)
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X), PairSit ε θ A B e Bs Mo om c hY hZ χ₁ χ₂ ω →
    polSpan Mo Bs ≤ schA D.host.F (Fin M.rank × Fin d) ∧
    (∀ Φ₁ ∈ schA D.host.F (Fin M.rank × Fin d), ∀ Φ₂ ∈ schA D.host.F (Fin M.rank × Fin d),
      thetaOf (ε := ε) e Mo Bs.ψ (Φ₁ + Φ₂) = thetaOf (ε := ε) e Mo Bs.ψ Φ₁ + thetaOf (ε := ε) e Mo Bs.ψ Φ₂) ∧
    ∀ (s : ℂ), ∀ Φ ∈ schA D.host.F (Fin M.rank × Fin d),
      thetaOf (ε := ε) e Mo Bs.ψ (s • Φ) = s • thetaOf (ε := ε) e Mo Bs.ψ Φ

def AlgOf : Prop :=
  ∀ (D : D7) (ε : Bool) (M X : HSp D) (θ : InfFam D) (A : Fr M) (B : Fr X) (d : ℕ) (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E d)
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X), PairSit ε θ A B e Bs Mo om c hY hZ χ₁ χ₂ ω →
    ∀ Φ ∈ polSpan Mo Bs, thetaOf (ε := ε) e Mo Bs.ψ Φ ∈ algF Bs.ψ θ ε A B

def AlgTo : Prop :=
  ∀ (D : D7) (ε : Bool) (M X : HSp D) (θ : InfFam D) (A : Fr M) (B : Fr X) (d : ℕ) (e : Fin X.rank ≃ Fin d)
    (Bs : Base D.host.F D.host.E) (Y : Spc D.host.F D.host.E M.rank) (Z : Spc D.host.F D.host.E d)
    (Mo : Model D.sp.cm.sig Y Z) (om : Rep D.sp.cm.sig Y Z) (c : D.host.E) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
    (χ₁ χ₂ : (AE D)ˣ →* Circle) (ω : WRep M X), PairSit ε θ A B e Bs Mo om c hY hZ χ₁ χ₂ ω →
    ∀ f ∈ algF Bs.ψ θ ε A B, ∃ Φ ∈ polSpan Mo Bs, thetaOf (ε := ε) e Mo Bs.ψ Φ = f

def Maps : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
      (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
      IsMatch Bs.ψ θ A A₁ B α β ωA ωB Pi rf rl p p' ∧
      ∀ Φ ∈ polSpan Γ.M Bs, ∀ Φ' ∈ polSpan Γ.M' Bs,
        p (thetaOf (ε := true) e Γ.M Bs.ψ Φ) = p' (thetaOf (ε := false) e Γ.M' Bs.ψ Φ') → PolMatch Bs Γ Xc R Rf Φ Φ'

def Closure : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∀ Φ ∈ polSpan Γ.M' Bs, ∃ Φ₀ ∈ polSpan Γ.M' Bs ⊓ Γ.M'.So Bs.ψ Bs.τ₁,
      thetaOf (ε := false) e Γ.M' Bs.ψ Φ - thetaOf (ε := false) e Γ.M' Bs.ψ Φ₀ ∈ finRel ωB (algF Bs.ψ θ false A₁ B)

def Moderate : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∀ Φ ∈ polSpan Γ.M' Bs ⊓ Γ.M'.So Bs.ψ Bs.τ₁, ModInt θ ωB ν₁ 𝓕₁ (thetaOf (ε := false) e Γ.M' Bs.ψ Φ)

def ConstEq : Prop :=
  ∀ (D : D7) (W W₁ X : HSp D) (θ : InfFam D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle)
    (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (Bs : Base D.host.F D.host.E)
    (Γ : Geo D.sp.cm.sig W.rank W₁.rank) (Xc : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (R : RealMaps D.host.F W.rank W₁.rank) (Rf : FinMaps D.host.F W.rank W₁.rank),
    Sit θ A A₁ B α β e ν 𝓕 ν₁ 𝓕₁ ωA ωB Bs Γ Xc om om' R Rf →
    ∀ c : ℂ, IsConst Bs Γ Xc om om' R Rf c → ∀ Φ ∈ polSpan Γ.M Bs, ∀ Φ' ∈ polSpan Γ.M' Bs ⊓ Γ.M'.So Bs.ψ Bs.τ₁,
      PolMatch Bs Γ Xc R Rf Φ Φ' →
      thetaInt ωA ν 𝓕 (thetaOf (ε := true) e Γ.M Bs.ψ Φ) = c • thetaInt ωB ν₁ 𝓕₁ (thetaOf (ε := false) e Γ.M' Bs.ψ Φ')

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
