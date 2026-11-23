import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MeanPeriodLogarithms

noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open scoped ComplexOrder

section Ops

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def OpLe (S S' : GSD K) (v : InfinitePlace K) (T : S.V →ₗ[K] S'.V) (t : ℝ) : Prop :=
  ∀ x : S.V, (S'.pairAt v (T x) (T x)).re ≤ t * (S.pairAt v x x).re

def PosAt (S : GSD K) (v : InfinitePlace K) : Prop := (S.gramV.map v.embedding).PosSemidef

end Ops

section Coef

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι]

def sqAt (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (σ ((bVV K lam).repr x i)) *
    σ (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j)) * σ ((bVV K lam).repr x j)).re

def CoefOpLe (σ : K →+* ℂ) {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') (t : ℝ) : Prop :=
  ∀ x, sqAt σ lam' (T x) ≤ t * sqAt σ lam x

open Classical in

def degAt {a b : ℕ} (e : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

end Coef

section Data

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

def LocSmall (q : ℕ) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Φ x ≠ 0 → ∀ y ∈ M, x y ∈ M') ∧ (∀ x z : HomE E a b, (∀ y ∈ M, z y ∈ M') → Φ (x + (q : E) • z) = Φ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Φ x)‖ ≤ β

def SmallDatum (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)
    (Ξ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ homAt S N N') ∧ (∀ x, ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Ξ x)‖ ≤ β

end Data

def Pres (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (G F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℂ) (y : Fin k → TaylorLogMetric.VC D a b), (∀ i, r i ∈ TaylorLogMetric.Qbar) ∧ (∀ i, StandardLatticesGL3.LaQ D T L L' (y i)) ∧
    (∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ∑ i, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i)‖ ≤ n) ∧ F = StandardLatticesGL3.comb D T r y G

def toHost {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  fun w => F fun τ => w (s.iT τ)

def supConst (D : D7) (a b : ℕ) : ℝ :=
  3 * (2 * ((TaylorLogMetric.fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (TaylorLogMetric.fF D * a * b)

def errUnit (N : NumDatum) (T : ℕ) : ℝ :=
  N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T)

def Hyp {D : D7} (N : NumDatum) {X : Fields} (s : Seam D X) {Pr : Primes X} (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m)
    (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
    (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
    (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) : Prop :=
  HostTie N s Pr ∧ WeightTie N W pl u δ ∧ CharTie N s W Ch G sel ∧ AnalyticTie D dl χ cD ∧ mu = 1 ∧ cst.sharp = true ∧
    I.Ok Ch sel mu cst G (N.R.m - 2) ∧ Sizes Pr W N.sc.a ∧ SizeRows N δ (Pr.T u)

def FamilyTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → StandardLatticesGL3.natTie D cc δ (B.eNat χ)

def FamilyVectors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.VecP χ

def FamilyNorms : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.ThP C χ

def PeriodLattices : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    TaylorLogMetric.IsChi D χ → IsDgen D cD → B.kc.YFinite → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))), Even a → Even b →
    (∀ P ∈ S, conjPrime₂ P ∉ S) → (ambOf s B χ cD).AAUnit S → (ambOf s B χ cD).LaHyp a b S

def CosetRefinement : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (Md : ℕ), X.Ok →
    (∀ P ∈ S, (2 : 𝓞 X.E) ∉ P.asIdeal) → Odd Md → A.LaHyp a b S → A.IndAdd a b S Md

end GlobalTheory.ColNorms
