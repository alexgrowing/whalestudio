import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

def Amb.AnaStep {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) : Prop :=
  A.LaHyp a b Sall ∧ A.ESmooth a b ∧ A.JetsRat a b Sall D

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def ThHyp : Prop :=
  (∀ i, i ≤ m2 → A.AnaStep (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) ∧
  A.AnaStep (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) ∧
  (∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) ∧
  ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho

def KerHypOn (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) ∧ Cp1EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY ∧
    Cp2EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P

end Inst

section Nat

open Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

def NatOk (σ₀ : X.K →+* ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ δ ≠ 0 ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD ∧ s.Ok ∧ s.σ₀ = σ₀

end Nat

section InstN

open Formalism.MainNotions

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m)

def LawTies : Prop :=
  MuqTie Ch sel mu cst ∧ MuqTieG sel mu cst G.σ₀ G.mu0 ∧ (∃ eta : Formalism.L2.Host.HChar X.E, Ch.Tied G.σ₀ (fun j τ => (W.row τ).e j) G.mu0 eta) ∧
    ∀ u τ, RowPar.of (W.hc u τ) = W.row τ

variable {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

def ThHypN : Prop :=
  NatOk s cc δ χ cD G.σ₀ ∧ LawTies W Ch sel mu cst G ∧ ThHyp W Ch sel mu cst (ambOf s B χ cD) u m2

end InstN

section Tab

variable {X : Fields} (A : Amb X) {a b : ℕ}

def Amb.tabK (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => Ξ x * A.jetK Sall N N' cB x m

def Amb.thDat (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) : VCx X.Tau a b → ℂ := fun z =>
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => A.σ₀ (Ξ x) * A.thInd Sall N N' cB x z

def TabNe {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (n : ι → ℕ) (J : (DVar ι a b →₀ ℕ) → K) : Prop :=
  ∃ P ∈ DIV.VV K lam, jetMap J n P ≠ 0

end Tab

section Ne

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def scalK (i : ℕ) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a (rowSG Pr sel mu)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr' : Frs X.E b (rowSG Pr sel mu)) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N fr *
    (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N' fr')⁻¹

def FirstCharacterPointNonvanishing (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) : Prop :=
  Y ∈ ybSet sel mu cst p.deco.1.N ∧ cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y ≠ 0

def SecondCharacterPointNonvanishing (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu) : Prop :=
  Y ∈ ybSet sel mu cst p.deco.1.N ∧ cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p Y d ≠ 0

end Ne

end Formalism.L2.Ker
