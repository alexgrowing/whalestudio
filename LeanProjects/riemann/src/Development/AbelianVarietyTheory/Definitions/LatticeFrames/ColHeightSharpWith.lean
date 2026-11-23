import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightWith

noncomputable section

namespace GlobalTheory.Core.Ht2

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.CoreHt

def SizeRowsS (CY : ℝ) (N : NumDatum) (δ : Code N) : Prop :=
  (Real.log N.rd ≤ N.sc.L ∧ Real.log N.q ≤ N.sc.L ∧ Real.log N.d ≤ N.sc.L ∧ Real.log (4 * N.sc.x) ≤ N.sc.L ∧
    |N.logDerivativeAtOne| ≤ N.sc.L) ∧
  (∀ i, ((N.R.k : ℝ) * N.sc.b) ^ 8 ≤ N.g i ∧ Real.log (N.g i) ≤ CY * N.sc.L + 1) ∧
  True ∧
  (N.R.f : ℝ) * N.Nm ≤ N.sc.b ∧
  (∀ j ∈ N.lifts, ∀ z, ∀ i < N.R.N (j - 1), 0 ≤ N.nu δ j z i ∧ ((N.nu δ j z i : ℚ) : ℝ) ≤ 3 * N.sc.a) ∧
  (∀ z i j, |(((N.hc z).b i - (N.hc z).e j : ℚ) : ℝ)| ≤ N.eta) ∧
  (∀ z i, 0 ≤ (N.hc z).v i ∧ (((N.hc z).v i : ℚ) : ℝ) ≤ N.Sc) ∧
  (∀ z (i : Fin N.R.k), 1 ≤ i.1 → i.1 + 1 < N.R.k → 0 ≤ N.uW δ z i ∧ ((N.uW δ z i : ℚ) : ℝ) ≤ N.Sc) ∧
  (∀ t ∈ N.TT, N.sc.b' ≤ ((N.bT t : ℚ) : ℝ) ∧ ((N.bT t : ℚ) : ℝ) ≤ 2 * N.sc.b') ∧
  ∀ z, ¬ IsTopPl N z → ∀ hk : 2 ≤ N.R.k,
    (N.hc z).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).v ⟨N.R.k - 2, by omega⟩ - 1 / 2 ∧
    N.Sc ≤ (((N.hc z).u ⟨0, by omega⟩ - (N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) ∧
    (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ 3 * N.Sc

theorem sizeRowsS_of {N : NumDatum} {δ : Code N} {T : ℕ} (h : SizeRows N δ T) : SizeRowsS 9 N δ :=
  ⟨h.1, h.2.1, trivial, h.2.2.2⟩

def HypS (CY : ℝ) {D : D7} (N : NumDatum) {X : Fields} (s : Seam D X) {Pr : Primes X} (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m)
    (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
    (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
    (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) : Prop :=
  HostTie N s Pr ∧ WeightTie N W pl u δ ∧ CharTie N s W Ch G sel ∧ AnalyticTie D dl χ cD ∧ mu = 1 ∧ cst.sharp = true ∧
    I.Ok Ch sel mu cst G (N.R.m - 2) ∧ Sizes Pr W N.sc.a ∧ SizeRowsS CY N δ

def logA (N : NumDatum) (T : ℕ) : ℝ :=
  ((N.TT.card : ℝ) * N.sc.b' + (N.R.f : ℝ) * (N.Sc + (N.R.m : ℝ) * N.eta + (N.Nm : ℝ))) * Real.log T

def logB (N : NumDatum) (T : ℕ) : ℝ := (N.R.f : ℝ) * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log T

def hZeroS (N : NumDatum) (C : ℝ) (δ : Code N) (T : ℕ) : ℝ :=
  hZero N C δ T + C * (((N.TT.card : ℝ) * N.sc.b' + (N.R.f : ℝ) * (N.Sc + (N.R.m : ℝ) * N.eta + (N.Nm : ℝ)) +
    (N.R.f : ℝ) * (N.R.m : ℝ) ^ 3 * (N.Nm : ℝ) ^ 2) * Real.log T)

def ColHeightSharpWith (CY C : ℝ) : Prop :=
  ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (hX : X.Ok) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R)
    (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
    (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau)
    (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b)
    (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF W sel mu I u j).Ok) (hL : I.Ok Ch sel mu cst G (N.R.m - 2)),
    HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD →
    mu = 1 → cst.sharp = true → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) →
    Sizes Pr W N.sc.a → SizeRowsS CY N δ →
      DualHtLe (MramH W Ch hX u) (MtildeH W Ch hX sel mu (rPsymF Ch))
        (phiCol W Ch hX sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hL)
        (hZeroS N C δ (Pr.T u))

def ColHeightSharp : Prop := ∀ CY : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ColHeightSharpWith CY C

end GlobalTheory.Core.Ht2

end
