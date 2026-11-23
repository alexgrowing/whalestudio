import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.HarderNarasimhan.QuotRealize

noncomputable section

namespace GlobalTheory.CoreHt

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def meanPl (c : InfinitePlace K → ℝ) : ℝ := (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, c v

def DualHtLe (A B : HLat K) (Φ : A.V →ₗ[K] Module.Dual K B.V) (h : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ,
    (∀ v, Formalism.HN.opNormAt A.b A.X B.b.dualBasis (Formalism.HN.dualFrame B.X) v Φ ^ 2 ≤ Real.exp (c v)) ∧ meanPl c ≤ h

def PairHtLe (A B : HLat K) (Φ : A.V →ₗ[K] Module.Dual K B.V) (h : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ,
    (∀ v x y, v (Φ x y) ^ 2 ≤ Real.exp (c v) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x ^ 2 * Formalism.HermitianLatticesTheory.normAt B.b B.X v y ^ 2) ∧ meanPl c ≤ h

def ColHtLe (Q : KerChain K) (h : ℝ) : Prop :=
  ∃ t : InfinitePlace K → ℝ,
    (∀ v (φ : (Q.F 0).Forms), (Q.S₁.ipAt Q.hS₁ v (Q.col φ) (Q.col φ)).re ≤
      Real.exp (t v) * (famIpAt (Q.F 0) (Q.hF 0) v φ φ).re) ∧ meanPl t ≤ h

end Generic

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
  (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def phiCol {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : I.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst I u m2 b} (A : ChKer W Ch sel mu cst I P u m2 b hY)
    (hF : ∀ j, (chF W sel mu I u j).Ok) {G : ChGlob X R.m} (hL : I.Ok Ch sel mu cst G m2) :
    (MramH W Ch hX u).V →ₗ[X.K] Module.Dual X.K (MtildeH W Ch hX sel mu P).V :=
  (PtilE W Ch sel mu P (mtildeOk W Ch sel mu hX P) u) ∘ₗ (colC A hF hL) ∘ₗ (MramV W Ch u).subtype

end Col

def hZero (N : NumDatum) (C : ℝ) (δ : Code N) (T : ℕ) : ℝ := N.hA C T + ∑ j ∈ N.lifts, N.hB C δ j

def ColHeightWith (C : ℝ) : Prop :=
  ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (hX : X.Ok) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R)
    (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
    (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau)
    (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b)
    (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF W sel mu I u j).Ok) (hL : I.Ok Ch sel mu cst G (N.R.m - 2)),
    HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD →
    mu = 1 → cst.sharp = true → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) →
    Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) →
      DualHtLe (MramH W Ch hX u) (MtildeH W Ch hX sel mu (rPsymF Ch))
        (phiCol W Ch hX sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hL)
        (hZero N C δ (Pr.T u))

def ColHeight : Prop := ∃ C : ℝ, 0 ≤ C ∧ ColHeightWith C

end GlobalTheory.CoreHt
