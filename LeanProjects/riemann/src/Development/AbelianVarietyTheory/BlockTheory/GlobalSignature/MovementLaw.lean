import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def AgreeOff (T : ℕ) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((T : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂

def InRangeOf {K : Type} [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x

def relOrd (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : ℤ := ordDet P N₁ - ordDet P N₂

end Generic

open Classical in

def JetsIn {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (deg : X.Tau → ℤ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) : Prop :=
  ∀ x, Ξ x ≠ 0 → ∀ m : DVar X.Tau a b →₀ ℕ,
    (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
    ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

section Scalar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def muVp (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ := (mUof Ch mu i P)⁻¹

def moveScal (u : Pr.Word) (i : ℕ) {a b : ℕ} (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  ∏ P ∈ Pr.vT u, ((muVp Ch mu i P ^ (-relOrd P N₁ N₂ + relOrd P N₁' N₂') : X.Kˣ) : X.K) *
    ((Pr.T u : ℕ) : X.K) ^ (((a / 2 : ℕ) : ℤ) * relOrd P N₁' N₂' - ((b / 2 : ℕ) : ℤ) * relOrd P N₁ N₂)

end Scalar

def MoveLaw : Prop :=
  ∀ (Dt : Dat), Dt.Ok →
  ∀ (D : D7) (s : Seam D Dt.X), s.Ok → s.σ₀ = Dt.sig0 →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
  ∀ (cD : D.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Dt.X.F) → HeightOneSpectrum (𝓞 Dt.X.E)), IsSel Dt.X sel →
  ∀ (S : Set ℕ), hostS D.host.q D.host.d (Dt.Pr.g 0) (Dt.Pr.g 1) (Set.range Dt.Pr.T ∪ (D.host.small : Set ℕ)) ⊆ S →
  ∀ (mu : Tup Dt.X.F Dt.X.E Dt.X.K S) (cst : LocCst Dt.X (rowSG Dt.Pr sel mu)) (u : Dt.Pr.Word),
    (∀ P ∈ Sall (Pr := Dt.Pr) sel mu u, Nat.Coprime (Ideal.absNorm cc) (Formalism.L2.Col.qOf P)) →
  ∀ (i j : ℕ), j = i + 1 → j ≤ Dt.R.m →
  ∀ (N₁ N₂ : Submodule (𝓞 Dt.X.E) (Sp Dt.X.E (Dt.R.N i))) (N₁' N₂' : Submodule (𝓞 Dt.X.E) (Sp Dt.X.E (Dt.R.N j))),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    AgreeOff (Dt.Pr.T u) N₁ N₂ → AgreeOff (Dt.Pr.T u) N₁' N₂' →
  ∀ (fr : Frs Dt.X.E (Dt.R.N i) (rowSG Dt.Pr sel mu)) (fr' : Frs Dt.X.E (Dt.R.N j) (rowSG Dt.Pr sel mu))
    (Ξ : HomE Dt.X.E (Dt.R.N i) (Dt.R.N j) → Dt.X.K),
    InRangeOf (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    InRangeOf (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    JetsIn (ambOf s B χ cD) (Sall (Pr := Dt.Pr) sel mu u) (cBof sel mu cst u)
      (fun τ => ∑ k, (Dt.W.nuW u (i + 1) τ).w k) N₁ N₁' Ξ →
    JetsIn (ambOf s B χ cD) (Sall (Pr := Dt.Pr) sel mu u) (cBof sel mu cst u)
      (fun τ => ∑ k, (Dt.W.nuW u (i + 1) τ).w k) N₂ N₂' Ξ →
    kerOf (stepT Dt.W Dt.Ch sel mu cst (ambOf s B χ cD) u i (Dt.W.lamTrue u j))
        (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      moveScal Dt.Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT Dt.W Dt.Ch sel mu cst (ambOf s B χ cD) u i (Dt.W.lamTrue u j))
          (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

end GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw
