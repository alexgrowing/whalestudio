import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Lattices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def idxExp {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : ℤ :=
  ordDet P N₂ - ordDet P N₁

def AgreeOff (T : ℕ) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((T : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂

def InBox {K : Type} [Field K] {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt Sall N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt Sall N N'), Ξ (x + y) = Ξ x

end Lattices

section Jets

variable {X : Fields} {a b : ℕ}

def degAt (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) : ℕ := ∑ β : Fin b, ∑ α : Fin a, m (τ, β, α)

def degNu (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (τ : X.Tau) : ℤ :=
  ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))

def JetsIn (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ x ∈ divLat cA (homAt Sall N N'), ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m

end Jets

def locScal {K : Type} [Field K] (a b q : ℕ) (w : Kˣ) (e e' : ℤ) : K :=
  ((w ^ (e' - e) : Kˣ) : K) * (q : K) ^ (((b / 2 : ℕ) : ℤ) * e - ((a / 2 : ℕ) : ℤ) * e')

section Scal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def moveScal (u : Pr.Word) (i : ℕ) {a b : ℕ} (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  ∏ P ∈ Pr.vT u, locScal a b (Pr.T u) (mUof Ch mu i P) (idxExp P N₁ N₂) (idxExp P N₁' N₂')

end Scal

def MoveLaw : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    X.Ok → Pr.Ok → Ch.FromHecke W s.σ₀ → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) →
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ →
    (∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal)) →
    ∀ (i : ℕ), i < R.m → ∀ (b : ℕ), b = R.N (i + 1) → ∀ (lam' : X.Tau → DomWeight b)
      (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
      (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
      IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
      AgreeOff (Pr.T u) N₁ N₂ → AgreeOff (Pr.T u) N₁' N₂' →
      InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
      InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
      JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁' →
      JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂' →
      kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
        moveScal Ch mu u i N₁ N₂ N₁' N₂' •
          kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

theorem locScal_one_one {K : Type} [Field K] (R : Ranks) (i q : ℕ) (w : Kˣ) :
    locScal (R.N i) (R.N (i + 1)) q w 1 1 = (q : K) ^ ((R.t + 1) / 2) := by
  obtain ⟨c, hc⟩ := R.t_odd
  have h1 : R.N (i + 1) = R.N i + 2 * (c + 1) := by
    unfold Ranks.N
    rw [hc]
    ring
  have h2 : (R.t + 1) / 2 = c + 1 := by omega
  have h3 : (((R.N (i + 1) / 2 : ℕ) : ℤ) * 1 - ((R.N i / 2 : ℕ) : ℤ) * 1) = ((c + 1 : ℕ) : ℤ) := by
    rw [h1]
    omega
  unfold locScal
  rw [h3, h2, sub_self, zpow_zero, Units.val_one, one_mul, zpow_natCast]

theorem locScal_zero_zero {K : Type} [Field K] (a b q : ℕ) (w : Kˣ) : locScal a b q w 0 0 = 1 := by
  simp [locScal]

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add ((R.t_odd.add_one).mul_left j)

end GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
