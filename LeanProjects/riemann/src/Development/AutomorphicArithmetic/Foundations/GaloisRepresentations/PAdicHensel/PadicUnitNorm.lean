import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.G1

def qf {R : Type} [CommRing R] (tr nm : ℤ) (a b : R) : R := a ^ 2 + (tr : R) * a * b + (nm : R) * b ^ 2

abbrev cF (E : Type) [Field E] [NumberField E] [IsCMField E] : FiniteAdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E :=
  conjFin (IsCMField.complexConj E).toRingEquiv

def LocFour : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (tr nm : ℤ), tr ^ 2 - 4 * nm ≠ 0 →
  ∀ u : v.adicCompletion F, u ≠ 0 → ∃ a b a' b' : v.adicCompletion F, qf tr nm a b + qf tr nm a' b' = u

def HenselV : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (f : Polynomial (v.adicCompletionIntegers F)) (a₀ : v.adicCompletionIntegers F), f.Monic →
  ¬ IsUnit (f.eval a₀) → IsUnit (f.derivative.eval a₀) → ∃ a, f.eval a = 0 ∧ ¬ IsUnit (a - a₀)

def LocUnit : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (tr nm : ℤ),
  ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal → ∀ u : v.adicCompletionIntegers F, IsUnit u →
  ∃ a b : v.adicCompletionIntegers F, qf tr nm a b = u

def LocRoot : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (tr nm : ℤ) (q : ℕ), q.Prime →
  (q : 𝓞 F) ∈ v.asIdeal → ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm → (∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) →
  ∃ ρ : v.adicCompletionIntegers F, ρ ^ 2 - tr * ρ + nm = 0 ∧ IsUnit (2 * ρ - tr)

def SplitRep : Prop := ∀ (R : Type) [CommRing R] (tr nm : ℤ) (ρ : R), ρ ^ 2 - tr * ρ + nm = 0 → IsUnit (2 * ρ - tr) →
  ∀ u : R, ∃ a b : R, qf tr nm a b = u

def AdFour : Prop := ∀ (F : Type) [Field F] [NumberField F] (tr nm : ℤ), tr ^ 2 - 4 * nm ≠ 0 → ∀ c : 𝓞 F, c ≠ 0 →
  ∃ a : Fin 4 → FiniteAdeleRing (𝓞 F) F,
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) * (qf tr nm (a 0) (a 1) + qf tr nm (a 2) (a 3)) = 1 ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (q : ℕ), q.Prime → (q : 𝓞 F) ∈ v.asIdeal → ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm →
      (∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) → c ∉ v.asIdeal → ∀ i, a i v ∈ v.adicCompletionIntegers F

def NormTwo : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  ∃ x y : FiniteAdeleRing (𝓞 E) E,
    algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) * (x * cF E x + y * cF E y) = 1 ∧
    ∀ (w : HeightOneSpectrum (𝓞 E)) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal →
      pLoc E w x ∈ w.adicCompletionIntegers E ∧ pLoc E w y ∈ w.adicCompletionIntegers E ∧
      pLoc E w (cF E x) ∈ w.adicCompletionIntegers E ∧ pLoc E w (cF E y) ∈ w.adicCompletionIntegers E

def BlockMat : Prop := ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ z, σ (σ z) = z) → ∀ c x y : R, σ c = c →
  c * (x * σ x + y * σ y) = 1 → ∀ m : ℕ, ∃ a : GL (Fin (2 * m + 1)) R,
    (a.val.map σ)ᵀ * Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else c) * a.val = 1 ∧
    ∀ S : Subring R, x ∈ S → y ∈ S → σ x ∈ S → σ y ∈ S → c ∈ S → ∀ i j, a.val i j ∈ S ∧ (a⁻¹).val i j ∈ S

def IsoEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Odd n →
  ∃ a : GL (Fin n) (FiniteAdeleRing (𝓞 E) E),
    (a.val.map (cF E))ᵀ * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * a.val = 1 ∧
    ∀ (w : HeightOneSpectrum (𝓞 E)) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal →
      GeneralLinearGroup.map (pLoc E w) a ∈ GlobalTheory.LFun.KGL w n

def PadMap : Prop := ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
  ∃ (v : HeightOneSpectrum ℤ) (_ : v.adicCompletion ℚ →+* w.adicCompletion F),
    ∀ q : ℤ, q ∈ v.asIdeal → (q : 𝓞 F) ∈ w.asIdeal

def Scale : Prop := ∀ (p : ℕ) (t : (AfP p)ˣ), ∃ s : ℚ, 0 < s ∧
  ∀ v : AwayP p, Valued.v (AfP.eval v (t : AfP p)) = Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) s)

def PadicUnitNorm : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : ℤ), ¬ (q : ℤ) ∣ 2 * D → ∀ u : ℚ_[q], ‖u‖ = 1 →
  ∃ x y : ℚ_[q], u = x ^ 2 - D * y ^ 2

def PadicSqFin : Prop := ∀ (q : ℕ) [Fact q.Prime], ∃ (m : ℕ) (κ : ℚ_[q] → Fin m), ∀ u u' : ℚ_[q], ‖u‖ = 1 → ‖u'‖ = 1 →
  κ u = κ u' → ∃ x : ℚ_[q], u' = u * x ^ 2

def ZUnitNorm : Prop := ∀ (v : HeightOneSpectrum ℤ) (D : ℤ), 2 * D ∉ v.asIdeal → ∀ u : v.adicCompletion ℚ, Valued.v u = 1 →
  ∃ x y : v.adicCompletion ℚ, u = x ^ 2 - D * y ^ 2

def ZSqFin : Prop := ∀ v : HeightOneSpectrum ℤ, ∃ (m : ℕ) (κ : v.adicCompletion ℚ → Fin m), ∀ u u' : v.adicCompletion ℚ,
  Valued.v u = 1 → Valued.v u' = 1 → κ u = κ u' → ∃ x, u' = u * x ^ 2

def UnitCls : Prop := ∀ (p : ℕ) (D : ℤ), D ≠ 0 → ∃ (I : Type) (_ : Finite I) (κ : (AfP p)ˣ → I), ∀ t t' : (AfP p)ˣ, κ t = κ t' →
  ∃ s : ℚ, 0 < s ∧ ∀ v : AwayP p, ∃ x y : v.1.adicCompletion ℚ,
    AfP.eval v (t' : AfP p) = algebraMap ℚ _ s * AfP.eval v (t : AfP p) * (x ^ 2 - D * y ^ 2)

abbrev inE {E : Type} [Field E] [NumberField E] [IsCMField E] (K : Type) [CommRing K] [Algebra (maximalRealSubfield E) K] (x : E) :
    K ⊗[maximalRealSubfield E] E := (1 : K) ⊗ₜ[maximalRealSubfield E] x

def TrivMat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E),
  (H.map (cj E))ᵀ = H → H.map (cj E) = H → ∀ (hd : H.det ≠ 0) (R : Type) [CommRing R] [Algebra ℚ R]
  (K : Type) [Field K] [Algebra (maximalRealSubfield E) K] (ψ : R →+* K) (β : Matrix (Fin n) (Fin n) E)
  (x : (R ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) (t : R),
  (x : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : R) ⊗ₜ[ℚ] β) * (starT (hermStar H hd) R x).unop = algebraMap R _ t →
  ∃ X : Matrix (Fin n) (Fin n) (K ⊗[maximalRealSubfield E] E), IsUnit X.det ∧
    X * (β * H⁻¹).map (inE K) * (X.map (GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K))ᵀ = ψ t • (H⁻¹).map (inE K)

def CongrScale : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M N N' : Matrix (Fin n) (Fin n) E)
  (K : Type) [Field K] [Algebra (maximalRealSubfield E) K] (θ : E) (D : ℤ), IsCMField.complexConj E θ = -θ → θ ^ 2 = (D : E) →
  ∀ (t t' a b : K) (s : ℚ), t' ≠ 0 → t' = (s : K) * t * (a ^ 2 - D * b ^ 2) →
  ∀ X X' : Matrix (Fin n) (Fin n) (K ⊗[maximalRealSubfield E] E), IsUnit X.det → IsUnit X'.det →
  X * N.map (inE K) * (X.map (GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K))ᵀ = t • M.map (inE K) →
  X' * N'.map (inE K) * (X'.map (GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K))ᵀ = t' • M.map (inE K) →
  GlobalTheory.HermGlobal.CongrOver (IsCMField.complexConj E) K ((s : E) • N) N'

def SplitCongr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (N N' : Matrix (Fin n) (Fin n) E),
  (∀ a b, IsCMField.complexConj E (N a b) = N b a) → (∀ a b, IsCMField.complexConj E (N' a b) = N' b a) → N.det ≠ 0 → N'.det ≠ 0 →
  ∀ (K : Type) [Field K] [Algebra (maximalRealSubfield E) K] (θ : E) (D : ℤ), D ≠ 0 → IsCMField.complexConj E θ = -θ →
  θ ^ 2 = (D : E) → ∀ r : K, r ^ 2 = (D : K) → GlobalTheory.HermGlobal.CongrOver (IsCMField.complexConj E) K N N'

def InfCongr : Prop := ∀ (n : ℕ) (G G' : Matrix (Fin n) (Fin n) ℂ), G.IsHermitian → G'.IsHermitian → ∀ ε : ℝ,
  (∀ x : Fin n → ℂ, x ≠ 0 → 0 < ε * (star x ⬝ᵥ (G *ᵥ x)).re) → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < ε * (star x ⬝ᵥ (G' *ᵥ x)).re) →
  ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ G' = Qᵀ * G * Q.map (starRingEnd ℂ)

def mat {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] (S : Setup A n p) (x : S.G.C) :
    Matrix (Fin n) (Fin n) E := x

open Classical in

def DefSign : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (B : DForm S.G), (∀ a b, IsCMField.complexConj E ((mat S B.β * (A.H n)⁻¹) a b) = (mat S B.β * (A.H n)⁻¹) b a) ∧
    (mat S B.β * (A.H n)⁻¹).det ≠ 0 ∧ ∀ (τ : E →+* ℂ) (x : Fin n → ℂ), x ≠ 0 →
      0 < (if InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ then (1 : ℝ) else -1) *
        (star x ⬝ᵥ ((mat S B.β * (A.H n)⁻¹).map τ *ᵥ x)).re

def RelOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (B B' : DForm S.G) (s : ℚ), 0 < s → ∀ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 →
  mat S B'.β * (A.H n)⁻¹ = Pᵀ * ((s : E) • (mat S B.β * (A.H n)⁻¹)) * P.map (IsCMField.complexConj E) → DForm.Rel B B'

def FinCongr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (B B' : DForm S.G) (x x' : (AfP p ⊗[ℚ] S.G.C)ˣ) (t t' : (AfP p)ˣ), Triv S.G (AfP p) B.β x t → Triv S.G (AfP p) B'.β x' t' →
  ∀ s : ℚ, 0 < s → (∀ v : AwayP p, ∃ a b : v.1.adicCompletion ℚ,
    AfP.eval v (t' : AfP p) = algebraMap ℚ _ s * AfP.eval v (t : AfP p) * (a ^ 2 - ((A.tr ^ 2 - 4 * A.nm : ℤ) : v.1.adicCompletion ℚ) * b ^ 2)) →
  ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
    GlobalTheory.HermGlobal.CongrOver (IsCMField.complexConj E) (w.adicCompletion (maximalRealSubfield E))
      ((s : E) • (mat S B.β * (A.H n)⁻¹)) (mat S B'.β * (A.H n)⁻¹)

def FinCls : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  Finite (DFCls S.G)

end UpperTheory.Gal.G1
