import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice

namespace GlobalTheory.HSShort

def ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (G : MvPolynomial (Fin B × Fin N) F) : ℝ := formHeight 0 w A G

def cst (n Λ : ℝ) : ℝ := Real.log (n * Λ) + (Real.log n + 1) / 2

structure Lat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  det : ∀ σ, (A σ).det ≠ 0
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def HtMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ : ℝ), Lat w A Λ → (∀ (a a' : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F), G ≠ 0 → G' ≠ 0 →
      IsMultiHomogeneous a G → IsMultiHomogeneous a' G' → ht w A (G * G') = ht w A G + ht w A G') ∧
    ∀ c : F, c ≠ 0 → ht w A (C c : MvPolynomial (Fin B × Fin N) F) = 0

def HtLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ : ℝ), Lat w A Λ → ∀ (a : Fin B → ℕ) (G : MvPolynomial (Fin B × Fin N) F), G ≠ 0 → IsMultiHomogeneous a G →
      -(cst n Λ * ∑ b, (a b : ℝ)) ≤ ht w A G

abbrev GenK (F : Type) [Field F] (D N : ℕ) : Type := FractionRing (MvPolynomial (Fin D × Fin N) F)

def gen (F : Type) [Field F] (D N : ℕ) : Fin D → Fin N → GenK F D N :=
  fun i j => algebraMap (MvPolynomial (Fin D × Fin N) F) _ (X (i, j))

def normForm (K : Type) [Field K] {O : Type} [CommRing O] [Algebra K O] [Module.Finite K O] {N : ℕ} (r : Fin N → O) :
    MvPolynomial (Fin 1 × Fin N) K :=
  (∑ j, (X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin N) K) •
    (Algebra.leftMulMatrix (Module.finBasis K O) (r j)).map (C : K → MvPolynomial (Fin 1 × Fin N) K)).det

def Primitive {F : Type} [Field F] {D N : ℕ} (G : MvPolynomial (Fin (D + 1) × Fin N) F) : Prop :=
  ∀ a : MvPolynomial (Fin D × Fin N) F, rename (Prod.map Fin.castSucc id) a ∣ G → IsUnit a

def IsCh {F : Type} [Field F] {D N : ℕ} {O : Type} [CommRing O] [Algebra (GenK F D N) O] [Module.Finite (GenK F D N) O]
    (r : Fin N → O) (G : MvPolynomial (Fin (D + 1) × Fin N) F) : Prop :=
  (∃ c : GenK F D N, c ≠ 0 ∧ spec (gen F D N) G = C c * normForm (GenK F D N) r) ∧ Primitive G

structure IsSection {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ} (I : Ideal (MvPolynomial (Fin N) F))
    (s : Fin D → Fin N → K) {O : Type} [CommRing O] [Algebra K O] (r : Fin N → O) (e : ℕ) : Prop where
  ne : ∀ τ : O →ₐ[K] AlgebraicClosure K, (fun j => τ (r j)) ≠ 0
  on : ∀ τ : O →ₐ[K] AlgebraicClosure K, ∀ g ∈ I, aeval (fun j => τ (r j)) g = 0
  cut : ∀ i, ∑ j, s i j • r j = 0
  count : ∀ y : Fin N → AlgebraicClosure K, y ≠ 0 → (∀ g ∈ I, aeval y g = 0) →
    (∀ i, ∑ j, algebraMap K _ (s i j) * y j = 0) →
    Nat.card {τ : O →ₐ[K] AlgebraicClosure K // ∃ c : AlgebraicClosure K, (fun j => τ (r j)) = c • y} = e

def ChowPower : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F))
    (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f →
    ∀ (O : Type) [CommRing O] [Algebra (GenK F D N) O] [Module.Finite (GenK F D N) O] [Algebra.Etale (GenK F D N) O]
      (r : Fin N → O) (e : ℕ), 1 ≤ e → IsSection I (gen F D N) r e →
      Module.finrank (GenK F D N) O = e * d ∧ IsCh r (f ^ e) ∧
        ∀ G, IsCh r G → (∃ c : F, c ≠ 0 ∧ G = C c * f ^ e) ∧ IsMultiHomogeneous (fun _ => Module.finrank (GenK F D N) O) G

def HeightTie : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F) (Λ : ℝ), Lat T.w T.A Λ → ∀ h, T.IsHeight h →
    ∀ (d e : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (c : F), IsChowForm T.imageIdeal T.D d f → 1 ≤ e → c ≠ 0 →
      ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) = h - (harmonic (T.N - 1) : ℝ) / 2 ∧
      h - (Real.log T.n + 1) / 2 ≤ ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ))

structure SimpleAt {F : Type} [Field F] [NumberField F] (T : Tuple F) (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop where
  good : T.IsGoodSection E s
  card : (T.geomPts E (T.linSection E s)).ncard = δ
  inj : (T.toLinSys.baseChange E).InjOnPts (T.geomPts E (T.linSection E s))
  fac : ∃ c : AlgebraicClosure E, c ≠ 0 ∧ spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f =
    C c * ∏ᶠ x ∈ T.geomPts E (T.linSection E s), lin (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1)

def Bertini : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f →
      (δ : ℤ) = T.del ∧ ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧
        ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E),
          aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 → SimpleAt T δ f E s

def BertiniNF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f →
      (δ : ℤ) = T.del ∧ ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E),
          aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 → SimpleAt T δ f E s

section Words

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

def word {t : ℕ} (u : Fin t → Fin N → K) : Module.End K A := (List.ofFn fun i => mul (u i)).prod

def pw {D : ℕ} (s : Fin D → Fin N → K) (α : Fin D →₀ ℕ) : Module.End K A := (List.ofFn fun i => mul (s i) ^ α i).prod

def coordP {B t : ℕ} (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) : MvPolynomial (Fin B × Fin N) K :=
  ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) m)) * ∏ i, X (β i, e i)

end Words

structure Sys (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] where

  N : ℕ

  n : ℕ

  D : ℕ

  T : ℕ

  w : Matrix (Fin N) (Fin n) F

  fr : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  mul : (Fin N → F) →ₗ[F] Module.End F A

  V : ℕ → Submodule F A

  M : ∀ j, Submodule (𝓞 F) (V j)

  nm : ∀ j, HermFam F (V j)

  beta : ℝ

  abelian₂ : ℝ

  Lam0 : ℝ

  LamD : ℝ

  LamT : ℝ

def ClaimS (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h d deg : ℝ) : Prop :=
  0 ≤ 1 - ((T - 1).choose D : ℝ) * δ / d ∧ 1 - ((T - 1).choose D : ℝ) * δ / d ≤ 1 ∧
    (1 - (1 - ((T - 1).choose D : ℝ) * δ / d)) * (T * h - D * (D + 1) * cst n Λ - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((T - 1).choose D : ℝ) * δ / d) * (T * cst n Λ + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ deg / d

namespace Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]
  (S : Sys F A)

def Short (j : ℕ) (Λ : ℝ) : Prop :=
  ∃ (r : ℕ) (b : Module.Basis (Fin r) F (S.V j)), ∀ i, b i ∈ S.M j ∧ ∀ σ, (S.nm j).nrm σ (b i) ≤ Λ

structure Hyp : Prop where
  one_le : 1 ≤ S.D
  le_T : S.D + 1 ≤ S.T
  lat : Lat S.w S.fr S.abelian₂
  comm : ∀ u v, S.mul u * S.mul v = S.mul v * S.mul u
  full : ∀ j ≤ S.T, IsFull (S.M j)
  stable : ∀ j < S.T, ∀ k, ∀ f ∈ S.M j, ∃ g ∈ S.M (j + 1), (g : A) = S.mul (S.w.col k) f
  bound : ∀ σ, ∀ j < S.T, ∀ (u : Fin S.N → ℂ) (m : ℕ) (c : Fin m → ℂ) (f : Fin m → S.V j) (g : Fin S.N × Fin m → S.V (j + 1)),
    (∀ k i, (g (k, i) : A) = S.mul (Pi.single k 1) (f i)) →
      cnrm (S.nm (j + 1)) σ (fun t => u t.1 * c t.2) g ≤ Real.sqrt S.beta * frameNorm (S.fr σ) u * cnrm (S.nm j) σ c f
  one_le_beta : 1 ≤ S.beta
  hermSysHyp_one_le_lambdaZero : 1 ≤ S.Lam0
  one_le_LamD : 1 ≤ S.LamD
  one_le_LamT : 1 ≤ S.LamT
  short0 : S.Short 0 S.Lam0
  shortD : S.Short S.D S.LamD
  shortT : S.Short S.T S.LamT

structure Col where

  j : ℕ

  t : ℕ
  add : j + t = S.T

  β : Fin t → Fin (S.D + 1)

  x : S.V j

def IsCo {d : ℕ} (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F) : Prop := ∀ i (x : S.V S.T), c i x = b.repr x i

def det {d : ℕ} (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col) : MvPolynomial (Fin (S.D + 1) × Fin S.N) F :=
  (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)).det

def Col.HasType {S : Sys F A} (κ : S.Col) (α : Fin S.D →₀ ℕ) : Prop :=
  ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α i

structure Flat (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) where

  ι : A →ₛₗ[algebraMap F E] A'
  indep : ∀ (m : ℕ) (v : Fin m → S.V S.T), LinearIndependent F v → LinearIndependent E fun i => ι (v i)

  mul : (Fin S.N → E) →ₗ[E] Module.End E A'
  comm : ∀ u v, mul u * mul v = mul v * mul u
  mul_ι : ∀ u x, mul (fun k => algebraMap F E (u k)) (ι x) = ι (S.mul u x)

  y : Fin δ → Fin S.N → E
  y_ne : ∀ p, y p ≠ 0

  res : A' →ₗ[E] (Fin δ → E)
  onto : (Submodule.span E (ι '' S.V 0)).map res = ⊤

  U : ℕ → Submodule E A'

  sym : ∀ a, U a →ₗ[E] (MonoDeg (Fin S.D) a × Fin δ → E)
  le : ∀ a < S.T - S.D, U (a + 1) ≤ U a
  ker : ∀ a < S.T - S.D, ∀ x : U a, sym a x = 0 ↔ x.1 ∈ U (a + 1)
  mono : ∀ a < S.T - S.D, ∀ (α : MonoDeg (Fin S.D) a) (l : Fin (S.T - a) → Fin S.N → E), ∀ m ∈ Submodule.span E (ι '' S.V 0),
    ∃ h : pw mul s α.1 (word mul l m) ∈ U a, ∀ α' p,
      sym a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * y p k) * res m p else 0
  div : U (S.T - S.D) = ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (Submodule.span E (ι '' S.V S.D)).map (pw mul s α.1)

def FlatAt (δ : ℕ) (f : MvPolynomial (Fin (S.D + 1) × Fin S.N) F) (s : Fin S.D → Fin S.N → F) : Prop :=
  ∃ (E A' : Type) (_ : Field E) (_ : Algebra F E) (_ : AddCommGroup A') (_ : Module E A')
    (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (c : E), c ≠ 0 ∧
      spec (fun i k => algebraMap F E (s i k)) f = C c * ∏ p, lin (Φ.y p)

structure Shape {d : ℕ} (δ : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0)
    (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d) : Prop where
  x_j : ∀ q, (col (ix q)).j = 0
  x_vec : ∀ q, ((col (ix q)).x : A) = m q.2
  x_type : ∀ q, (col (ix q)).HasType q.1.2.1
  rest : ∀ k, k ∉ Set.range ix → ((col k).j = S.D ∧ ∀ q, (col k).β q ≠ Fin.last S.D) ∨ (col k).j = S.T

def ShortCols {d : ℕ} (col : Fin d → S.Col) : Prop :=
  ∀ k, (col k).x ∈ S.M (col k).j ∧ ∀ σ, (S.nm (col k).j).nrm σ (col k).x ≤
    if (col k).j = 0 then S.Lam0 else if (col k).j = S.D then S.LamD else S.LamT

def deepRank (s : Fin S.D → Fin S.N → F) : ℕ :=
  Module.finrank F (⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) : Submodule F A)

def expo : ℕ := ∑ a ∈ Finset.range (S.T - S.D), (a + S.D - 1).choose (S.D - 1) * (S.T - a)

end Sys

def SlopeBound : Prop :=
  ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]
    (S : Sys F A), S.Hyp → ∀ (δ : ℕ) (f : MvPolynomial (Fin (S.D + 1) × Fin S.N) F) (Q : MvPolynomial (Fin S.D × Fin S.N) F),
      1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible f → Q ≠ 0 →
      (∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.FlatAt δ f s) →
      0 < Module.finrank F (S.V S.T) ∧
        ClaimS S.T S.D S.n S.abelian₂ S.beta S.Lam0 S.LamD S.LamT δ (ht S.w S.fr f / (((S.D : ℝ) + 1) * δ))
          (Module.finrank F (S.V S.T)) (deg (S.nm S.T) (S.M S.T))

structure GeoHyp {F : Type} [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) : Prop where
  totallyComplex : IsTotallyComplex F
  bir : X.Birational
  nef : IsNef F X.LA
  big : IsBig F X.LA
  nef₂ : IsNef F X.L₂
  big₂ : IsBig F X.L₂
  mulStable : X.MulStable
  mulBound : X.MulBound fun _ => X.beta
  normsLe : X.NormsLe
  one_le_Lam : 1 ≤ X.abelian₂
  hermSysHyp_one_le_lambdaZero : 1 ≤ Λ₀
  short0 : X.ShortFamily 0 Λ₀
  shortD : X.ShortFamily X.D X.LamD
  shortT : X.ShortFamily X.T X.LamT

def GeoBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ h, X.IsHeight h →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 X.T X.D X.n 1 X.abelian₂ X.beta X.LamD X.LamT (Real.log Λ₀) X.del h X.d (X.degM X.T)

example {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)
    (u : Fin 0 → Fin N → K) : word mul u = 1 := by simp [word]

end GlobalTheory.HSShort
