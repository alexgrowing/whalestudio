import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc Matrix MeasureTheory
open scoped Classical

namespace GlobalTheory.SgGlob

section Rat
variable {E : Type} [Field E] [NumberField E]

def IntUp {r : ℕ} (u : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  GlobalTheory.SgAlg.IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)

def Tied (σ : E →+* E) (g : ℕ) {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IntUp u ∧ IntUp u' ∧
    (∀ a b : Fin (r + 1), a < b → (g : E)⁻¹ * (u a b - u' a b) ∈ dInv E ((b : ℕ) - a)) ∧
    Z' = GlobalTheory.SgAlg.cT σ u * Z * u'

def eps (K : Type) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun b => (-1) ^ (r - (b : ℕ))

def AtPt {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ x : Matrix (Fin (r + 1)) (Fin (r + 1)) E × Matrix (Fin (r + 1)) (Fin (r + 1)) E,
    GlobalTheory.SgAlg.IsLo x.1 ∧ GlobalTheory.SgAlg.IsUp x.2 ∧ Z * eps E r = x.1 * w.mat * x.2

def phaseZ (g : ℕ) {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℂ :=
  if h : AtPt w Z then psiInf (-((g : E)⁻¹ * (simpleLow h.choose.1 + simpleUp h.choose.2))) else 0

def ClsAt (σ : E →+* E) (g : ℕ) {r : ℕ} (w : Pt E (r + 1)) : Type :=
  Quot fun Z Z' : {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E // AtPt w Z} => Tied σ g Z.1 Z'.1

def Xs {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (GlobalTheory.SgAlg.eOf P).mulVecLin

def W0 (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Set (Fin n → E) :=
  {v | (GlobalTheory.SgAlg.cT σ P * J) *ᵥ v = 0 ∧ (GlobalTheory.SgAlg.cT σ P' * J) *ᵥ v = 0}

def nrm (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Fin n → E := P' *ᵥ fun b => (GlobalTheory.SgAlg.pairM σ J P' P)⁻¹ b (Fin.last r)

def ScalarPair (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P₁ P₂ : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  (GlobalTheory.SgAlg.pairM σ J P₁ P)⁻¹ (Fin.last r) (Fin.last r) = (GlobalTheory.SgAlg.pairM σ J P₂ P)⁻¹ (Fin.last r) (Fin.last r) ∧
  nrm σ J P P₁ - nrm σ J P P₂ ∈ Xs P ∧
  ∃ δ : Matrix (Fin n) (Fin n) E, GlobalTheory.SgAlg.IsUn σ J δ ∧ latMap δ Λ = Λ ∧ δ * P₁ = P₂ ∧
    (∀ v ∈ Λ, (GlobalTheory.SgAlg.cT σ (GlobalTheory.SgAlg.eOf P₁) * J) *ᵥ v = 0 →
      ∃ x ∈ Λ, x ∈ Xs P ∧ (g : E)⁻¹ • (δ *ᵥ v - v - x) ∈ Λ) ∧
    (∀ v₁ ∈ W0 σ J P P₁, ∃ v₂ ∈ W0 σ J P P₂, v₁ - v₂ ∈ Xs P ∧ δ *ᵥ v₁ - v₂ ∈ Xs P₂) ∧
    δ *ᵥ nrm σ J P₁ P - nrm σ J P₂ P ∈ Xs P₂

def nPartners (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ) (x : Tri E n r)
    (Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℕ∞ :=
  ENat.card (Quot fun P₂ P₃ : {P₂ : Matrix (Fin n) (Fin (r + 1)) E //
      (x.1, x.2.1, P₂) ∈ GenConf σ J T T' g Z₂ ∧ ScalarPair σ J g x.1 x.2.1 x.2.2 P₂} =>
    ∃ ν, GlobalTheory.SgAlg.InN σ J x.2.1 ν ∧ ν * x.2.1 = x.2.1 ∧ latMap ν x.1 = x.1 ∧ ν * P₂.1 = P₃.1)

def pairMass (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ENNReal :=
  ∑' c : Quot (fun x y : GenConf σ J T T' g Z₁ => ∃ γ, IsoTri σ J γ x.1 y.1),
    (ENat.toENNReal (ENat.card {γ // IsoTri σ J γ (Quot.out c).1 (Quot.out c).1}))⁻¹ *
      ENat.toENNReal (nPartners σ J T T' g (Quot.out c).1 Z₂)
end Rat

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

def Zloc {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  Matrix.of fun a b => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ (-(2 * (r : ℤ) - a - b))) * (X.A p).ιE (Z a b)

def Zmod {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  GlobalTheory.SgDen.zz (X.M p) (X.Zloc p Z) * eps (X.A p).Ep r

def tau (p : HeightOneSpectrum (𝓞 F)) (T T' : F) : (X.A p).Ep :=
  tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')

def Zplus {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  X.Zmod p Z - Matrix.single (Fin.last r) (Fin.last r) (X.tau p T T')

def wtLoc {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (w : Pt E (r + 1))
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  (GlobalTheory.SgLoc.orbMeas (X.M p) (X.ptMod r p w) {xy | ∃ l u, GlobalTheory.SgAlg.IsLo l ∧ GlobalTheory.SgAlg.IsUp u ∧
    GlobalTheory.SgDen.IntR (X.M p) l ∧ GlobalTheory.SgDen.IntR (X.M p) u ∧
    GlobalTheory.SgLoc.orbMat (X.ptMod r p w) xy = l * X.Zmod p Z * u}).toReal

def wt {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ := ∏ᶠ p, X.wtLoc p w Z

def gramPlus {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (X.A p).Ep :=
  let l : (X.A p).Ep := GlobalTheory.SgDen.levInv (X.M p)
  let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (X.A p).Ep :=
    Matrix.fromBlocks 1 (if (X.M p).split.isSome then (-l) • 1 else 0) 0 (l • 1)
  GlobalTheory.SgDen.ct (X.M p).L A *
    Matrix.fromBlocks (GlobalTheory.SgAlg.TF r ((X.A p).ιE (algebraMap F E T))) (X.Zloc p Z)
      (GlobalTheory.SgDen.ct (X.M p).L (X.Zloc p Z)) (GlobalTheory.SgAlg.TF r ((X.A p).ιE (algebraMap F E T'))) * A

def densLoc (n : ℕ) {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F))
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  GlobalTheory.SgDen.densF (GlobalTheory.SgDen.resQ (X.A p).Fp) (GlobalTheory.SgDen.eta (X.A p).Ep) n (2 * r + 2)
    (GlobalTheory.SgDen.corank (X.M p).L (X.gramPlus T T' p Z))

def dens (n : ℕ) {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  ∏' p, X.densLoc n T T' p Z

def admitted {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∀ p, GlobalTheory.SgDen.IntR (X.M p) (X.Zplus T T' p Z)

def KtopZ (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  if ∃ p, KtopLoc (X.M p) (X.tau p T T') (X.ptMod r p w) (X.ptMod r p w') = 0 then 0
  else ∏ᶠ p, KtopLoc (X.M p) (X.tau p T T') (X.ptMod r p w) (X.ptMod r p w')

def KAtopZ (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  X.KtopZ r T T' w w' / ((X.phi r w * X.phi r w' : ℝ) : ℂ)

def KgsM {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  ∑' c : ClsAt (sig : E →+* E) (g₁ * g₂) w × ClsAt (sig : E →+* E) (g₁ * g₂) w',
    ((X.wt w (Quot.out c.1).1 * X.wt w' (Quot.out c.2).1 *
      (pairMass (sig : E →+* E) J (algebraMap F E T) (algebraMap F E T') (g₁ * g₂)
        (Quot.out c.1).1 (Quot.out c.2).1).toReal : ℝ) : ℂ) *
      phaseZ (g₁ * g₂) w (Quot.out c.1).1 * conj (phaseZ (g₁ * g₂) w' (Quot.out c.2).1)

def IsMassConst (k r : ℕ) (J : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E) (T T' : F) (c : ℝ) : Prop :=
  ∀ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E, TotPos (GZ sig T T' Z) → X.admitted T T' Z →
    Mass (sig : E →+* E) J (algebraMap F E T) (algebraMap F E T') (g₁ * g₂) Z =
      ENNReal.ofReal (c * normInf (GZ sig T T' Z) ^ (k - 1) * X.dens (k + 2 * r + 1) T T' Z)

end ModFam

def SpaceOK {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n : ℕ} (r : ℕ) (J : Matrix (Fin n) (Fin n) E) : Prop :=
  GlobalTheory.SgAlg.IsHermU σ J ∧ (∃ Λ, SelfDual σ J Λ) ∧
    ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin n) (Fin n) ℂ, IsUnit A.det ∧
      J.map τ = Aᴴ * Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r + 1 then (-1 : ℂ) else 1) * A

end GlobalTheory.SgGlob
