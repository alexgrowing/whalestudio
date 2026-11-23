import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
import GroundTheory.AutomorphicForms.ReductionMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

def IsWt {G : Type} [Mul G] [MeasurableSpace G] (ν : Measure G) (β : G → ℝ≥0∞) : Prop :=
  Measurable β ∧ ∀ g, ∫⁻ h, β (h * g) ∂ν = 1

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def Dt (g : GA E k) : ℝ := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ)

def UU (j : ℕ) (g : GA E k) : Prop :=
  (∀ i c : Fin k, c < i → g.val i c = 0) ∧ (∀ i, g.val i i = 1) ∧
    ∀ i c : Fin k, (c : ℕ) < j → g.val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c

variable (E k) in

def nuD : ℕ → Measure (GA E k)
  | 0 => Measure.dirac 1
  | d + 1 => Measure.map (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2)
      ((vecMeasure E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)))).prod (nuD d))

def nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) : Measure (GA E k) :=
  Measure.sum fun γ : Γ => Measure.map (fun g => ratGL E k γ * g) (nuD E k d)

variable (E k) in

def nuP (m : ℕ) : Measure (GA E k) := nuG {γ | IsMir m γ} (k - (m + 1))

variable (E k) in

def nuB (j : ℕ) : Measure (GA E k) := nuG {γ | GlobalTheory j γ} (k - j)

variable (E k) in

def RowT (j : ℕ) : Type := {ξ : Fin k → E // ξ ≠ 0 ∧ ∀ i : Fin k, j ≤ (i : ℕ) → ξ i = 0}

def gam {j : ℕ} (ξ : RowT E k j) : GL (Fin k) E :=
  Classical.epsilon fun γ => GlobalTheory j γ ∧ ∀ i c : Fin k, (i : ℕ) + 1 = j → γ.val i c = ξ.1 c

def lastRow (g : GA E k) : Fin k → Ad E := fun c => ∑ i : Fin k, if (i : ℕ) + 1 = k then g.val i c else 0

structure Pre (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E k → ℂ) : Prop where
  cont : Continuous f
  left : ∀ γ : GL (Fin k) E, IsMir m γ → ∀ g, f (ratGL E k γ * g) = f g
  law : ∀ j, m < j → ∀ (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k), f (blkU y * g) = ψ (dot (eLast k j) y) * f g

def RatInv {X : Type} (f : GA E k → X) : Prop := ∀ γ g, f (ratGL E k γ * g) = f g

def invT (g : GA E k) : GA E k :=
  ⟨(g⁻¹.val)ᵀ, (g.val)ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

def ht (g : GA E k) (ξ : Fin k → E) : ℝ := height g ξ / Dt g ^ ((k : ℝ)⁻¹)

def Dec (f : GA E k → ℂ) : Prop := ∀ M : ℕ, ∃ C : ℝ, ∀ g ξ, ξ ≠ 0 → ‖f g‖ ≤ C * ht g ξ ^ M

def dmin (g : GA E k) : ℝ := ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1

def wt (M : ℕ) (g : GA E k) : ℝ := min 1 (dmin g) ^ M

def G0 (S : Finset (Pl E)) : Set (GA E k) := {g | ∀ w, w ∉ S → Iwasawa.iwasawaExponent _ k (cLoc w g) = 0}

def LawOff (S : Finset (Pl E)) (P : GA E k → ℂ) (a : Off E S → (Fin k → ℤ) → ℂ) : Prop :=
  ∀ (w : Off E S) (g : GA E k), cLoc w.1 g = 1 → ∀ n ∈ Iwasawa.unipotent (w.1.adicCompletion E) k,
    ∀ κ ∈ GLnLocal.integralGL (w.1.adicCompletion E) k, ∀ l : Fin k → ℤ,
      P (g * fl k w.1 (n * Iwasawa.torusPow (w.1.adicCompletion E) k l * κ)) = P g * a w l

def SphOff [IsTotallyComplex E] {X : Type} (S : Finset (Pl E)) (P : GA E k → X) : Prop :=
  ∀ g κ : GA E k, cInf κ = 1 → (∀ w ∈ S, cLoc w κ = 1) →
    (∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) → P (g * κ) = P g

def aLoc {S : Finset (Pl E)} {m : ℕ} (α : Off E S → Fin m → ℂˣ) (β : Off E S → Fin k → ℂˣ) (w : Off E S)
    (l : Fin k → ℤ) : ℂ :=
  halfModulus (w.1.adicCompletion E) l ^ 2 * (nq w : ℂ) ^ (-(((m : ℂ) - k) / 2) * ((∑ i, l i : ℤ) : ℂ)) *
    loc (nq w) (α w) (β w) 0 l

def sumF (f : GA E k → ℂ) (g : GA E k) : ℂ := ∑' ξ : RowT E k k, f (ratGL E k (gam ξ) * g)

def PW (ψ : AddChar (Ad E) ℂ) (f φ : GA E k → ℂ) (g : GA E k) : ℂ :=
  whit ψ (k - 1) f g * conj (whit ψ (k - 1) φ g)

variable [IsTotallyComplex E]

structure Dat (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E)) {m : ℕ} (α : Off E S → Fin m → ℂˣ)
    (β : Off E S → Fin k → ℂˣ) (u : ℝ) (f φ : GA E k → ℂ) : Prop where
  pre : Pre ψ (k - 1) f
  supp : ∃ C : Set (Fin k → Ad E), IsCompact C ∧ ∀ g, f g ≠ 0 → lastRow g ∈ C
  sq : ∃ a ε C : ℝ, 0 < ε ∧ ∀ g, ∑' ξ : RowT E k k, ‖f (ratGL E k (gam ξ) * g)‖ₑ ^ 2 ≤
    ENNReal.ofReal (C * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a))
  good : Good ψ (k - 1) φ
  inv : RatInv φ
  dec : Dec φ
  law : LawOff S (PW ψ f φ) (aLoc α β)
  sph : SphOff S (PW ψ f φ)
  one : 0 < (PW ψ f φ 1).re
  pos : ∃ a b : ℝ, 0 < a ∧ ∀ g ∈ G0 S, PW ψ f φ g ≠ 0 →
    a ≤ Dt g ∧ Dt g ≤ b ∧ 0 ≤ (PW ψ f φ g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re

structure Grow (H H₀ : GA E k → ℂ) : Prop where
  meas : Measurable H
  meas₀ : Measurable H₀
  inv : RatInv H
  inv₀ : RatInv H₀
  cen : ∀ t g, H₀ (splitCentre E k t * g) = H₀ g
  bdd : ∃ C : ℝ, ∀ g, ‖H₀ g‖ ≤ C
  big : ∀ M : ℕ, ∃ C : ℝ, ∀ g, 1 ≤ Dt g → ‖H g‖ ≤ C * (Dt g ^ M)⁻¹
  small : ∃ C : ℝ, ∀ g, Dt g < 1 → ‖(Dt g : ℂ) * H g - H₀ g‖ ≤ C * Dt g

variable (E k) in

def band : Set (GA E k) := {g | 1 ≤ Dt g ∧ Dt g < Dt (splitCentre E k 1)}

omit [IsTotallyComplex E] in

def embM {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin k) (Fin k) R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i c => if h : (i : ℕ) < k ∧ (c : ℕ) < k then A ⟨i, h.1⟩ ⟨c, h.2⟩ else (1 : Matrix (Fin m) (Fin m) R) i c

omit [IsTotallyComplex E] in

def IsEmb {R : Type} [CommRing R] {m : ℕ} (ι : GL (Fin k) R →* GL (Fin m) R) : Prop := ∀ g, (ι g).val = embM m g.val

omit [IsTotallyComplex E] in

def pT (ψ : AddChar (Ad E) ℂ) (j : ℕ) : ℕ → (GA E k → ℂ) → GA E k → ℂ
  | 0, f => f
  | d + 1, f => pT ψ j d (colT ψ (j + d) f)

omit [IsTotallyComplex E] in

def psN (ψ : AddChar (Ad E) ℂ) (n : GA E k) : ℂ :=
  ψ (∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1, n.val p.1 p.2)

structure WRep (w : GA E k → ℝ) (ρ : GA E k →* (XB E k →L[ℂ] XB E k)) (J : XB E k →L[ℂ] XB E k) : Prop where
  mul : ∀ x g, J x g = (w g : ℂ) * x g
  inter : ∀ h x, J (ρ h x) = Rt E k h (J x)
  inj : Function.Injective J
  poly : PolyBd (ρ.comp (infGL E k))

def Bump (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E)) (Ω : GA E k → Prop) (C : Set (GA E k)) (W : GA E k → ℂ) : Prop :=
  IsCompact C ∧ (∀ c ∈ C, InS S c) ∧ (∃ t : ℝ, 0 < t ∧ W 1 = t) ∧
    ∀ g, Ω g → W g ≠ 0 → ∃ n, ∃ c ∈ C, ∃ t : ℝ, UU 0 n ∧ InS S n ∧ g = n * c ∧ 0 ≤ t ∧ W g = psN ψ n * t

structure Cut (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E)) (U : Set (GA E k)) (φ : XB E k)
    (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) : Prop where
  nonneg : ∀ y, 0 ≤ η y
  cont : Continuous η
  cpt : HasCompactSupport η
  zero : η 0 = 0
  contV : Continuous fun y => (η y : ℂ) • Rt E k (s y)⁻¹ φ
  one : 0 < η (lastRow (1 : GA E k)) ∧ s (lastRow (1 : GA E k)) = 1
  small : ∃ C, IsCompact C ∧ C ⊆ U ∧ ∀ y, η y ≠ 0 → s y ∈ C ∧ InS S (s y)
  mir : ∀ g, InS S g → η (lastRow g) ≠ 0 → MirS S (g * (s (lastRow g))⁻¹)
  int : ∀ y, η y ≠ 0 → ∀ w, w ∉ S → ∀ i, pLoc E w (pFin E (y i)) ∈ Formalism.UG.Ov E w
  dep : ∀ y y' : Fin k → Ad E, (∀ i, pInf E (y i) = pInf E (y' i)) →
    (∀ w ∈ S, ∀ i, pLoc E w (pFin E (y i)) = pLoc E w (pFin E (y' i))) → s y = s y' ∧
      ((∀ w, w ∉ S → ∀ i, pLoc E w (pFin E (y' i)) ∈ Formalism.UG.Ov E w) → η y ≠ 0 → η y' = η y)
  ft : ∃ Cf : Set (Fin k → Af E), IsCompact Cf ∧ ∀ M : ℕ, ∃ C : ℝ, ∀ (z : Fin k → Ad E) g,
    ‖∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * z i) ∂vecMeasure E (Fin k)‖ ≤
      Cf.indicator (fun _ => C * ((1 + ‖fun i => pInf E (z i)‖) ^ M)⁻¹) fun i => pFin E (z i)

end PositivityTheory.AdelicQuotientData

end
