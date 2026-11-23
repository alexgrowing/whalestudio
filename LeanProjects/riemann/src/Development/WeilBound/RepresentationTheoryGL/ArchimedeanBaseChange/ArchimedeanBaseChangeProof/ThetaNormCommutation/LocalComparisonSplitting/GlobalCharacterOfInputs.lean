import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem phiU_val (a : ℕ) (R : Type) [CommRing R] : (PhiU a R).val = GlobalTheory.Tw.Phi a R := rfl

theorem phiU_inv_val (a : ℕ) (R : Type) [CommRing R] : ((PhiU a R)⁻¹).val = (GlobalTheory.Tw.Phi a R)ᵀ := rfl

theorem thetaGL_eq (a : ℕ) (R : Type) [CommRing R] (c : R →+* R) (g : GL (Fin a) R) :
    thetaGL a c g = PhiU a R * thetaR c a g * (PhiU a R)⁻¹ := Units.ext rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

abbrev Gf (E : Type) [Field E] [NumberField E] (a b : ℕ) : Type := GL (Fin a) (Af E) × GL (Fin b) (Af E)

abbrev Gi (E : Type) [Field E] (a b : ℕ) : Type := InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ

def Kf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  ⨅ w : Pl E, (GlobalTheory.LFun.KGL w n).comap (GeneralLinearGroup.map (pLoc E w))

def thP (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Gf E a b →* Gf E a b := (thF E a).prodMap (thF E b)

def atW (w : Pl E) (y : Gf E a b) : GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w) y.1, GeneralLinearGroup.map (pLoc E w) y.2)

def finFn (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Gf E a b) : ℂ :=
  ∏ᶠ w ∈ S, φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1

def gam (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : Subgroup (Gf E a b) :=
  ((ratF E a).prodMap (ratF E b)).range ⊓ GlobalTheory.BCT.twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂)

def orbFn (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (x : Gf E a b) : ℂ := finFn S φ₁ φ₂ (x⁻¹ * (ratF E a δ₁, ratF E b δ₂) * thP E a b x)

def dcSum {B : Type} [Group B] (Γ K : Subgroup B) (F : B → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set B) (K : Set B),
    (avg fun k : K => F (Quotient.out q * k)) / (Nat.card (Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup B) : ℂ)

def polE (δ : GL (Fin n) E) : E[X] := (δ * thE E n δ).val.charpoly

def comps (x : GA E a × GA E b) : Gi E a b × Gf E a b :=
  (fun v => (GeneralLinearGroup.map (cV v) x.1, GeneralLinearGroup.map (cV v) x.2),
    (GeneralLinearGroup.map (pFin E) x.1, GeneralLinearGroup.map (pFin E) x.2))

def KfOC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  IsOpen (Kf E n : Set (GL (Fin n) (Af E))) ∧ IsCompact (Kf E n : Set (GL (Fin n) (Af E)))

def FinLevel : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E))
  (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∃ U : Subgroup (Gf E a b), IsOpen (U : Set (Gf E a b)) ∧ ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u⁻¹ * y * thP E a b u) = finFn S φ₁ φ₂ y

def FinHalf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
    {q : DoubleCoset.Quotient (gam δ₁ δ₂ : Set (Gf E a b)) (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) |
      ∃ k ∈ (Kf E a).prod (Kf E b), orbFn S φ₁ φ₂ δ₁ δ₂ (Quotient.out q * k) ≠ 0}.Finite ∧
    (∀ x : Gf E a b, Finite (gam δ₁ δ₂ ⊓ ((Kf E a).prod (Kf E b)).map (MulAut.conj x).toMonoidHom : Subgroup (Gf E a b))) ∧
    dcSum (gam δ₁ δ₂) ((Kf E a).prod (Kf E b)) (orbFn S φ₁ φ₂ δ₁ δ₂) =
      mass (thF E a) (ratF E a).range (ratF E a δ₁) * mass (thF E b) (ratF E b).range (ratF E b δ₂) *
        ∏ᶠ w ∈ S, twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)

def QIndep : Prop := ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSingletonClass G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (H : Subgroup G) [Countable H]
  (F : G → ℂ) (ρ : G → ENNReal), Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → IsQuotNormaliser H Measure.count ρ →
    quotIntegral μ H Measure.count F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ

def QConj : Prop := ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSingletonClass G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (H H' : Subgroup G) [Countable H]
  (F : G → ℂ) (g : G), Measurable F → (∀ h ∈ H, ∀ x, F (h * x) = F x) → (∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H) →
    quotIntegral μ H' Measure.count (fun x => F (g * x)) = quotIntegral μ H Measure.count F

def QSplit : Prop := ∀ (G A B : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSingletonClass G] [Group A] [MeasurableSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (α : Measure A) [SFinite α] (β : Measure B) [β.IsHaarMeasure] [SFinite β] (e : G →* A × B), Measurable e →
  μ.map e = α.prod β → ∀ (Γ : Subgroup G) [Countable Γ] (Γ' K U : Subgroup B),
  Γ.map ((MonoidHom.snd A B).comp e) = Γ' → (∀ γ ∈ Γ, (e γ).2 = 1 → γ = 1) →
  IsOpen (K : Set B) → IsCompact (K : Set B) → IsOpen (U : Set B) →
  ∀ (F₁ : A → ℂ) (F₂ : B → ℂ), Measurable F₁ → Integrable F₁ α → (∀ γ ∈ Γ, ∀ x, F₁ ((e γ).1 * x) = F₁ x) →
    (∀ γ ∈ Γ', ∀ y, F₂ (γ * y) = F₂ y) → (∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y) →
    {q : DoubleCoset.Quotient (Γ' : Set B) (K : Set B) | ∃ k ∈ K, F₂ (Quotient.out q * k) ≠ 0}.Finite →
    (∀ x : B, Finite (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup B)) →
    quotIntegral μ Γ Measure.count (fun x => F₁ (e x).1 * F₂ (e x).2) = (β.real K : ℂ) * (∫ x, F₁ x ∂α) * dcSum Γ' K F₂

def HaarSplit : Prop := ∀ (G A B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [T2Space A] [MeasurableSpace A] [BorelSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B] (μ : Measure G) [μ.IsHaarMeasure]
  (α : Measure A) [α.IsHaarMeasure] (e : G ≃ₜ* A × B), ∃ β : Measure B, β.IsHaarMeasure ∧ μ.map e = α.prod β

def Topo : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (LocallyCompactSpace (GA E n) ∧ SecondCountableTopology (GA E n) ∧ T2Space (GA E n)) ∧
  (LocallyCompactSpace (GL (Fin n) (Af E)) ∧ SecondCountableTopology (GL (Fin n) (Af E)) ∧ T2Space (GL (Fin n) (Af E))) ∧
  (LocallyCompactSpace (GL (Fin n) ℂ) ∧ SecondCountableTopology (GL (Fin n) ℂ)) ∧ Countable (GL (Fin n) E) ∧
  Continuous (thF E n) ∧ Continuous (thetaR (starRingEnd ℂ) n)

def CompIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  ∃ e : (GA E a × GA E b) ≃ₜ* (Gi E a b × Gf E a b), ∀ x, e x = comps x

def TranslAd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E), IsTransl u →
  ∀ g : GA E n, thetaGL n (conjAd E) g = ratGL E n u * thetaA E n g * (ratGL E n u)⁻¹

def AdelEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E))
  (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ →
  ∀ (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E) (x : GA E a × GA E b),
    adel S u₁ u₂ ψ φ₁ φ₂ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) =
      (∏ v, ψ v (twConj (thetaR (starRingEnd ℂ) a) ((comps x).1 v).1 (GeneralLinearGroup.map v.embedding d₁),
        twConj (thetaR (starRingEnd ℂ) b) ((comps x).1 v).2 (GeneralLinearGroup.map v.embedding d₂))) *
      orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (comps x).2

def CentEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ → ∀ (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E),
    (∀ y, y ∈ gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) ↔ ∃ γ ∈ (ratCent d₁).prod (ratCent d₂), (comps γ).2 = y) ∧
    ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), ((comps γ).2 = 1 → γ = 1) ∧ ∀ v,
      ((comps γ).1 v).1 ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaR (starRingEnd ℂ) a) (GeneralLinearGroup.map v.embedding d₁) ∧
      ((comps γ).1 v).2 ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaR (starRingEnd ℂ) b) (GeneralLinearGroup.map v.embedding d₂)

def PolEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E), IsTransl u →
  ∀ d : GL (Fin n) E, (IsRegEll d ↔ polE (d * u⁻¹) ∈ Ell E n) ∧ ∀ v : InfinitePlace E,
    (GeneralLinearGroup.map v.embedding d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map v.embedding d)).val.charpoly =
      (polE (d * u⁻¹)).map v.embedding ∧ (IsRegEll d → EllC (GeneralLinearGroup.map v.embedding d))

def ClassBij : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E), IsTransl u →
  ∃ e : TwCl (thE E n) ≃ TwClass E n, ∀ c, ∃ g, c.rep * u = twConj (thetaE E n) g (Quot.out (e c)) ∧
    (IsRegEll (Quot.out (e c)) ↔ IsRegEll (c.rep * u))

def EllDiag : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ), EllC d → ∃ (g d' : GL (Fin n) ℂ) (z : Fin n → ℂ),
  d'.val = diagonal z ∧ (∀ i, ‖z i‖ = 1) ∧ (Function.Injective fun i => z i ^ 2) ∧ d = twConj (thetaR (starRingEnd ℂ) n) g d'

def DiagProper : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ) (z : Fin n → ℂ), d.val = diagonal z → (∀ i, ‖z i‖ = 1) →
  (Function.Injective fun i => z i ^ 2) → ∀ C : Set (GL (Fin n) ℂ), IsCompact C →
    IsCompact {x | twConj (thetaR (starRingEnd ℂ) n) x d ∈ C}

def EllProper : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ), EllC d → ∀ C : Set (GL (Fin n) ℂ), IsCompact C →
  IsCompact {x | twConj (thetaR (starRingEnd ℂ) n) x d ∈ C}

def WeylAt : Prop := ∀ (n : ℕ) (l : DomWeight n) (γ : Fin n → ℂ), (∀ i, γ i ≠ 0) → Function.Injective γ →
  chAt l (diagonal γ).charpoly = PositivityTheory.RgBcC.weylChar l.w γ

def LefOne [MeasurableSpace (GL (Fin n) ℂ)] (ν : Measure (GL (Fin n) ℂ)) (l : DomWeight n) (val : ℂ) (f : GL (Fin n) ℂ → ℂ) :
    Prop :=
  Continuous f ∧ HasCompactSupport f ∧ ∀ (d : GL (Fin n) ℂ) (z : Fin n → ℂ), d.val = diagonal z → (∀ i, ‖z i‖ = 1) →
    (Function.Injective fun i => z i ^ 2) →
    ∫ x, f (PositivityTheory.RgTw.tw x d) ∂ν = val * starRingEnd ℂ (PositivityTheory.RgBcC.weylChar l.w fun i => z i ^ 2)

def LefPair : Prop := ∀ (a b : ℕ) [MeasurableSpace (GL (Fin a) ℂ)] [BorelSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)]
  [BorelSpace (GL (Fin b) ℂ)] (ν₁ : Measure (GL (Fin a) ℂ)) [ν₁.IsHaarMeasure] (ν₂ : Measure (GL (Fin b) ℂ)) [ν₂.IsHaarMeasure]
  (l₁ : DomWeight a) (l₂ : DomWeight b) (v₁ v₂ : ℂ) (f₁ : GL (Fin a) ℂ → ℂ) (f₂ : GL (Fin b) ℂ → ℂ),
    LefOne ν₁ l₁ v₁ f₁ → LefOne ν₂ l₂ v₂ f₂ → LefAt ν₁ ν₂ l₁ l₂ (v₁ * v₂) fun y => f₁ y.1 * f₂ y.2

def Term : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) [MeasurableSpace (GA E a)]
  [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)] [MeasurableSpace (GL (Fin a) ℂ)]
  [BorelSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)] [BorelSpace (GL (Fin b) ℂ)] (μ₁ : Measure (GA E a))
  [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (ν₁ : Measure (GL (Fin a) ℂ)) [ν₁.IsHaarMeasure]
  (ν₂ : Measure (GL (Fin b) ℂ)) [ν₂.IsHaarMeasure], ∃ c : ℂ, c ≠ 0 ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ →
    ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (val : InfinitePlace E → ℂ)
      (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ),
      (∀ v, LefAt ν₁ ν₂ (l₁ v) (l₂ v) (val v) (ψ v)) → IsTestP φ₁ → IsTestP φ₂ →
      ∀ (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E), IsRegEll d₁ → IsRegEll d₂ →
      orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) d₁ d₂ = c * (∏ v, val v) *
        (mass (thF E a) (ratF E a).range (ratF E a (d₁ * u₁⁻¹)) * mass (thF E b) (ratF E b).range (ratF E b (d₂ * u₂⁻¹)) *
          chW l₁ (polE (d₁ * u₁⁻¹)) * chW l₂ (polE (d₂ * u₂⁻¹)) *
          ∏ᶠ w ∈ S, twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w (d₁ * u₁⁻¹), locEl b w (d₂ * u₂⁻¹)) (seen φ₁ φ₂ w))

def OrbInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) [MeasurableSpace (GA E a)]
  [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)] (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure]
  (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (φ : GA E a × GA E b → ℂ) (d₁ g₁ : GL (Fin a) E) (d₂ g₂ : GL (Fin b) E),
    (Continuous fun x : GA E a × GA E b =>
      φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))) →
    orbTerm2 μ₁ μ₂ φ (twConj (thetaE E a) g₁ d₁) (twConj (thetaE E b) g₂ d₂) = orbTerm2 μ₁ μ₂ φ d₁ d₂

def AdelCont : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E))
  (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ →
  ∀ (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ),
    (∀ v, Continuous (ψ v)) → IsTestP φ₁ → IsTestP φ₂ → ∀ (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E),
    Continuous fun x : GA E a × GA E b =>
      adel S u₁ u₂ ψ φ₁ φ₂ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))

def QConjOf : Prop := QIndep → QConj
def QSplitOf : Prop := QIndep → QSplit
def AdelEqOf : Prop := TranslAd → AdelEq
def EllProperOf : Prop := EllDiag → DiagProper → Topo → EllProper
def LefPairOf : Prop := EllDiag → WeylAt → Topo → LefPair
def OrbInvOf : Prop := QConj → Topo → OrbInv
def AdelContOf : Prop := AdelEq → FinLevel → CompIso → Topo → AdelCont
def TermOf : Prop := QSplit → HaarSplit → Topo → CompIso → KfOC → FinLevel → FinHalf → AdelEq → CentEq → PolEq → EllProper → Term
def GlobalCharacterOfInputs : Prop := Term → OrbInv → AdelCont → ClassBij → PolEq → G4

end PositivityTheory.Rg.BcB.G8

end
