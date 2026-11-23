import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

def QMap : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (G' : Type) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [T2Space G']
  [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (e : G ≃ₜ* G') (μ : Measure G) [μ.IsHaarMeasure] (μ' : Measure G') [μ'.IsHaarMeasure]
  (T : Subgroup G) (T' : Subgroup G') (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (ν' : Measure T') [ν'.IsHaarMeasure]
  [ν'.IsInvInvariant] (F : G → ℂ), IsClosed (T : Set G) → T.map e.toMonoidHom = T' → Measurable F → (∀ t ∈ T, ∀ x, F (t * x) = F x) →
  quotIntegral μ' T' ν' (fun x => F (e.symm x)) = 0 → quotIntegral μ T ν F = 0

def QInt : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (C : Set G), IsClosed (T : Set G) → IsCompact C →
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (F : G → ℂ) (B : ℝ), 0 ≤ B → Measurable F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ x, F x ≠ 0 → x ∈ (T : Set G) * C) →
    (∀ x ∈ C, ‖F x‖ ≤ B) → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ ∧ ‖quotIntegral μ T ν F‖ ≤ A * B

def QAdd : Prop := ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (T : Subgroup G) (ν : Measure T),
  (∀ (ι : Type) (s : Finset ι) (F : ι → G → ℂ), (∀ i ∈ s, Measurable (F i) ∧ quotLIntegral μ T ν (fun x => ‖F i x‖ₑ) ≠ ⊤) →
    quotIntegral μ T ν (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, quotIntegral μ T ν (F i)) ∧
  (∀ F F' : G → ℂ, Measurable F → Measurable F' → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ →
    quotLIntegral μ T ν (fun x => ‖F' x‖ₑ) ≠ ⊤ → quotIntegral μ T ν (fun x => F x - F' x) = quotIntegral μ T ν F - quotIntegral μ T ν F') ∧
  ∀ (c : ℂ) (F : G → ℂ), quotIntegral μ T ν (fun x => c * F x) = c * quotIntegral μ T ν F

def QProd : Prop := ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  (G₂ : Type) [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂]
  [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
  (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) (ν : Measure (T₁.prod T₂)) [ν.IsHaarMeasure] [ν.IsInvInvariant] (F : G₁ × G₂ → ℂ),
  IsClosed (T₁ : Set G₁) → IsClosed (T₂ : Set G₂) → (∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s) → (∀ s ∈ T₂, ∀ t ∈ T₂, s * t = t * s) →
  Measurable F → (∀ t ∈ T₁.prod T₂, ∀ x, F (t * x) = F x) →
  ((∀ (ν₁ : Measure T₁) [ν₁.IsHaarMeasure] [ν₁.IsInvInvariant] x₂, quotIntegral μ₁ T₁ ν₁ (fun x₁ => F (x₁, x₂)) = 0) ∨
    ∀ (ν₂ : Measure T₂) [ν₂.IsHaarMeasure] [ν₂.IsInvInvariant] x₁, quotIntegral μ₂ T₂ ν₂ (fun x₂ => F (x₁, x₂)) = 0) →
  quotIntegral (μ₁.prod μ₂) (T₁.prod T₂) ν F = 0

structure VP {m : ℕ} (V : ((Fin m → SignType) → ℝ) → ℂ) : Prop where
  meas : Measurable V
  bdd : ∀ M : ℝ, ∃ B : ℝ, ∀ y, (∀ e, |y e| ≤ M) → ‖V y‖ ≤ B
  diff : ∀ (y y' : (Fin m → SignType) → ℝ) e s t, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') →
    V (Function.update y e s) - V (Function.update y e t) = V (Function.update y' e s) - V (Function.update y' e t)

def Vfun : Prop := ∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [ν.IsHaarMeasure]
  (Γ : Subgroup T) (m : ℕ) (a : T → Fin m → ℝ), (∀ s t : T, s * t = t * s) → DiscreteTopology Γ → Continuous a →
  (∀ s t, a (s * t) = a s + a t) → (∀ t ∈ Γ, a t = 0) → (∀ M : ℝ, ∃ C : Set T, IsCompact C ∧ ∀ t, (∀ i, |a t i| ≤ M) → t ∈ (Γ : Set T) * C) →
  VP (fun y => quotIntegral ν Γ Measure.count fun t => (gam y (a t) : ℂ)) ∧
    ∀ (y : (Fin m → SignType) → ℝ) (s : T), quotIntegral ν Γ Measure.count (fun t => (gam (fun e => y e - sdot e (a s)) (a t) : ℂ)) =
      quotIntegral ν Γ Measure.count fun t => (gam y (a t) : ℂ)

abbrev thC (n : ℕ) : Monoid.End (GL (Fin n) ℂ) := thetaR (starRingEnd ℂ) n

def IsFlag {n : ℕ} (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : Prop :=
  W₁ ≠ ⊥ ∧ W₁ ≤ W₂ ∧ perpD (starRingEnd ℂ) d W₁ = W₂ ∧ perpD (starRingEnd ℂ) d W₂ = W₁

structure LocFam {n m : ℕ} (d : GL (Fin n) ℂ) (V : ((Fin m → SignType) → ℝ) → ℂ) (p : GL (Fin n) ℂ → (Fin m → SignType) → ℝ) : Prop where
  cont : Continuous p
  zero : ∀ x, p x 0 = 0
  cpt : ∀ x k, thC n k = k → p (x * k) = p x
  tor : ∀ t ∈ twCent (thC n) d, ∀ x z, V (p (t * x) + z) = V (p x + z)
  nil : ∀ e, e ≠ 0 → ∃ W₁ W₂, IsFlag d W₁ W₂ ∧ ∀ u : GL (Fin n) ℂ, u.val - 1 ∈ nilrad W₁ W₂ → ∀ x e', SLe e e' ∨ SLe e' e → p (u * x) e' = p x e'

def LocTor : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ), (d * thC n d).val.charpoly.Separable →
  IsClosed (twCent (thC n) d : Set (GL (Fin n) ℂ)) ∧ (∀ s ∈ twCent (thC n) d, ∀ t ∈ twCent (thC n) d, s * t = t * s) ∧
    Continuous (thC n) ∧ LocallyCompactSpace (GL (Fin n) ℂ) ∧ SecondCountableTopology (GL (Fin n) ℂ)

def OneVanish : Prop := ∀ (n m : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (μ : Measure (GL (Fin n) ℂ))
  [μ.IsHaarMeasure] (d : GL (Fin n) ℂ) (ν : Measure (twCent (thC n) d)) [ν.IsHaarMeasure] [ν.IsInvInvariant] (f : GL (Fin n) ℂ → ℂ)
  (V : ((Fin m → SignType) → ℝ) → ℂ) (p : GL (Fin n) ℂ → (Fin m → SignType) → ℝ) (z : (Fin m → SignType) → ℝ),
  (d * thC n d).val.charpoly.Separable → Continuous f → HasCompactSupport f → VeryCusp f → VP V → LocFam d V p → z 0 = 0 →
  quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + z) - V (p x))) = 0

def TwoVanish : Prop := ∀ (n m : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (μ : Measure (GL (Fin n) ℂ))
  [μ.IsHaarMeasure] (d₁ d₂ : GL (Fin n) ℂ) (ν : Measure ((twCent (thC n) d₁).prod (twCent (thC n) d₂))) [ν.IsHaarMeasure] [ν.IsInvInvariant]
  (f : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ) (V : ((Fin m → SignType) → ℝ) → ℂ) (p₁ p₂ : GL (Fin n) ℂ → (Fin m → SignType) → ℝ)
  (z : (Fin m → SignType) → ℝ), m ≠ 0 → (d₁ * thC n d₁).val.charpoly.Separable → (d₂ * thC n d₂).val.charpoly.Separable →
  Continuous f → HasCompactSupport f → (∀ g, VeryCusp fun x => f (x, g)) → (∀ g, VeryCusp fun x => f (g, x)) → VP V →
  LocFam d₁ V p₁ → LocFam d₂ V p₂ → z 0 = 0 →
  quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z)) = 0

def ploc {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℂ) (g : GL (Fin n) ℂ) : ℝ :=
  Real.log ((((g⁻¹ : GL (Fin n) ℂ).val * M)ᴴ * ((g⁻¹ : GL (Fin n) ℂ).val * M)).det).re

def pAt {E : Type} [Field E] [NumberField E] {n m : ℕ} (Wof : (Fin m → SignType) → Submodule E (Fin n → E)) (v : InfinitePlace E)
    (g : GL (Fin n) ℂ) (e : Fin m → SignType) : ℝ := ploc ((basisMat (Wof e)).map v.embedding) g

def Ploc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (v : InfinitePlace E) (W : Submodule E (Fin n → E)),
  (∀ x : GA E n, lognInf v (frame x (basisMat W)) = ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x)) ∧
  Continuous (ploc ((basisMat W).map v.embedding)) ∧
  (∀ x k, thC n k = k → ploc ((basisMat W).map v.embedding) (x * k) = ploc ((basisMat W).map v.embedding) x) ∧
  (W = ⊥ → (∀ x, ploc ((basisMat W).map v.embedding) x = 0) ∧ ∀ x : GA E n, deg x W = 0) ∧
  (∀ g, GeneralLinearGroup.map (cV v) (embInf n v g) = g) ∧
  (∀ v', v' ≠ v → ∀ g, GeneralLinearGroup.map (cV v') (embInf n v g) = 1) ∧
  (∀ d : GL (Fin n) E, GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d) ∧
  ∀ (g : GL (Fin n) ℂ) (x : GA E n), deg (embInf n v g * x) W + ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) =
    deg x W + ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x)

structure Par {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} (d : GL (Fin n) E)
    (Wof : (Fin m → SignType) → Submodule E (Fin n → E)) (a : GA E n → Fin m → ℝ) : Prop where
  reg : IsRegD d
  iso : ∀ e, IsoStab d (Wof e)
  uniq : ∀ W, IsoStab d W → ∃! e, Wof e = W
  zero : Wof 0 = ⊥
  meet : ∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e'
  mono : ∀ e e', SLe e e' → Wof e ≤ Wof e'
  perp : ∀ e, perpD (conjE E) d (perpD (conjE E) d (Wof e)) = Wof e
  comm : ∀ t ∈ adCent d, ∀ t' ∈ adCent d, t * t' = t' * t
  closed : IsClosed (adCent d : Set (GA E n))
  degT : ∀ t ∈ adCent d, ∀ x e, deg (t * x) (Wof e) = deg x (Wof e) + sdot e (a t)

def yOf {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} (τ : ℝ) (Wof : (Fin m → SignType) → Submodule E (Fin n → E))
    (x : GA E n) (e : Fin m → SignType) : ℝ := prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)

def FamAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n m : ℕ) (d : GL (Fin n) E)
  (Wof : (Fin m → SignType) → Submodule E (Fin n → E)) (a : GA E n → Fin m → ℝ) (V : ((Fin m → SignType) → ℝ) → ℂ) (v : InfinitePlace E),
  Par d Wof a → (∀ t ∈ adCent d, ∀ y, V (fun e => y e - sdot e (a t)) = V y) →
  (∀ t ∈ twCent (thC n) (locGL v d), embInf n v t ∈ adCent d) →
  (locGL v d * thC n (locGL v d)).val.charpoly.Separable ∧ LocFam (locGL v d) V (pAt Wof v)

def AdTop : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), LocallyCompactSpace (GA E n) ∧ T2Space (GA E n) ∧
  SecondCountableTopology (GA E n) ∧ Continuous (thetaA E n) ∧ (∀ W : Submodule E (Fin n → E), Measurable[borel _] fun x : GA E n => deg x W) ∧
  ∀ d : GL (Fin n) E, IsClosed (ratCent d : Set (GA E n)) ∧ DiscreteTopology (ratCent d) ∧ Countable (ratCent d)

def Glob2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (n m : ℕ)
  [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure] (d : GL (Fin n) E)
  (ν : Measure (adCent d)) [ν.IsHaarMeasure] [ν.IsInvInvariant] (Wof : (Fin m → SignType) → Submodule E (Fin n → E))
  (a : GA E n → Fin m → ℝ) (V : ((Fin m → SignType) → ℝ) → ℂ) (τ : ℝ) (φ : GA E n → ℂ), m ≠ 0 → Par d Wof a → VP V →
  (∀ t ∈ adCent d, ∀ y, V (fun e => y e - sdot e (a t)) = V y) → IsTest φ → (∀ v, VCAt v φ) →
  quotIntegral μ (adCent d) ν (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) = 0

def Glob1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure] (d : GL (Fin n) E)
  (ν : Measure (adCent d)) [ν.IsHaarMeasure] [ν.IsInvInvariant] (φ : GA E n → ℂ), IsRegD d → ¬ IsRegEll d →
  (∀ t ∈ adCent d, ∀ t' ∈ adCent d, t * t' = t' * t) → IsClosed (adCent d : Set (GA E n)) → IsTest φ → (∀ v, VCAt v φ) →
  quotIntegral μ (adCent d) ν (fun x => φ (twConj (thetaA E n) x (ratGL E n d))) = 0

def CutInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
  (μ : Measure (GA E n)) [μ.IsHaarMeasure] (τ : ℝ) (φ : GA E n → ℂ) (d : GL (Fin n) E), IsTest φ →
  Measurable (fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d))) ∧
  (∀ g ∈ ratCent d, ∀ x, chiT τ (g * x) * φ (twConj (thetaA E n) (g * x) (ratGL E n d)) =
    chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d))) ∧
  quotLIntegral μ (ratCent d) Measure.count (fun x => ‖chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d))‖ₑ) ≠ ⊤

end PositivityTheory.Rg.BcB.CV

end
