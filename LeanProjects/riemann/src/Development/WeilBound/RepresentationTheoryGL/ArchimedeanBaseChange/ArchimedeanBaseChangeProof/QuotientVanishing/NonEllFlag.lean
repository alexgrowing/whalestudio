import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.D4

open PositivityTheory.Rg.BcB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IsoStab (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) : Prop :=
  img (nrm d) W = W ∧ W ≤ perpD (conjE E) d W

def adCent (d : GL (Fin n) E) : Subgroup (GA E n) := twCent (thetaA E n) (ratGL E n d)

def ratIn (d : GL (Fin n) E) : Subgroup (adCent d) := (ratCent d).subgroupOf (adCent d)

def locSub (v : InfinitePlace E) (W : Submodule E (Fin n → E)) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun x : Fin n → E => fun i => v.embedding (x i)) '' W)

def locGL (v : InfinitePlace E) : GL (Fin n) E →* GL (Fin n) ℂ := GeneralLinearGroup.map v.embedding

def PairParam : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E), IsRegD d →
  ∃ (m : ℕ) (Wof : (Fin m → SignType) → Submodule E (Fin n → E)), (∀ e, IsoStab d (Wof e)) ∧
    (∀ W, IsoStab d W → ∃! e, Wof e = W) ∧ Wof 0 = ⊥ ∧ (∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') ∧
    (∀ e e', SLe e e' → Wof e ≤ Wof e') ∧ ∀ e, perpD (conjE E) d (perpD (conjE E) d (Wof e)) = Wof e

def TorusChar : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (m : ℕ)
  (Wof : (Fin m → SignType) → Submodule E (Fin n → E)), (∀ e, IsoStab d (Wof e)) →
  (∀ W, IsoStab d W → ∃! e, Wof e = W) → Wof 0 = ⊥ → (∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') →
  (∀ e e', SLe e e' → Wof e ≤ Wof e') → IsRegD d →
  (∀ t ∈ adCent d, ∀ t' ∈ adCent d, t * t' = t' * t) ∧ ∃ a : GA E n → (Fin m → ℝ), (∀ t ∈ adCent d, ∀ x e, deg (t * x) (Wof e) = deg x (Wof e) + sdot e (a t)) ∧
    (∀ t ∈ adCent d, ∀ t' ∈ adCent d, a (t * t') = a t + a t') ∧ (∀ t ∈ ratCent d, a t = 0) ∧
    ContinuousOn a (adCent d) ∧
    ∀ M : ℝ, ∃ C : Set (GA E n), IsCompact C ∧ ∀ t ∈ adCent d, (∀ i, |a t i| ≤ M) → t ∈ ((ratCent d : Set (GA E n)) * C)

def PosY : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, ∀ (d : GL (Fin n) E) (m : ℕ)
  (Wof : (Fin m → SignType) → Submodule E (Fin n → E)), (∀ e, IsoStab d (Wof e)) → (∀ W, IsoStab d W → ∃! e, Wof e = W) →
  Wof 0 = ⊥ → (∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') → (∀ e e', SLe e e' → Wof e ≤ Wof e') → IsRegD d →
  ∀ (τ : ℝ) (x : GA E n), C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ →
    PosFam fun e => prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)

def ChiGam : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, ∀ (d : GL (Fin n) E) (m : ℕ)
  (Wof : (Fin m → SignType) → Submodule E (Fin n → E)) (a : GA E n → (Fin m → ℝ)), (∀ e, IsoStab d (Wof e)) →
  (∀ W, IsoStab d W → ∃! e, Wof e = W) → Wof 0 = ⊥ → (∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') →
  (∀ e e', SLe e e' → Wof e ≤ Wof e') → IsRegD d →
  (∀ t ∈ adCent d, ∀ x e, deg (t * x) (Wof e) = deg x (Wof e) + sdot e (a t)) →
  ∀ (τ : ℝ) (x : GA E n), C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ → ∀ t ∈ adCent d,
    chiT τ (t * x) = (gam (fun e => prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)) (a t) : ℂ)

def QuotStage : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (T : Subgroup G)
  (μT : Measure T) [μT.IsHaarMeasure] [μT.IsInvInvariant] (Γ₀ : Subgroup T) (F : G → ℂ),
  IsClosed (T : Set G) → DiscreteTopology Γ₀ → Measurable F → (∀ g ∈ Γ₀, ∀ x, F ((g : G) * x) = F x) →
  quotLIntegral μ (Γ₀.map T.subtype) Measure.count (fun x => ‖F x‖ₑ) ≠ ⊤ →
  quotIntegral μ (Γ₀.map T.subtype) Measure.count F =
    quotIntegral μ T μT fun x => quotIntegral μT Γ₀ Measure.count fun t => F ((t : G) * x)

def QuotProd : Prop := ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
  [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
  (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure] (T₁ : Subgroup G₁) (T₂ : Subgroup G₂)
  (ν₁ : Measure T₁) [SFinite ν₁] [ν₁.IsInvInvariant] (ν₂ : Measure T₂) [SFinite ν₂] [ν₂.IsInvInvariant]
  (ν : Measure (T₁.prod T₂)) [SFinite ν] [ν.IsInvInvariant] (F : G₁ × G₂ → ℂ), Measurable F →
  ν.map (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂)) =
    ν₁.prod ν₂ → (∀ t ∈ T₁.prod T₂, ∀ x, F (t * x) = F x) →
  (∀ x₂, quotIntegral μ₁ T₁ ν₁ (fun x₁ => F (x₁, x₂)) = 0) → quotIntegral (μ₁.prod μ₂) (T₁.prod T₂) ν F = 0

def SplitAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (v : InfinitePlace E)
  [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure],
  ∃ (G' : Type) (_ : Group G') (_ : TopologicalSpace G') (_ : IsTopologicalGroup G') (_ : LocallyCompactSpace G')
    (_ : SecondCountableTopology G') (_ : MeasurableSpace G') (_ : BorelSpace G')
    (_ : MeasurableSpace (GL (Fin n) ℂ)) (_ : BorelSpace (GL (Fin n) ℂ))
    (e : GA E n ≃ₜ* GL (Fin n) ℂ × G') (μ₁ : Measure (GL (Fin n) ℂ)) (μ₂ : Measure G') (θ' : Monoid.End G'),
    μ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ μ.map e = μ₁.prod μ₂ ∧ (∀ g, (e g).1 = GeneralLinearGroup.map (cV v) g) ∧
    (∀ y, e (embInf n v y) = (y, 1)) ∧ (∀ g, e (thetaA E n g) = (thetaR (starRingEnd ℂ) n (e g).1, θ' (e g).2)) ∧
    ∀ d : GL (Fin n) E, (adCent d).map e.toMonoidHom =
      (twCent (thetaR (starRingEnd ℂ) n) (locGL v d)).prod (twCent θ' (e (ratGL E n d)).2)

def LocFlag : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E)
  (W : Submodule E (Fin n → E)) (v : InfinitePlace E), IsoStab d W → W ≠ ⊥ →
  perpD (conjE E) d (perpD (conjE E) d W) = W → locSub v W ≠ ⊥ ∧ locSub v W ≤ locSub v (perpD (conjE E) d W) ∧
    perpD (starRingEnd ℂ) (locGL v d) (locSub v W) = locSub v (perpD (conjE E) d W) ∧
    perpD (starRingEnd ℂ) (locGL v d) (locSub v (perpD (conjE E) d W)) = locSub v W ∧
    ∀ x : GA E n, ∀ y : GL (Fin n) ℂ, y.val - 1 ∈ nilrad (locSub v W) (locSub v (perpD (conjE E) d W)) →
      ∀ W' : Submodule E (Fin n → E), W' ≤ W ∨ (W ≤ W' ∧ W' ≤ perpD (conjE E) d W) →
        lognInf v (frame (embInf n v y * x) (basisMat W')) = lognInf v (frame x (basisMat W'))

def NonEllFlag : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E), IsRegD d →
  ¬ IsRegEll d → ∃ (v : InfinitePlace E) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≠ ⊥ ∧ W₁ ≤ W₂ ∧
    perpD (starRingEnd ℂ) (locGL v d) W₁ = W₂ ∧ perpD (starRingEnd ℂ) (locGL v d) W₂ = W₁

def SplitAt2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (v₁ v₂ : InfinitePlace E), v₁ ≠ v₂ →
  ∀ [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure],
  ∃ (G' : Type) (_ : Group G') (_ : TopologicalSpace G') (_ : IsTopologicalGroup G') (_ : LocallyCompactSpace G')
    (_ : SecondCountableTopology G') (_ : MeasurableSpace G') (_ : BorelSpace G')
    (_ : MeasurableSpace (GL (Fin n) ℂ)) (_ : BorelSpace (GL (Fin n) ℂ))
    (e : GA E n ≃ₜ* (GL (Fin n) ℂ × GL (Fin n) ℂ) × G') (μ₁ : Measure (GL (Fin n) ℂ)) (μ₂ : Measure G')
    (θ' : Monoid.End G'), μ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ μ.map e = (μ₁.prod μ₁).prod μ₂ ∧
    (∀ g, (e g).1 = (GeneralLinearGroup.map (cV v₁) g, GeneralLinearGroup.map (cV v₂) g)) ∧
    (∀ y, e (embInf n v₁ y) = ((y, 1), 1)) ∧ (∀ y, e (embInf n v₂ y) = ((1, y), 1)) ∧
    (∀ g, e (thetaA E n g) = ((thetaR (starRingEnd ℂ) n (e g).1.1, thetaR (starRingEnd ℂ) n (e g).1.2), θ' (e g).2)) ∧
    ∀ d : GL (Fin n) E, (adCent d).map e.toMonoidHom =
      ((twCent (thetaR (starRingEnd ℂ) n) (locGL v₁ d)).prod (twCent (thetaR (starRingEnd ℂ) n) (locGL v₂ d))).prod
        (twCent θ' (e (ratGL E n d)).2)

def LocProper : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ), (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable →
  ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ C' : Set (GL (Fin n) ℂ), IsCompact C' ∧
    {x | twConj (thetaR (starRingEnd ℂ) n) x d ∈ C} ⊆ (twCent (thetaR (starRingEnd ℂ) n) d : Set (GL (Fin n) ℂ)) * C'

def RatDisc : Prop := (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E),
  ratCent d ≤ adCent d ∧ DiscreteTopology (ratIn d) ∧ IsClosed (adCent d : Set (GA E n))) ∧
  ∀ m : ℕ, Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => gam p.1 p.2

end PositivityTheory.Rg.BcB.D4

end
