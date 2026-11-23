import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NumberField.AdeleRing TensorProduct

namespace PositivityTheory.Rg.Tf.Geo

def N0 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ a, galAd σ (adeleMap F E a) = adeleMap F E a) ∧ (∀ x : E, galAd σ (algebraMap E 𝔸[E] x) = algebraMap E 𝔸[E] (σ x)) ∧
    (∀ y, (galAd σ)^[Module.finrank F E] y = y) ∧ Continuous (galAd σ) ∧ (∀ y, (galAd σ y).1 = galInf σ y.1) ∧
    (∀ a, galInf σ (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) a) = GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) a) ∧ Continuous (galInf σ) ∧
    Topology.IsClosedEmbedding (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (∀ y, atFin v (galAd σ y) = galFin σ v (atFin v y)) ∧
      (∀ a : 𝔸[F], atFin v (adeleMap F E a) = incFin E v (a.2 v)) ∧ (∀ a, galFin σ v (incFin E v a) = incFin E v a) ∧
      Continuous (galFin σ v) ∧ Topology.IsClosedEmbedding (incFin E v)

def N6 : Prop := ∀ (k R : Type) [Field k] [CharZero k] [CommRing R] [Algebra k R] (n : ℕ) (γ : Matrix (Fin n) (Fin n) k),
    γ.charpoly.Separable → ∀ x : Matrix (Fin n) (Fin n) R, x * γ.map (algebraMap k R) = γ.map (algebraMap k R) * x →
      ∃ p : R[X], x = aeval (γ.map (algebraMap k R)) p

def Q4 : Prop := ∀ (X T X' T' : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] [Group X'] [TopologicalSpace X'] [IsTopologicalGroup X'] [LocallyCompactSpace X'] [T2Space X']
    [SecondCountableTopology X'] [MeasurableSpace X'] [BorelSpace X'] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T']
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] [ν.IsMulRightInvariant]
    (e : X ≃ₜ* X') (e' : T ≃ₜ* T') (i : T →* X) (i' : T' →* X'), Topology.IsClosedEmbedding i → (∀ t, i' (e' t) = e (i t)) →
    ∀ (a b : NNReal), a ≠ 0 → b ≠ 0 → ∀ Φ : X' → ℂ, Continuous Φ → (∀ t x, Φ (i' t * x) = Φ x) →
      (∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i' t * y) →
      quotInt (a • μ.map e) id i' (b • ν.map e') Φ = ((a : ℝ) / (b : ℝ) : ℝ) * quotInt μ id i ν (Φ ∘ e)

def Q5 : Prop := ∀ (X T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] [ν.IsMulRightInvariant] (i : T →* X), Topology.IsClosedEmbedding i → ∀ K : Subgroup X,
    IsOpen (K : Set X) → IsCompact (K : Set X) →
      quotInt μ id i ν (Set.indicator {x | ∃ t, ∃ y ∈ K, x = i t * y} 1) = ((μ.real K / ν.real (K.comap i) : ℝ) : ℂ)

def HtC : Prop := (∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Y : ℝ),
      IsCompact {g : G1 E n | AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) ≤ Y}) ∧
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ f : CC E n, Ell σ f →
      Integrable (twKQ θ f) (quotientMeasure (Gam E n) μ))

def TensorsOverNumberField : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (fi : GL (Fin n) (InfiniteAdeleRing F) → ℂ) (f : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F) → ℂ),
    Continuous fi → HasCompactSupport fi → (∀ v, Continuous (f v) ∧ HasCompactSupport (f v)) →
    (∀ v ∉ S, f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1) →
    Continuous (tensF fi f) ∧ HasCompactSupport (tensF fi f)

def SelmerRankBoundLaurent : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : GL (Fin n) (v.adicCompletion F),
      x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ GLnLocal.integralGL (v.adicCompletion F) n ↔
      ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
        ∃ y ∈ GLnLocal.integralGL (v.adicCompletion F) n, x = t * y

def G6 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), 0 < n →
    ∃ (C : ℝ) (c : ℕ), ∀ (q : HeightOneSpectrum (𝓞 F)) (Φ : AdelicGLn.AdelicGL E n → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ g, Φ g ≠ 0 → heightOff q g ≤ Y ∧ ∀ w : PlacesOver E q,
        ‖((finAt w.1 g : GL (Fin n) (w.1.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1) →
      ∀ g : G1 E n, avg Φ g ≠ 0 → heightOff q (g : AdelicGLn.AdelicGL E n) ≤ C * Y ^ c ∧
        ∃ g', Φ g' ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), finAt w (g : AdelicGLn.AdelicGL E n) = finAt w g'

end PositivityTheory.Rg.Tf.Geo
