import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NumberField.AdeleRing TensorProduct

namespace PositivityTheory.Rg.Tf.Geo

def G0 : Prop := (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure], ∃ θ : Twist μ, IsGalTwist σ θ) ∧
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (μ : Measure (G1 F n)) [μ.IsHaarMeasure],
    IsGalTwist (1 : F ≃ₐ[F] F) (Twist.id μ)

def EllipticityFromProductFormula : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∃ (C : ℝ) (c : ℕ),
    ∀ (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q), (∀ w : PlacesOver E q, Function.Surjective (completionMap q w.1)) →
    ∀ ν : Fin n → ℤ, Function.Injective ν → ∑ i, ν i = 0 →
      (∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0) →
    ∀ (j : ℕ) (Y : ℝ), 1 ≤ Y → C * Y ^ c < 2 ^ j → ∀ f : G1 E n → ℂ,
      (∀ g : G1 E n, f g ≠ 0 → heightOff q (g : AdelicGLn.AdelicGL E n) ≤ Y ∧
        (∃ a ∈ GroundTheory.Automorphic.GLnLocal.iwahori (w₀.1.adicCompletion E) n, ∃ b ∈ GroundTheory.Automorphic.GLnLocal.iwahori (w₀.1.adicCompletion E) n,
          finAt w₀.1 (g : AdelicGLn.AdelicGL E n) = a * Cartan.diagPow (w₀.1.adicCompletion E) n (fun i => (j : ℤ) * ν i) * b) ∧
        ∀ w : PlacesOver E q, w ≠ w₀ → finAt w.1 (g : AdelicGLn.AdelicGL E n) ∈ GroundTheory.Automorphic.GLnLocal.iwahori (w.1.adicCompletion E) n) →
      Ell σ f

def G2 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∃ (C : ℝ) (c : ℕ), ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (f : CC E n) (Y : ℝ), 1 ≤ Y → (∀ g : G1 E n, f g ≠ 0 → AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) ≤ Y) → Ell σ f →
      ∀ x : G1 E n, twK θ f x ≠ 0 → qht x ≤ C * Y ^ c

def G3 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μE : Measure (G1 E n)) [μE.IsHaarMeasure] (μF : Measure (G1 F n)) [μF.IsHaarMeasure]
    (θ : Twist μE), IsGalTwist σ θ → ∀ (c : ℂ) (fE : CC E n) (fF : CC F n),
      Ell σ fE → Ell (1 : F ≃ₐ[F] F) fF → GMatch σ μE μF c fE fF → twInt θ fE = c * twInt (Twist.id μF) fF

open Classical in

def G4 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → (Module.finrank F E).Prime →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing E))]
      [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (GL (Fin n) (CompletionsOver E v))]
      [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (GL (Fin n) (v.adicCompletion F))]
      [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (μE : Measure (G1 E n)) (μF : Measure (G1 F n))
      (μiE : Measure (GL (Fin n) (InfiniteAdeleRing E))) (μiF : Measure (GL (Fin n) (InfiniteAdeleRing F)))
      (mE : ∀ v : HeightOneSpectrum (𝓞 F), Measure (GL (Fin n) (CompletionsOver E v)))
      (mF : ∀ v : HeightOneSpectrum (𝓞 F), Measure (GL (Fin n) (v.adicCompletion F))),
      μE.IsHaarMeasure → μF.IsHaarMeasure → μiE.IsHaarMeasure → μiF.IsHaarMeasure →
      (∀ v, (mE v).IsHaarMeasure ∧ mE v (unitSet E n v) = 1) →
      (∀ v, (mF v).IsHaarMeasure ∧ mF v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (φi : GL (Fin n) (InfiniteAdeleRing E) → ℂ) (fi : GL (Fin n) (InfiniteAdeleRing F) → ℂ)
      (φ : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (CompletionsOver E v) → ℂ)
      (f : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F) → ℂ) (ci : ℂ) (c : HeightOneSpectrum (𝓞 F) → ℂ),
      Continuous φi → HasCompactSupport φi → Continuous fi → HasCompactSupport fi →
      (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ Continuous (f v) ∧ HasCompactSupport (f v)) →
      (∀ v ∉ S, φ v = (unitSet E n v).indicator 1 ∧
        f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 ∧ c v = 1) →
      Match (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) (Module.finrank F E) μiE μiF ci φi fi →
      (∀ v, Match (incFin E v) (galFin σ v) (Module.finrank F E) (mE v) (mF v) (c v) (φ v) (f v)) →
      GMatch σ μE μF ((κ : ℂ) * ci * ∏ v ∈ S, c v) (avg (tensE φi φ)) (avg (tensF fi f))

def G5 : Prop := (∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 0 < n → ∀ Φ : AdelicGLn.AdelicGL E n → ℂ, Continuous Φ →
      HasCompactSupport Φ → Continuous (avg Φ) ∧ HasCompactSupport (avg Φ)) ∧
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φi : GL (Fin n) (InfiniteAdeleRing E) → ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (CompletionsOver E v) → ℂ), Continuous φi → HasCompactSupport φi →
    (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v)) → (∀ v ∉ S, φ v = (unitSet E n v).indicator 1) →
    Continuous (tensE φi φ) ∧ HasCompactSupport (tensE φi φ)

def Q1 : Prop := ∀ (X G T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (u : X →* G) (i : T →* X), Measurable u → Continuous i → ∀ (Φ : X → ℂ) (ρ : G → ℝ≥0∞), Measurable Φ →
      (∀ t x, Φ (i t * x) = Φ x) → IsNormAlong u (fun t => u (i t)) ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ (u x) ∂μ < ⊤ →
      quotInt μ u (fun t => u (i t)) ν Φ = ∫ x, Φ x * ((ρ (u x)).toReal : ℂ) ∂μ

def Q2 : Prop := ∀ (X T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (i : T →* X), Topology.IsClosedEmbedding i → ∃ ρ : X → NNReal, Continuous ρ ∧
      IsNormAlong id i ν (fun x => (ρ x : ℝ≥0∞)) ∧
      ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧ ∀ t, ∀ x ∈ C, ρ (i t * x) ≠ 0 → i t * x ∈ C'

def Q3 : Prop := ∀ (X T X' T' : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] [Group X'] [TopologicalSpace X'] [IsTopologicalGroup X'] [LocallyCompactSpace X'] [T2Space X']
    [SecondCountableTopology X'] [MeasurableSpace X'] [BorelSpace X'] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T']
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] (μ' : Measure X') [μ'.IsHaarMeasure]
    (ν' : Measure T') [ν'.IsHaarMeasure] [ν.IsInvInvariant] [ν'.IsInvInvariant] [ν.IsMulRightInvariant]
    [ν'.IsMulRightInvariant] (i : T →* X) (i' : T' →* X'), Topology.IsClosedEmbedding i → Topology.IsClosedEmbedding i' →
    ∀ (Φ : X → ℂ) (Φ' : X' → ℂ), Continuous Φ → Continuous Φ' → (∀ t x, Φ (i t * x) = Φ x) → (∀ t x, Φ' (i' t * x) = Φ' x) →
      (∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i t * y) →
      (∃ C, IsCompact C ∧ ∀ x, Φ' x ≠ 0 → ∃ t, ∃ y ∈ C, x = i' t * y) →
      quotInt (μ.prod μ') id (fun t : T × T' => (i t.1, i' t.2)) (ν.prod ν') (fun x => Φ x.1 * Φ' x.2) =
        quotInt μ id i ν Φ * quotInt μ' id i' ν' Φ'

def U1 : Prop := ∀ (X : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (Γ : Subgroup X) [DiscreteTopology Γ] (μ : Measure X) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (θ : X →* X), Continuous θ → (∀ g ∈ Γ, θ g ∈ Γ) → ∀ (f : CompactlySupportedContinuousMap X ℂ),
    (∃ C, IsCompact C ∧ ∀ x, ∀ δ ∈ Γ, f (x⁻¹ * δ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y) →
    ∀ (ι : Type) (r : ι → X), (∀ i, r i ∈ Γ) →
      (∀ δ ∈ Γ, (∃ x, f (x⁻¹ * δ * θ x) ≠ 0) → ∃ i, ∃ g ∈ Γ, δ = g⁻¹ * r i * θ g) →
      (∀ i i', ∀ g ∈ Γ, r i' = g⁻¹ * r i * θ g → i = i') →
      ∀ [∀ i, DiscreteTopology ↥(Γ ⊓ twCent θ (r i))],
      HasSum (fun i => ∫ y, f ((Quotient.out y)⁻¹ * r i * θ (Quotient.out y)) ∂quotientMeasure (Γ ⊓ twCent θ (r i)) μ)
        (∫ y, ∑ᶠ γ : Γ, f ((Quotient.out y)⁻¹ * (γ : X) * θ (Quotient.out y)) ∂quotientMeasure Γ μ) ∧
      ∀ i, Integrable (fun y => f ((Quotient.out y)⁻¹ * r i * θ (Quotient.out y))) (quotientMeasure (Γ ⊓ twCent θ (r i)) μ)

def U2 : Prop := ∀ (X T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] [ν.IsMulRightInvariant] (i : T →* X), Topology.IsClosedEmbedding i →
    ∀ (Λ : Subgroup T) [DiscreteTopology Λ] (Γ₀ : Subgroup X) [DiscreteTopology Γ₀], Λ.map i = Γ₀ →
      quotientMeasure Λ ν Set.univ < ⊤ → ∀ Φ : X → ℂ, Continuous Φ → (∀ t x, Φ (i t * x) = Φ x) →
      Integrable (fun y => Φ (Quotient.out y)) (quotientMeasure Γ₀ μ) →
      ∫ y, Φ (Quotient.out y) ∂quotientMeasure Γ₀ μ = ((quotientMeasure Λ ν Set.univ).toReal : ℂ) * quotInt μ id i ν Φ ∧
      ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤

def N1 : Prop := ∀ (k E : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E),
    (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, ∀ δ : GL (Fin n) E, IsTwRegSemisimple σ δ →
    ∃ (h : GL (Fin n) E) (γ : GL (Fin n) k), normGL σ (h⁻¹ * δ * sigmaGL σ h) = incl γ

def N2 : Prop := ∀ (k E : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E),
    (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, (∀ (δ δ' : GL (Fin n) E) (γ : GL (Fin n) k), IsRegSemisimple γ → normGL σ δ = incl γ →
      normGL σ δ' = incl γ → ∃ h : GL (Fin n) E, δ' = h⁻¹ * δ * sigmaGL σ h) ∧
    ∀ γ γ' : GL (Fin n) k, IsRegSemisimple γ →
      (γ : Matrix (Fin n) (Fin n) k).charpoly = (γ' : Matrix (Fin n) (Fin n) k).charpoly → ∃ h : GL (Fin n) k, γ' = h⁻¹ * γ * h

def N3 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F), IsRegSemisimple γ → normGL σ δ = incl γ →
    ∀ x : AdelicGLn.AdelicGL E n, x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x = AdelicGLn.diagonal E n δ ↔
      ∃ t : AdelicGLn.AdelicGL F n, t * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t ∧ x = mapGL n (adeleMap F E) t

def N4 : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F) (γ₁ : G1 F n),
    (γ₁ : AdelicGLn.AdelicGL F n) = AdelicGLn.diagonal F n γ → Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly →
    (∀ s t : Subgroup.centralizer {γ₁}, s * t = t * s) ∧
    ∃ C : Set (Subgroup.centralizer {γ₁}), IsCompact C ∧ ∀ t : Subgroup.centralizer {γ₁},
      ∃ g : Subgroup.centralizer {γ₁}, (g : G1 F n) ∈ Gam F n ∧ ∃ y ∈ C, t = g * y

def N5 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → Topology.IsClosedEmbedding (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n) ∧
    (∀ g : AdelicGLn.AdelicGL F n, (detModule E n (mapGL n (adeleMap F E) g) : ℝ) = (detModule F n g : ℝ) ^ Module.finrank F E) ∧
    ∀ g : AdelicGLn.AdelicGL E n, detModule E n (mapGL n (galAd σ) g) = detModule E n g

def P1 : Prop := ∀ (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] [CharZero k] (n : ℕ) (γ : GL (Fin n) k),
    (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable → ∀ D : Set (GL (Fin n) k), IsCompact D →
    ∃ C : Set (GL (Fin n) k), IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y

def P2 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) (v.adicCompletion F)) (δ : GL (Fin n) (CompletionsOver E v)),
      (γ : Matrix (Fin n) (Fin n) (v.adicCompletion F)).charpoly.Separable →
      twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) γ →
      ∀ D : Set (GL (Fin n) (CompletionsOver E v)), IsCompact D → ∃ C, IsCompact C ∧
        ∀ x, x⁻¹ * δ * mapGL n (galFin σ v) x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = mapGL n (incFin E v) t * y) ∧
    ∀ (γ : GL (Fin n) (InfiniteAdeleRing F)) (δ : GL (Fin n) (InfiniteAdeleRing E)),
      (γ : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)).charpoly.Separable →
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ =
        mapGL n (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) γ →
      ∀ D : Set (GL (Fin n) (InfiniteAdeleRing E)), IsCompact D → ∃ C, IsCompact C ∧
        ∀ x, x⁻¹ * δ * mapGL n (galInf σ) x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C,
          x = mapGL n (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) t * y

def K1 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F), IsRegSemisimple γ → normGL σ δ = incl γ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : GL (Fin n) (CompletionsOver E v),
      x⁻¹ * mapGL n (atFin v) (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x ∈ unitSet E n v ↔
      ∃ t : GL (Fin n) (v.adicCompletion F), t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
        ∃ y ∈ unitSet E n v, x = mapGL n (incFin E v) t * y

def H1 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → (Module.finrank F E).Prime → ∀ γ : GL (Fin n) F, Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly →
    (∃ δ, twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ =
      mapGL n (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (mapGL n (RingHom.fst _ _) (AdelicGLn.diagonal F n γ))) →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ δ, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ =
      mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ))) →
    ∃ δ : GL (Fin n) E, normGL σ δ = incl γ

def A1 : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (μ : Fin n → ℤ), Function.Injective μ → ∀ a ∈ GroundTheory.Automorphic.GLnLocal.iwahori k n, ∀ b ∈ GroundTheory.Automorphic.GLnLocal.iwahori k n, ∀ p : k[X], p.Monic →
      p ∣ ((a * Cartan.diagPow k n μ * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly →
      ∃ J : Finset (Fin n), J.card = p.natDegree ∧
        ValuativeRel.valuation k (p.coeff 0) = ValuativeRel.valuation k (∏ i ∈ J, ((Cartan.diagPow k n μ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i)

end PositivityTheory.Rg.Tf.Geo
