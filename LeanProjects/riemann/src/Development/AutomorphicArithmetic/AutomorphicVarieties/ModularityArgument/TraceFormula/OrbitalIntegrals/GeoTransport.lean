import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open GroundTheory.Automorphic
open scoped ENNReal

namespace UpperTheory.V.Z.Tf.Orb

def TwCentImg : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E),
    (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (δ : GL (Fin n) E) (γ : GL (Fin n) k), IsRegSemisimple γ →
    normGL σ δ = incl γ → IsTwRegSemisimple σ δ ∧ twCent (sigmaGL σ) δ = (Subgroup.centralizer {γ}).map incl

def QuotAlong : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (j : H →* G), Topology.IsClosedEmbedding j →
    ∀ μG : Measure G, μG.IsHaarMeasure → ∀ (T : Subgroup H) (S : Subgroup G), IsClosed (T : Set H) → (∀ a ∈ T, ∀ b ∈ T, Commute a b) →
    S = T.map j → ∀ ν : Measure T, ν.IsHaarMeasure → ∃ μ : Measure S, μ.IsHaarMeasure ∧
      Measure.map (fun x : S => (x : G)) μ = Measure.map (fun t : T => j t) ν ∧
      ∀ F : G → ℂ, Measurable F → (∀ s ∈ S, ∀ g, F (s * g) = F g) →
        PositivityTheory.Rg.Tf.Geo.quotInt μG id (fun t : T => j t) ν F = quotIntegral μG S μ F

def OrbEq : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] (μG : Measure G) (T : Subgroup G) (ν : Measure T) (F : G → ℂ),
    PositivityTheory.Rg.Tf.Geo.quotInt μG id (fun t : T => (t : G)) ν F = quotIntegral μG T ν F

def InclClosed : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] (n : ℕ),
    Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E)

def GeoOfMatch : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
    ∀ φ ∈ SB (GL (Fin n) E), ∀ f ∈ SB (GL (Fin n) k), Match σ μE μk φ f →
      PositivityTheory.Rg.Tf.Geo.Match (algebraMap k E) (σ : E →+* E) (Module.finrank k E) μE μk 1 φ f

def QuotReal : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG]
    (H : Subgroup G) (μ : Measure H) [SFinite μ] (A : Set G), MeasurableSet A →
    quotIntegral μG H μ (A.indicator 1) = ((quotLIntegral μG H μ (A.indicator 1)).toReal : ℂ)

def UnitMatch : Prop :=
  BCFLUnit → ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], IsUnramifiedLoc k E → ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 → μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      Match σ μE μk (unitFnC E) (unitFnC k)

def UnitSB : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ),
    IsOpen (unitGL (n := Fin n) E : Set (GL (Fin n) E)) ∧ IsCompact (unitGL (n := Fin n) E : Set (GL (Fin n) E)) ∧
      (unitFnC E : GL (Fin n) E → ℂ) ∈ SB (GL (Fin n) E)

def GeoTransport : Prop :=
  ∀ (R S S' : Type) [CommRing R] [CommRing S] [CommRing S'] [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace S']
    [IsTopologicalRing S] [IsTopologicalRing S'] (e : S ≃+* S'), Continuous e → Continuous e.symm →
    ∀ (ι : R →+* S) (ι' : R →+* S') (s : S →+* S) (s' : S' →+* S'), (∀ x, e (ι x) = ι' x) → (∀ y, e (s y) = s' (e y)) →
    ∀ (n l : ℕ) [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)] [BorelSpace (GL (Fin n) S)]
      [MeasurableSpace (GL (Fin n) S')] [BorelSpace (GL (Fin n) S')] (μ : Measure (GL (Fin n) S)) (μR : Measure (GL (Fin n) R)),
      (μ.IsHaarMeasure → (μ.map (mapGL n (e : S →+* S'))).IsHaarMeasure) ∧
      ∀ (γ : GL (Fin n) R), (∀ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ ↔
          twNorm (mapGL n s') l (mapGL n (e : S →+* S') δ) = mapGL n ι' γ) ∧
        ∀ (ν : Measure (Subgroup.centralizer {γ})) (ρ' : GL (Fin n) S' → ℝ≥0∞),
          (PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : Subgroup.centralizer {γ} => mapGL n ι' (t : GL (Fin n) R)) ν ρ' ↔
            PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : Subgroup.centralizer {γ} => mapGL n ι (t : GL (Fin n) R)) ν
              fun g => ρ' (mapGL n (e : S →+* S') g)) ∧
          ∀ Φ : GL (Fin n) S' → ℂ, ∫ x, Φ x * ((ρ' x).toReal : ℂ) ∂(μ.map (mapGL n (e : S →+* S'))) =
            ∫ x, Φ (mapGL n (e : S →+* S') x) * ((ρ' (mapGL n (e : S →+* S') x)).toReal : ℂ) ∂μ

def AlongIndep : Prop :=
  ∀ (G T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group T] [MeasurableSpace T] [MeasurableInv T]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (ν : Measure T) [SFinite ν] [ν.IsInvInvariant] (j : T →* G), Measurable j →
    ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) → ∀ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t => j t) ν ρ →
    PositivityTheory.Rg.Tf.Geo.quotInt μ id (fun t => j t) ν F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ

def PlaceData : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∃ (_ : Algebra (v.adicCompletion F) (w.1.adicCompletion E)) (_ : ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E))
      (_ : FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)) (_ : IsGalois (v.adicCompletion F) (w.1.adicCompletion E))
      (s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E),
      (∀ τ, τ ∈ Subgroup.zpowers s) ∧ Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E ∧
      (∀ x, incFin E v x w = algebraMap _ (w.1.adicCompletion E) x) ∧ (∀ y, galFin σ v y w = s (y w)) ∧
      (Algebra.IsUnramifiedAt (𝓞 F) w.1.asIdeal → IsUnramifiedLoc (v.adicCompletion F) (w.1.adicCompletion E))

def PlaceOfLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)]
      (s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E),
      (∀ τ, τ ∈ Subgroup.zpowers s) → Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E →
      (∀ x, incFin E v x w = algebraMap _ (w.1.adicCompletion E) x) → (∀ y, galFin σ v y w = s (y w)) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))), mE.IsHaarMeasure → mF.IsHaarMeasure →
    ∀ [MeasurableSpace (GL (Fin n) (w.1.adicCompletion E))] [BorelSpace (GL (Fin n) (w.1.adicCompletion E))],
      (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w))).IsHaarMeasure ∧
      ∀ φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)), ∀ f ∈ SB (GL (Fin n) (v.adicCompletion F)),
        Match s (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w))) mF φ f → PositivityTheory.Rg.Tf.Geo.Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF 1 (fun g => φ (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g)) f

def PlaceUniq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (Module.finrank F E).Prime →
    ∀ v : HeightOneSpectrum (𝓞 F), (¬ ∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)) →
    ∃ w : PlacesOver E v, ∀ w' : PlacesOver E v, w' = w

def PlaceInt : Prop :=
  (∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ),
    (unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) = GLnLocal.integralGL (v.adicCompletion F) n) ∧
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v),
    (∀ w' : PlacesOver E v, w' = w) → ∀ n : ℕ, PositivityTheory.Rg.Tf.Geo.unitSet E n v =
      mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) ⁻¹' unitGL (n := Fin n) (w.1.adicCompletion E)

def PlaceUnit : Prop :=
  BCFLUnit → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    Algebra.IsUnramifiedAt (𝓞 F) w.1.asIdeal →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))), mE.IsHaarMeasure → mF.IsHaarMeasure →
      mE (PositivityTheory.Rg.Tf.Geo.unitSet E n v) = 1 → mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
      PositivityTheory.Rg.Tf.Geo.Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF 1 ((PositivityTheory.Rg.Tf.Geo.unitSet E n v).indicator 1)
        ((GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1)

end UpperTheory.V.Z.Tf.Orb
