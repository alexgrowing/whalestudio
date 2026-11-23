import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

def AvgInt : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → μ K = 1 →
    ∀ U : Subgroup G, IsOpen (U : Set G) → ∀ F : G → ℂ, (∀ u ∈ U, ∀ x, F (x * u) = F x) → ∀ q : G,
      GlobalTheory.BCT.avg (fun y : K => F (q * y)) = ∫ y in (K : Set G), F (q * y) ∂μ

def OneCoset : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → μ K = 1 →
    ∀ T : Subgroup G, IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, Commute a b) → ∀ ν : Measure T, ν.IsHaarMeasure →
    ∀ F : G → ℂ, Continuous F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → ∀ q : G,
      quotIntegral μ T ν ({g | ∃ t ∈ T, ∃ y ∈ K, g = t * q * y}.indicator F) =
        ((ν.real {t : T | q⁻¹ * (t : G) * q ∈ K} : ℝ) : ℂ)⁻¹ * ∫ y in (K : Set G), F (q * y) ∂μ

def VolIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (T C H : Subgroup G),
    IsClosed (T : Set G) → ∀ ν : Measure T, ν.IsHaarMeasure → C ≤ T → IsCompact (C : Set G) → H ≤ C →
    IsOpen {t : T | (t : G) ∈ H} → ν.real {t : T | (t : G) ∈ H} ≠ 0 ∧
      ν.real {t : T | (t : G) ∈ C} = (H.relIndex C : ℝ) * ν.real {t : T | (t : G) ∈ H}

def SumCoset : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → μ K = 1 →
    ∀ T : Subgroup G, IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, Commute a b) → ∀ ν : Measure T, ν.IsHaarMeasure →
    ∀ F : G → ℂ, Continuous F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → CptMod T F →
      {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ y ∈ K, F (Quotient.out q * y) ≠ 0}.Finite ∧
      quotIntegral μ T ν F = ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
        quotIntegral μ T ν ({g | ∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y}.indicator F)

def OrbSum : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → μ K = 1 →
    ∀ (θ : G →* G), Continuous θ → ∀ (δ : G) (T : Subgroup G), T = GlobalTheory.BCT.twCent θ δ → (∀ a ∈ T, ∀ b ∈ T, Commute a b) →
    IsCompact (GlobalTheory.BCT.cptPart T : Set G) → ∀ ν : Measure T, ν.IsHaarMeasure →
    ∀ (U : Subgroup G) (f : G → ℂ), GlobalTheory.BCT.IsLevel θ K U → GlobalTheory.BCT.IsHecke U f → CptMod T (fun x => f (x⁻¹ * δ * θ x)) →
      ν.real {t : T | (t : G) ∈ GlobalTheory.BCT.cptPart T} ≠ 0 ∧
      quotIntegral μ T ν (fun x => f (x⁻¹ * δ * θ x)) =
        ((ν.real {t : T | (t : G) ∈ GlobalTheory.BCT.cptPart T} : ℝ) : ℂ)⁻¹ * GlobalTheory.BCT.twOrb θ K δ f

def CptCpt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : GL (Fin n) k) (T : Subgroup (GL (Fin n) k)), (A : Matrix (Fin n) (Fin n) k).charpoly.Separable →
    IsClosed (T : Set (GL (Fin n) k)) → (∀ t ∈ T, Commute t A) → IsCompact (GlobalTheory.BCT.cptPart T : Set (GL (Fin n) k))

def CptConj : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (j : H →* G),
    Topology.IsClosedEmbedding j → ∀ (S : Subgroup G) (T : Subgroup H) (h : G), (∀ x, x ∈ S ↔ ∃ t ∈ T, h⁻¹ * x * h = j t) →
    IsCompact (GlobalTheory.BCT.cptPart T : Set H) → ∀ (μ : Measure S) (ν : Measure T),
      Measure.map (fun x : S => h⁻¹ * (x : G) * h) μ = Measure.map (fun t : T => j t) ν →
      μ.real {x : S | (x : G) ∈ GlobalTheory.BCT.cptPart S} = ν.real {t : T | (t : H) ∈ GlobalTheory.BCT.cptPart T}

def Dict : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ n : ℕ, GlobalTheory.LBC.galAct σ n = sigmaGL σ ∧ (∀ δ : GL (Fin n) E, GlobalTheory.LBC.norm k σ δ = normGL σ δ) ∧
      (∀ δ : GL (Fin n) E, twCent (sigmaGL σ) δ = GlobalTheory.BCT.twCent (sigmaGL σ) δ) ∧
      (∀ γ : GL (Fin n) k, Subgroup.centralizer {γ} = GlobalTheory.BCT.twCent (MonoidHom.id _) γ) ∧
      (∀ (δ h : GL (Fin n) E) (γ : GL (Fin n) k), IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ → IsRegSemisimple γ ∧
        (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) = (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly ∧
        ∀ x, x ∈ twCent (sigmaGL σ) δ ↔ ∃ t ∈ Subgroup.centralizer {γ}, h⁻¹ * x * h = incl t) ∧
      ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k), IsRegSemisimple γ →
        (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) = (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly → IsNormOf σ δ γ

def MatchOfSum : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ n : ℕ, ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 → μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
    ∀ (UE : Subgroup (GL (Fin n) E)) (Uk : Subgroup (GL (Fin n) k)) (φ : GL (Fin n) E → ℂ) (f : GL (Fin n) k → ℂ),
      GlobalTheory.BCT.IsLevel (GlobalTheory.LBC.galAct σ n) (unitGL E) UE → GlobalTheory.BCT.IsLevel (MonoidHom.id _) (unitGL k) Uk →
      GlobalTheory.BCT.IsHecke UE φ → GlobalTheory.BCT.IsHecke Uk f →
      (∀ δ : GL (Fin n) E, (GlobalTheory.LBC.norm k σ δ : Matrix (Fin n) (Fin n) E).charpoly.Separable →
        ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) =
            (GlobalTheory.LBC.norm k σ δ : Matrix (Fin n) (Fin n) E).charpoly →
          GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct σ n) (unitGL E) δ φ = GlobalTheory.BCT.twOrb (MonoidHom.id _) (unitGL k) γ f) →
      (∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (unitGL k) γ f ≠ 0 →
          ∃ δ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) =
            (GlobalTheory.LBC.norm k σ δ : Matrix (Fin n) (Fin n) E).charpoly) →
      UpperTheory.ConvolutionTheory.Loc.Match σ μE μk φ f

def TrSum : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → μ K = 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ U : Subgroup G, IsOpen (U : Set G) → U ≤ K →
    ∀ f : G → ℂ, GlobalTheory.BCT.IsHecke U f → ∀ A : V →ₗ[ℂ] V, (∀ v ∈ fixed ρ U, A v ∈ fixed ρ U) →
      (∀ v ∈ twKer ρ U 1, A v ∈ twKer ρ U 1) → ∀ (B : V →ₗ[ℂ] V) (c : ℂ), IsIntegralOp μ ρ f B → HasFinTrace (B ∘ₗ A) c →
      FiniteDimensional ℂ (fixed ρ U) → c = GlobalTheory.BCT.twTr ρ K U f A

def TwScale : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) E) V), IsSmooth ρ → ρ.IsIrreducible →
    ∀ I : V ≃ₗ[ℂ] V, (∀ g x, I (ρ g x) = ρ (GlobalTheory.LBC.galAct σ n g) (I x)) →
      ∃ a : ℂ, a ≠ 0 ∧ GlobalTheory.LBC.IsTwInt k σ ρ (a • (I : V →ₗ[ℂ] V))

end UpperTheory.Gal.InertialTypesAlt.L
