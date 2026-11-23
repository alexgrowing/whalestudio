import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G
open scoped ENNReal NumberField.AdeleRing

namespace UpperTheory.ConvolutionTheory.T4

section

abbrev Pl (K : Type) [Field K] : Type := HeightOneSpectrum (𝓞 K)

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev GA : Type := AdelicGLn.AdelicGL K n

abbrev pI : GA K n →* GL (Fin n) (InfiniteAdeleRing K) := mapGL n (RingHom.fst _ _)

def pF (v : Pl K) : GA K n →* GL (Fin n) (v.adicCompletion K) where
  toFun := finAt v
  map_one' := Units.ext (by ext a b; simp only [finAt_apply, Units.val_one, Matrix.one_apply]; split_ifs <;> rfl)
  map_mul' := finAt_mul v

theorem pF_apply (v : Pl K) (g : GA K n) : pF K n v g = finAt v g := rfl

abbrev KF (v : Pl K) : Subgroup (GL (Fin n) (v.adicCompletion K)) := GLnLocal.integralGL (v.adicCompletion K) n

abbrev zA (s : ℝ) : GA K n := centralSection K n ⟨Real.exp s, Real.exp_pos s⟩

variable {K n}

abbrev TA (γ : GL (Fin n) K) : Subgroup (GA K n) := Subgroup.centralizer {AdelicGLn.diagonal K n γ}

abbrev TI (γ : GL (Fin n) K) : Subgroup (GL (Fin n) (InfiniteAdeleRing K)) :=
  Subgroup.centralizer {pI K n (AdelicGLn.diagonal K n γ)}

abbrev TF (γ : GL (Fin n) K) (v : Pl K) : Subgroup (GL (Fin n) (v.adicCompletion K)) :=
  Subgroup.centralizer {pF K n v (AdelicGLn.diagonal K n γ)}

abbrev EulT [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing K))] [∀ v : Pl K, MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    (γ : GL (Fin n) K) (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl K, Measure (TF γ v)) (b : NNReal)
    (S : Finset (Pl K)) : Prop :=
  Eul (cen (pI K n) (AdelicGLn.diagonal K n γ)) (fun v => cen (pF K n v) (AdelicGLn.diagonal K n γ))
    (fun v => (KF K n v).comap (TF γ v).subtype) ν νi nv b S

def FF (γ : GL (Fin n) K) (Φ : GA K n → ℂ) (x : GA K n) : ℂ :=
  ∫ s : ℝ, Φ (zA K n s * (x⁻¹ * AdelicGLn.diagonal K n γ * x))

end

section

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E] (n : ℕ)

variable (F) in

abbrev infMap : InfiniteAdeleRing F →+* InfiniteAdeleRing E :=
  GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)

abbrev pE (v : Pl F) : GA E n →* GL (Fin n) (CompletionsOver E v) := mapGL n (atFin v)

def KE (v : Pl F) : Subgroup (GL (Fin n) (CompletionsOver E v)) where
  carrier := unitSet E n v
  one_mem' w := by rw [map_one]; exact one_mem _
  mul_mem' {a b} ha hb w := by rw [map_mul]; exact mul_mem (ha w) (hb w)
  inv_mem' {a} ha w := by rw [map_inv]; exact inv_mem (ha w)

variable {E n}

def FE (σ : E ≃ₐ[F] E) (δ : GL (Fin n) E) (Φ : GA E n → ℂ) (x : GA E n) : ℂ :=
  ∫ s : ℝ, Φ (zA E n s * (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x))

end

def QSub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (H : Subgroup G), IsClosed (H : Set G) → ∀ (μ : Measure H) (j : T →* H) (ν : Measure T), Pair μ j ν →
    ∀ Φ : H → ℂ, Measurable Φ → (∀ t g, Φ (j t * g) = Φ g) →
      quotInt μ (fun x : H => (x : G)) (fun t => (j t : G)) ν Φ = qI μ j ν Φ

def RPF : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), RP (pI K n) (pF K n) (KF K n)

def RPE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    RP (pI E n) (fun v : Pl F => pE E n v) (fun v => KE E n v)

def Compat : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
    (∀ g, pI E n (mapGL n (galAd σ) g) = mapGL n (galInf σ) (pI E n g)) ∧
    (∀ (v : Pl F) g, pE E n v (mapGL n (galAd σ) g) = mapGL n (galFin σ v) (pE E n v g)) ∧
    (∀ g, pI E n (mapGL n (adeleMap F E) g) = mapGL n (infMap F E) (pI F n g)) ∧
    (∀ (v : Pl F) g, pE E n v (mapGL n (adeleMap F E) g) = mapGL n (incFin E v) (pF F n v g)) ∧
    (∀ g, mapGL n (galAd σ) (mapGL n (adeleMap F E) g) = mapGL n (adeleMap F E) g) ∧
    (∀ g, mapGL n (galInf σ) (mapGL n (infMap F E) g) = mapGL n (infMap F E) g) ∧
    (∀ δ, mapGL n (galAd σ) (AdelicGLn.diagonal E n δ) = AdelicGLn.diagonal E n (sigmaGL σ δ)) ∧
    ∀ γ, mapGL n (adeleMap F E) (AdelicGLn.diagonal F n γ) = AdelicGLn.diagonal E n (incl γ)

def GalCont : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
    Continuous (mapGL n (galAd σ)) ∧ Continuous (mapGL n (galInf σ)) ∧ ∀ v : Pl F, Continuous (mapGL n (galFin σ v))

def LocEmb : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    IsClosedEmbedding (mapGL n (infMap F E)) ∧ ∀ v : Pl F, IsClosedEmbedding (mapGL n (incFin E v))

def UnitIff : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (t : GL (Fin n) (v.adicCompletion F)),
    mapGL n (incFin E v) t ∈ unitSet E n v ↔ t ∈ KF F n v

def CentLoc : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}),
    (∃ r : (InfiniteAdeleRing K)ˣ, ∀ g : GL (Fin n) (InfiniteAdeleRing K),
      ((pI K n (centralSection K n s) * g : GL (Fin n) (InfiniteAdeleRing K)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
        (r : InfiniteAdeleRing K) • (g : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))) ∧
    (∀ g, pI K n (centralSection K n s) * g = g * pI K n (centralSection K n s)) ∧
    (∀ v : Pl K, pF K n v (centralSection K n s) = 1) ∧
    ∀ (F : Type) [Field F] [NumberField F] [Algebra F K] (v : Pl F), pE K n v (centralSection K n s) = 1

def CentBC : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (s : {r : ℝ // 0 < r}),
    mapGL n (adeleMap F E) (centralSection F n s) = centralSection E n (s ^ Module.finrank F E)

def ZNorm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (s : ℝ) (δ : GL (Fin n) (InfiniteAdeleRing E)),
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) (pI E n (zA E n s) * δ) =
        mapGL n (infMap F E) (pI F n (zA F n s)) * twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ

def LocNorm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F), normGL σ δ = incl γ →
      twNorm (mapGL n (galInf σ)) (Module.finrank F E) (pI E n (AdelicGLn.diagonal E n δ)) =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ)) ∧
      ∀ v : Pl F, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) (pE E n v (AdelicGLn.diagonal E n δ)) =
        mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ))

def SepLoc : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable ∧
    (∀ s : ℝ, (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable) ∧
    ∀ v : Pl F, (finAt v (AdelicGLn.diagonal F n γ)).val.charpoly.Separable

def TComm : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    (∀ s t : TA γ, s * t = t * s) ∧ (∀ s t : TI γ, s * t = t * s) ∧ (∀ v : Pl F, ∀ s t : TF γ v, s * t = t * s) ∧
    ∀ γ₁ : G1 F n, (γ₁ : GA F n) = AdelicGLn.diagonal F n γ → ∀ s t : Subgroup.centralizer {γ₁}, s * t = t * s

def Triv : Prop := ∀ (F : Type) [Field F] [NumberField F],
    galInf (1 : F ≃ₐ[F] F) = RingHom.id _ ∧ infMap F F = RingHom.id _ ∧
    ∀ v : Pl F, galFin (1 : F ≃ₐ[F] F) v = RingHom.id _ ∧ Function.Bijective (incFin F v)

def BoundE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (δ : GL (Fin n) (InfiniteAdeleRing E)) (D : Set (GL (Fin n) (InfiniteAdeleRing E))), IsCompact D →
      ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x) ∈ D → s ∈ B

def InfF : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ γ : GL (Fin n) (InfiniteAdeleRing F),
    (∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D →
      ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, pI F n (zA F n s) * (x⁻¹ * γ * x) ∈ D → s ∈ B) ∧
    (γ.val.charpoly.Separable → ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D →
      ∃ C, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y)

def SelmerRankBoundLaurent : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
    ∀ᶠ v : Pl F in cofinite, ∀ x : GL (Fin n) (v.adicCompletion F),
      x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ KF F n v ↔
      ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧ ∃ y ∈ KF F n v, x = t * y

def Spl : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    (∃ e : G1 E n × {r : ℝ // 0 < r} ≃ₜ* GA E n, ∀ x, e x = (x.1 : GA E n) * mapGL n (adeleMap F E) (centralSection F n x.2)) ∧
    ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : GA F n) = AdelicGLn.diagonal F n γ →
      (∃ e : Subgroup.centralizer {γ₁} × {r : ℝ // 0 < r} ≃ₜ* TA γ,
        ∀ x, (e x : GA F n) = ((x.1 : G1 F n) : GA F n) * centralSection F n x.2) ∧
      ∃ j : Subgroup.centralizer {γ₁} →* G1 E n, IsClosedEmbedding j ∧
        ∀ t, (j t : GA E n) = mapGL n (adeleMap F E) ((t : G1 F n) : GA F n)

def Glob : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (G1 E n)) (μF : Measure (G1 F n)), μE.IsHaarMeasure → μF.IsHaarMeasure →
    ∃ (μE' : Measure (GA E n)) (μF' : Measure (GA F n)), Uni μE' ∧ Uni μF' ∧
      ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : GA F n) = AdelicGLn.diagonal F n γ → IsRegSemisimple γ →
      ∀ ν : Measure (Subgroup.centralizer {γ₁}), ν.IsHaarMeasure → ∃ ν' : Measure (TA γ), ν'.IsHaarMeasure ∧
        (∀ Φ : GA F n → ℂ, Measurable (FF γ Φ) →
          quotInt μF id (fun t : Subgroup.centralizer {γ₁} => (t : G1 F n)) ν (fun x => avg Φ (x⁻¹ * γ₁ * x)) =
            qI μF' (TA γ).subtype ν' (FF γ Φ)) ∧
        ∀ δ : GL (Fin n) E, normGL σ δ = incl γ → ∀ Φ : GA E n → ℂ, Measurable (FE σ δ Φ) →
          quotInt μE (fun x : G1 E n => (x : GA E n))
            (fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n)) ν
            (fun x => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n))) =
            qI μE' ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ν' (FE σ δ Φ)

def SideF : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [∀ v : Pl F, BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (μ : Measure (GA F n)) (μi : Measure (GL (Fin n) (InfiniteAdeleRing F))) (m : ∀ v : Pl F, Measure (GL (Fin n) (v.adicCompletion F))),
      Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
      ∀ (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl F, Measure (TF γ v)),
      ν.IsHaarMeasure → νi.IsHaarMeasure → (∀ v, (nv v).IsHaarMeasure) → ∀ (S : Finset (Pl F)) (a b : NNReal), a ≠ 0 → b ≠ 0 →
      EulT γ ν νi nv b S → Eul (pI F n) (pF F n) (KF F n) μ μi m a S →
      ∀ (fi : GL (Fin n) (InfiniteAdeleRing F) → ℂ) (f : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ),
      Continuous fi → HasCompactSupport fi → (∀ v, Continuous (f v)) →
      (∀ v ∉ S, f v = (KF F n v : Set _).indicator 1 ∧ ∀ x : GL (Fin n) (v.adicCompletion F),
        x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ KF F n v ↔
        ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧ ∃ y ∈ KF F n v, x = t * y) →
      Measurable (FF γ (tensF fi f)) ∧ qI μ (TA γ).subtype ν (FF γ (tensF fi f)) =
        ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) *
          (∫ s : ℝ, qI μi (TI γ).subtype νi fun x => fi (x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x)) *
          ∏ v ∈ S, qI (m v) (TF γ v).subtype (nv v) fun x => f v (x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x)

def SideE : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [∀ v : Pl F, BorelSpace (GL (Fin n) (v.adicCompletion F))]
      [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing E))]
      [∀ v : Pl F, MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [∀ v : Pl F, BorelSpace (GL (Fin n) (CompletionsOver E v))]
      (μ : Measure (GA E n)) (μi : Measure (GL (Fin n) (InfiniteAdeleRing E))) (m : ∀ v : Pl F, Measure (GL (Fin n) (CompletionsOver E v))),
      Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) → ∀ γ : GL (Fin n) F, IsRegSemisimple γ →
      ∀ δ : GL (Fin n) E, normGL σ δ = incl γ →
      ∀ (ν : Measure (TA γ)) (νi : Measure (TI γ)) (nv : ∀ v : Pl F, Measure (TF γ v)),
      ν.IsHaarMeasure → νi.IsHaarMeasure → (∀ v, (nv v).IsHaarMeasure) → ∀ (S : Finset (Pl F)) (a b : NNReal), a ≠ 0 → b ≠ 0 →
      EulT γ ν νi nv b S → Eul (pI E n) (fun v : Pl F => pE E n v) (fun v => KE E n v) μ μi m a S →
      ∀ (φi : GL (Fin n) (InfiniteAdeleRing E) → ℂ) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ),
      Continuous φi → HasCompactSupport φi → (∀ v, Continuous (φ v)) →
      (∀ v ∉ S, φ v = (unitSet E n v).indicator 1 ∧ ∀ x : GL (Fin n) (CompletionsOver E v),
        x⁻¹ * mapGL n (atFin v) (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x ∈ unitSet E n v ↔
        ∃ t : GL (Fin n) (v.adicCompletion F), t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
          ∃ y ∈ unitSet E n v, x = mapGL n (incFin E v) t * y) →
      Measurable (FE σ δ (tensE φi φ)) ∧ qI μ ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ν (FE σ δ (tensE φi φ)) =
        ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) *
          (∫ s : ℝ, qI μi ((mapGL n (infMap F E)).comp (TI γ).subtype) νi fun x =>
            φi (x⁻¹ * (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) * mapGL n (galInf σ) x)) *
          ∏ v ∈ S, qI (m v) ((mapGL n (incFin E v)).comp (TF γ v).subtype) (nv v) fun x =>
            φ v (x⁻¹ * pE E n v (AdelicGLn.diagonal E n δ) * mapGL n (galFin σ v) x)

end UpperTheory.ConvolutionTheory.T4
