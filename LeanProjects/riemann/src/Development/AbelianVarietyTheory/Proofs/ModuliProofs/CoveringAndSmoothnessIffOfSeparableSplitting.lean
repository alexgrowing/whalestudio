import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoveringAndSmoothness
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoveringAbelianLocusSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension

noncomputable section

namespace GlobalTheory.CoveringCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke

section Fibres

def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)

theorem splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩

theorem exists_finite_splitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩

def SeparableSplitting : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G))

end Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isChartAt_iff (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Y.X) :
    CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, f, g⟩, e⟩, fun ⟨⟨a, b, c, d, f, g⟩, e⟩ => ⟨a, b, c, d, e, f, g⟩⟩

theorem covered_iff (Y : Model Xo c β) (p : ℕ) : (∀ x, UniformizationBase.CovAt Y p x) ↔ CoveringAbelianLocusSmooth.CoveredByCharts Y p := by
  refine forall_congr' fun x => ⟨?_, ?_⟩
  · rintro ⟨n, R, _, _, _, ξ, h₁, h₂⟩
    exact ⟨n, R, _, _, _, ξ, fun i => (isChartAt_iff Y x _ _).2 (h₁ i),
      fun V C _ _ _ _ _ _ _ _ => h₂ C V⟩
  · rintro ⟨n, R, _, _, _, ξ, h₁, h₂⟩
    exact ⟨n, R, _, _, _, ξ, fun i => (isChartAt_iff Y x _ _).1 (h₁ i),
      fun C V _ _ _ _ _ _ _ _ => h₂ V C⟩

theorem abLocusSmooth_iff (Y : Model Xo c β) : UniformizationBase.AbLocusSmooth Y ↔ CoveringAbelianLocusSmooth.AbLocusSmooth Y := Iff.rfl

theorem splitFibres_iff_imperfect (Y : Model Xo c β) :
    Y.SplitFibres ↔ ∀ x : Y.X, ¬ PerfectField (Y.X.residueField x) →
      ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
        FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
          SplitOver Y.t.G x k := by
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  by_cases hx : PerfectField (Y.X.residueField x)
  · obtain ⟨k, _, _, hk, hs⟩ := exists_finite_splitOver Y.t.G Y.t.semi x
    exact ⟨k, inferInstance, inferInstance, hk, inferInstance, hs⟩
  · exact h x hx

theorem splitFibres_of_separableSplitting (h : SeparableSplitting) (Y : Model Xo c β) : Y.SplitFibres := fun x => by
  obtain ⟨k, _, _, hk, hs, T⟩ := h (Y.X.residueField x) _
    (IsSemiAbelian.pullback (show Sp (Y.X.residueField x) ⟶ Y.X from Y.X.fromSpecResidueField x) Y.t.G Y.t.semi)
  exact ⟨k, inferInstance, inferInstance, hk, hs, splitOver_of_torusExtension Y.t.G Y.t.semi x k T⟩

end One

theorem goodPrime_iff (l : Level H) (p : ℕ) : UniformizationBase.GoodPrime l p ↔ CoveringAbelianLocusSmooth.GoodPrime l p := Iff.rfl

theorem smoothnessLemma_iff : UniformizationBase.SmoothnessLemma ↔ CoveringAbelianLocusSmooth.SmoothnessLemma := Iff.rfl

def CoveringForSplitFibres : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, (Y i).SplitFibres → ∀ x : (Y i).X, UniformizationBase.CovAt (Y i) p x

theorem coveringLemma_iff_restricted : CoveringAbelianLocusSmooth.CoveringLemma ↔ CoveringForSplitFibres :=
  ⟨fun h E _ _ _ H D Xo p W hp hW Y hY i hs => (covered_iff _ p).2 (h E H D Xo p W hp hW Y hY i hs),
    fun h E _ _ _ H D Xo p W hp hW Y hY i hs => (covered_iff _ p).1 (h E H D Xo p W hp hW Y hY i hs)⟩

theorem coveringLemma_imp (h : UniformizationBase.CoveringLemma) : CoveringAbelianLocusSmooth.CoveringLemma :=
  fun E _ _ _ H D Xo p W hp hW Y hY i _ => (covered_iff _ p).1 (h E H D Xo p W hp hW Y hY i)

theorem coveringLemma_iff_of_separableSplitting (h : SeparableSplitting) :
    UniformizationBase.CoveringLemma ↔ CoveringAbelianLocusSmooth.CoveringLemma :=
  ⟨coveringLemma_imp, fun hB E _ _ _ H D Xo p W hp hW Y hY i =>
    (covered_iff _ p).2 (hB E H D Xo p W hp hW Y hY i (splitFibres_of_separableSplitting h _))⟩

theorem typings_compare :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
      (∀ (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X),
        CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x) ∧
      ((∀ x, UniformizationBase.CovAt Y p x) ↔ CoveringAbelianLocusSmooth.CoveredByCharts Y p) ∧
      (UniformizationBase.AbLocusSmooth Y ↔ CoveringAbelianLocusSmooth.AbLocusSmooth Y) ∧ (UniformizationBase.GoodPrime l p ↔ CoveringAbelianLocusSmooth.GoodPrime l p) ∧
      (Y.SplitFibres ↔ ∀ x : Y.X, ¬ PerfectField (Y.X.residueField x) →
        ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
          FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
            SplitOver Y.t.G x k)) ∧
    (UniformizationBase.SmoothnessLemma ↔ CoveringAbelianLocusSmooth.SmoothnessLemma) ∧
    (CoveringAbelianLocusSmooth.CoveringAndSmoothness ↔ CoveringForSplitFibres ∧ UniformizationBase.SmoothnessLemma) ∧
    (UniformizationBase.CoveringAndSmoothness → CoveringAbelianLocusSmooth.CoveringAndSmoothness) :=
  ⟨fun _ _ _ _ _ _ l _ _ _ _ _ Y p =>
      ⟨fun x R _ _ _ ξ => isChartAt_iff Y x R ξ, covered_iff Y p, abLocusSmooth_iff Y, goodPrime_iff l p,
        splitFibres_iff_imperfect Y⟩,
    smoothnessLemma_iff, and_congr coveringLemma_iff_restricted smoothnessLemma_iff.symm,
    fun h => ⟨coveringLemma_imp h.1, smoothnessLemma_iff.1 h.2⟩⟩

theorem coveringAndSmoothness_iff_of_separableSplitting (h : SeparableSplitting) :
    UniformizationBase.CoveringAndSmoothness ↔ CoveringAbelianLocusSmooth.CoveringAndSmoothness :=
  and_congr (coveringLemma_iff_of_separableSplitting h) smoothnessLemma_iff

end GlobalTheory.CoveringCompare
