import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedUnipotentRadicalAtRealPlaceTrivialAtPlacStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalAtRealPlaceCommuteInfTrivialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalEqAtRealPlaceMulTrivialAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelIndicatorTestFunctionFactorAtRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealComponentFrameHomUnitaryDiagStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingRealComponentUnipotentRadicalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

open GlobalTheory.FibreAtTau

variable {D : D7}

theorem isHaarSub_map_closedEmb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : GlobalTheory.Dec.IsHaarSub (N : Set H) ν) :
    GlobalTheory.Dec.IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hm : Measurable ι := hι.continuous.measurable
  have hc : IsClosed ((N.map ι : Subgroup G) : Set G) := hι.isClosedMap _ hN
  obtain ⟨h0, hK, hc0, hinv⟩ := hν
  refine ⟨?_, ⟨fun K hK' => ?_⟩, ?_, ?_⟩
  · rwa [Ne, Measure.map_eq_zero_iff hm.aemeasurable]
  · rw [Measure.map_apply hm hK'.isClosed.measurableSet]
    exact (hι.isCompact_preimage hK').measure_lt_top
  · rw [Measure.map_apply hm hc.measurableSet.compl]
    refine measure_mono_null (fun z hz hzN => hz ⟨z, hzN, rfl⟩) hc0
  · rintro _ ⟨m, hmN, rfl⟩
    rw [Measure.map_map (measurable_const_mul _) hm]
    have : ((fun x => ι m * x) ∘ ι) = ι ∘ (fun x => m * x) := by
      funext x; simp
    rw [this, ← Measure.map_map hm (measurable_const_mul _), hinv m hmN]

theorem isHaarSub_top {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] : GlobalTheory.Dec.IsHaarSub ((⊤ : Subgroup H) : Set H) ν := by
  refine ⟨NeZero.ne ν, inferInstance, by simp, fun m _ => MeasureTheory.map_mul_left_eq_self ν m⟩

theorem L_closed (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) :
    IsClosed (atP θ V C τ : Set (NI V C)) ∧ IsClosed (offP θ V C τ : Set (NI V C)) :=
  GlobalTheory.T.isClosed_unipotentRadical_atRealPlace_trivialAtPlace D θ hθ V r C τ

theorem L_comm (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) :
    (∀ p ∈ atP θ V C τ, ∀ q ∈ offP θ V C τ, p * q = q * p) ∧ ∀ h, h ∈ atP θ V C τ → h ∈ offP θ V C τ → h = 1 :=
  GlobalTheory.T.unipotentRadical_atRealPlace_commute_inf_trivial D θ hθ V r C τ

theorem L_decomp (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : IsIsoFrame V C) (τ : D.what₂.Tau) (h : NI V C) : ∃ p ∈ atP θ V C τ, ∃ q ∈ offP θ V C τ, h = p * q :=
  GlobalTheory.T.unipotentRadical_eq_atRealPlace_mul_trivialAtPlace D θ hθ V r C hC τ h

theorem L_factor (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (τ : D.what₂.Tau) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (q : NI V C) (hq : q ∈ offP θ V C τ) (x y : GA D V) :
    ∃ R : ℂ, ∀ p ∈ atP θ V C τ, coef θ M K v a (x * ((p * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.rep τ (cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y) (a τ)⟫_ℂ * R :=
  GlobalTheory.T.levelIndicatorTestFunction_factor_atRealPlace D θ hθ V S M K v a τ r C q hq x y

theorem L_hom (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ),
      ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
  GlobalTheory.T.exists_realComponent_frame_hom_unitaryDiag D θ hθ V S M τ

theorem L_emb (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (E : GA D V →* Formalism.REAL.UJ (M.ε τ)) (hE : ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) :
    ∃ W : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.Dec.IsIsoC (M.ε τ) W ∧
      Topology.IsClosedEmbedding (fun p : atP θ V C τ => E ((p : NI V C) : GA D V)) ∧
      Set.range (fun p : atP θ V C τ => E ((p : NI V C) : GA D V)) = GlobalTheory.Dec.NW (M.ε τ) W :=
  GlobalTheory.T.isClosedEmbedding_realComponent_unipotentRadical D θ hθ V S M τ r C hC E hE

theorem fibre_integral_eq_zero : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (v a : ∀ τ, M.H τ), (∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → (∀ τ, a τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →
    ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧
      ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V,
        ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  intro hP D θ hθ V S M K v a hv ha τ r C hC
  refine ⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1,
    L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩
  intro ν hν q hq x y
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩
  obtain ⟨E, hE⟩ := L_hom θ hθ V S M τ
  obtain ⟨W, hW, hemb, hrange⟩ := L_emb θ hθ V S M τ C hC E hE
  obtain ⟨R, hR⟩ := L_factor θ hθ V S M K v a τ C q hq x y
  let ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ) := E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)
  have hι : Topology.IsClosedEmbedding ι := hemb
  have hmap := isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)
  have hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W := by
    rw [← MonoidHom.range_eq_map, MonoidHom.coe_range]
    exact hrange
  rw [hr] at hmap
  have hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ) := by
    have hDS := M.ds τ
    exact ⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩
  have h0 := ((GlobalTheory.Published.discreteSeriesCoefficientsCuspidal_iff.1 hP) V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (a τ) (v τ)
    (ha τ) (hv τ) W hW (ν.map ι) hmap (E x) (E y)).2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R := by
    intro p
    rw [hR p p.2]
    congr 2
    show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)
    congr 2
    change M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)
    rw [hE, hE, hE]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  simp_rw [key]
  have hint := hι.measurableEmbedding.integral_map (μ := ν)
    (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)
  rw [integral_mul_const, ← hint, h0, zero_mul]

end GlobalTheory.FibreAtTau
