import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraAnalyticityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudoCoefficientUnitaryPqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraCharactersOfInputsStatement
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa

open MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmIwa

open CompanionTheory.D.gk.admitted

variable {n : ℕ}

def Gp (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Type := {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G}

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)}

instance : TopologicalSpace (Gp G) := instTopologicalSpaceSubtype
instance : T2Space (Gp G) := inferInstanceAs (T2Space {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G})
instance : SecondCountableTopology (Gp G) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  inferInstanceAs (SecondCountableTopology {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G})

def Gp.m (g : Gp G) : Matrix (Fin n) (Fin n) ℂ := g.1

theorem Gp.m_mem (g : Gp G) : g.m ∈ G := g.2

theorem Gp.ext {a b : Gp G} (h : a.m = b.m) : a = b := Subtype.ext h

theorem continuous_m : Continuous (Gp.m : Gp G → Matrix (Fin n) (Fin n) ℂ) := continuous_subtype_val

theorem isEmbedding_m : Topology.IsEmbedding (Gp.m : Gp G → Matrix (Fin n) (Fin n) ℂ) :=
  Topology.IsEmbedding.subtypeVal

variable [hG : Fact (GlobalTheory.LinRed.IsLinRed G)]

instance : Group (Gp G) where
  mul a b := ⟨a.1 * b.1, hG.out.mul_mem _ a.2 _ b.2⟩
  one := ⟨1, hG.out.one_mem⟩
  inv a := ⟨a.1⁻¹, hG.out.inv_mem _ a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := Subtype.ext
    (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG.out.isUnit _ a.2)))

@[simp] theorem m_mul (a b : Gp G) : (a * b).m = a.m * b.m := rfl
@[simp] theorem m_one : (1 : Gp G).m = 1 := rfl
@[simp] theorem m_inv (a : Gp G) : (a⁻¹).m = (a.m)⁻¹ := rfl

instance : IsTopologicalGroup (Gp G) where
  continuous_mul := by
    refine isEmbedding_m.continuous_iff.2 ?_
    exact (continuous_m.comp continuous_fst).matrix_mul (continuous_m.comp continuous_snd)
  continuous_inv := by
    refine isEmbedding_m.continuous_iff.2 ?_
    have h : ((Gp.m : Gp G → _) ∘ fun a : Gp G => a⁻¹) =
        fun a : Gp G => (a.m.det)⁻¹ • a.m.adjugate := by
      funext a
      show (a.m)⁻¹ = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    refine Continuous.smul (Continuous.inv₀ continuous_m.matrix_det fun a => ?_)
      continuous_m.matrix_adjugate
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hG.out.isUnit _ a.2)).ne_zero

def Kc (G : Set (Matrix (Fin n) (Fin n) ℂ)) [hG : Fact (GlobalTheory.LinRed.IsLinRed G)] : Subgroup (Gp G) where
  carrier := {g | g.m ∈ Matrix.unitaryGroup (Fin n) ℂ}
  one_mem' := Submonoid.one_mem (Matrix.unitaryGroup (Fin n) ℂ)
  mul_mem' ha hb := Submonoid.mul_mem (Matrix.unitaryGroup (Fin n) ℂ) ha hb
  inv_mem' {a} ha := by
    show (a.m)⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ha)]
    exact Unitary.star_mem ha

theorem mem_Kc {k : Gp G} : k ∈ Kc G ↔ k.m ∈ Matrix.unitaryGroup (Fin n) ℂ := Iff.rfl

theorem isCompact_maxCpt : IsCompact (GlobalTheory.LinRed.maxCpt G) := by
  have hbd : GlobalTheory.LinRed.maxCpt G ⊆ Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 := by
    intro g hg i _ j _
    simpa using entry_norm_bound_of_unitary hg.2 i j
  have hcmp : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 : Set (Fin n → Fin n → ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset hcmp ?_ hbd
  refine isClosed_of_closure_subset fun g hg => ?_
  have hU : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = {m | mᴴ * m = 1} := by
      ext m
      exact Matrix.mem_unitaryGroup_iff'
    rw [this]
    exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hgU : g ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hU.closure_subset_iff.2 Set.inter_subset_right (closure_mono (le_refl _) hg)
  have hgu : IsUnit g := IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.1 hgU)
  exact ⟨hG.out.closed g hgu (closure_mono Set.inter_subset_left hg), hgU⟩

instance : CompactSpace (Kc G) := by
  refine isCompact_univ_iff.1 ?_
  have he : Topology.IsEmbedding fun k : Kc G => (k.1).m :=
    isEmbedding_m.comp Topology.IsEmbedding.subtypeVal
  rw [he.isCompact_iff, Set.image_univ]
  have : Set.range (fun k : Kc G => (k.1).m) = GlobalTheory.LinRed.maxCpt G := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1.2, mem_Kc.1 k.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨m, h1⟩, mem_Kc.2 h2⟩, rfl⟩
  rw [this]
  exact isCompact_maxCpt

instance : MeasurableSpace (Kc G) := borel _
instance : BorelSpace (Kc G) := ⟨rfl⟩

def homG {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn G σ) : Gp G →* (H →L[ℂ] H) where
  toFun g := σ g.m
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdG (G : Set (Matrix (Fin n) (Fin n) ℂ)) [hG : Fact (GlobalTheory.LinRed.IsLinRed G)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Gp G →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * g.m * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (a.m * b.m) * U = _
    calc Uᴴ * (a.m * b.m) * U = Uᴴ * a.m * (U * Uᴴ) * b.m * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

omit hG in

theorem admissible_of_polynomial_identity (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg)
    (hLR : GlobalTheory.LinRed.IsLinRed G) (h5 : PositivityTheory.Tls2.Iua.IwaOn G) : PositivityTheory.Tls2.Iua.AdmG G := by
  haveI : Fact (GlobalTheory.LinRed.IsLinRed G) := ⟨hLR⟩
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (Kc G) := (Measure.haar : Measure (Kc G)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (Kc G) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homG hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homG hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_m fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (Kc G) μ H ((homG hσ).comp (Kc G).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ ⟨k.1.2, mem_Kc.1 k.2⟩ u hu) v hv
  let st : Gp G → Gp G := fun g => ⟨g.mᴴ, hLR.star_mem _ g.2⟩
  let Tr : Set (Gp G) := {s | (stdG G hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdG G hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_m).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * g.mᴴ * U = (Uᴴ * g.m * U)ᴴ
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdG G hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : Gp G, U * stdG G hU g * Uᴴ = g.m := fun g => by
      show U * (Uᴴ * g.m * U) * Uᴴ = _
      calc U * (Uᴴ * g.m * U) * Uᴴ = (U * Uᴴ) * g.m * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact Gp.ext ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : Gp G, ∃ k ∈ Kc G, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa g.m g.2
    exact ⟨⟨k, hk.1⟩, mem_Kc.2 hk.2, ⟨s, hs⟩, ht, Gp.ext hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → Gp G, stdPoly E (fun i => homG hσ (g i)) = 0 := fun g =>
    h3 (Gp G) (Kc G) μ st Tr (Fin n) (stdG G hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (Gp G) (Kc G) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homG hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (Gp G) H (homG hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu =>
    hS' ⟨g, hg⟩ u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ k.1.1 (T u) = T (e k • σ k.1.1 u)
    rw [map_smul, hT _ ⟨k.1.2, mem_Kc.1 k.2⟩ u]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem RamifiedPrimeLengthBound {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hLR : GlobalTheory.LinRed.IsLinRed G)
    (h : PositivityTheory.Tls2.Iua.IwaOn G) : PositivityTheory.Tls2.Iua.AdmG G :=
  admissible_of_polynomial_identity finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator hLR h

end GlobalTheory.CompanionTheory.AdmIwa
