import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section
namespace GlobalTheory.HaarSB

section General

variable (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G]

def measG : MeasurableSpace G := borel G

attribute [local instance] measG

instance borelG : BorelSpace G := ⟨rfl⟩

def intSub : Submodule ℂ (G → ℂ) where
  carrier := {h | Integrable h (Measure.addHaar : Measure G)}
  zero_mem' := integrable_zero _ _ _
  add_mem' := Integrable.add
  smul_mem' c _ h := h.smul c

def I0 : intSub G →ₗ[ℂ] ℂ where
  toFun h := ∫ x, (h : G → ℂ) x ∂(Measure.addHaar : Measure G)
  map_add' h h' := integral_add h.2 h'.2
  map_smul' c h := integral_smul c (h : G → ℂ)

def Lext : (G → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend (I0 G)).choose

variable {G}

theorem Lext_apply (h : G → ℂ) (hh : Integrable h (Measure.addHaar : Measure G)) :
    Lext G h = ∫ x, h x ∂(Measure.addHaar : Measure G) :=
  LinearMap.congr_fun (LinearMap.exists_extend (I0 G)).choose_spec ⟨h, hh⟩

theorem integrable_of_SB {f : G → ℂ} (hf : f ∈ SB G) : Integrable f (Measure.addHaar : Measure G) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem Lext_translate {f : G → ℂ} (hf : f ∈ SB G) (a : G) :
    Lext G (fun x => f (x + a)) = Lext G f := by
  have hi := integrable_of_SB hf
  rw [Lext_apply _ (hi.comp_add_right a), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

end General

theorem exists_invariant_form (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (K : Set G) (hKc : IsCompact K) (hKo : IsOpen K) (h0 : (0 : G) ∈ K) :
    ∃ Λ : (G → ℂ) →ₗ[ℂ] ℂ, (∀ f ∈ SB G, ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧ ∃ f ∈ SB G, Λ f ≠ 0 := by
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_addGroup (hKo.mem_nhds h0)
  letI := measG G
  refine ⟨Lext G, fun f hf a => Lext_translate hf a, K.indicator fun _ => 1, ?_, ?_⟩
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant G ℂ) ⟨hKc.isClosed, hKo⟩).isLocallyConstant,
      HasCompactSupport.intro hKc fun z hz => Set.indicator_of_notMem hz _⟩
  · have hi : Integrable (K.indicator fun _ => (1 : ℂ)) (Measure.addHaar : Measure G) :=
      (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hKc.measure_lt_top.ne)
    rw [Lext_apply _ hi, integral_indicator_const _ hKo.measurableSet]
    have hpos : 0 < (Measure.addHaar : Measure G) K := hKo.measure_pos _ ⟨0, h0⟩
    have : 0 < (Measure.addHaar : Measure G).real K := ENNReal.toReal_pos hpos.ne' hKc.measure_lt_top.ne
    simpa using this.ne'

theorem exists_invariant_form_matrix : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  intro F _ _ v n d
  set O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hOc : IsCompact O := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  have h0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
  set K : Set (Matrix (Fin n) (Fin d) (Fv F v)) := Set.univ.pi fun _ => Set.univ.pi fun _ => O
  exact exists_invariant_form _ K
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc)
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)
    (fun _ _ _ _ => h0)

end GlobalTheory.HaarSB
