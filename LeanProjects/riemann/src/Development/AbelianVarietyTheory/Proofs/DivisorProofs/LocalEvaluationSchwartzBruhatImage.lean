import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section

namespace GlobalTheory.ThK.PlaneEvSB

variable {F : Type} [Field F] [NumberField F] {n d d₁ : ℕ}

def pr1 {R : Type} (hd : d = d₁ + 2) (y : Fin n × Fin d → R) : Fin n × Fin d₁ → R :=
  fun q => y ((idx hd).symm (Sum.inl q))

def pr2 {R : Type} (hd : d = d₁ + 2) (y : Fin n × Fin d → R) : Fin n × Fin 2 → R :=
  fun q => y ((idx hd).symm (Sum.inr q))

def glue {R : Type} (hd : d = d₁ + 2) (ab : (Fin n × Fin d₁ → R) × (Fin n × Fin 2 → R)) : Fin n × Fin d → R :=
  fun k => Sum.elim ab.1 ab.2 (idx hd k)

section Top

variable {R : Type} [TopologicalSpace R] (hd : d = d₁ + 2)

theorem continuous_first_projection : Continuous (pr1 (n := n) (R := R) hd) := continuous_pi fun _ => continuous_apply _

theorem continuous_second_projection : Continuous (pr2 (n := n) (R := R) hd) := continuous_pi fun _ => continuous_apply _

theorem continuous_glue : Continuous (glue (n := n) (R := R) hd) := by
  refine continuous_pi fun k => ?_
  simp only [glue]
  rcases idx hd k with q | q
  · exact (continuous_apply q).comp continuous_fst
  · exact (continuous_apply q).comp continuous_snd

theorem glue_pr (y : Fin n × Fin d → R) : glue hd (pr1 hd y, pr2 hd y) = y := by
  funext k
  simp only [glue, pr1, pr2]
  rcases h : idx hd k with q | q
  · show y ((idx hd).symm (Sum.inl q)) = y k; rw [← h, Equiv.symm_apply_apply]
  · show y ((idx hd).symm (Sum.inr q)) = y k; rw [← h, Equiv.symm_apply_apply]

end Top

theorem first_projection_insert_zero {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : pr1 hd (ins0 hd x) = x := by
  funext q; simp [pr1]

theorem second_projection_insert_zero {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : pr2 hd (ins0 hd x) = 0 := by
  funext q; simp [pr2]

theorem continuous_insert_zero {R : Type} [TopologicalSpace R] [Zero R] (hd : d = d₁ + 2) :
    Continuous (ins0 (n := n) (R := R) hd) := by
  refine continuous_pi fun k => ?_
  simp only [ins0]
  rcases idx hd k with q | q
  · exact continuous_apply q
  · exact continuous_const

theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem map_ev_SB (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2) (v : Pl F) :
    (SB (Fin n × Fin d → Fv F v)).map (ev hd v) = SB (Fin n × Fin d₁ → Fv F v) := by
  haveI : CompactSpace (v.adicCompletionIntegers F) := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hOc : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 this
  have hOo : IsClopen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isClopen_integer _
  apply le_antisymm
  · rintro _ ⟨φ, ⟨hl, hc⟩, rfl⟩
    have hemb : Topology.IsClosedEmbedding (ins0 (n := n) (R := Fv F v) hd) :=
      Function.LeftInverse.isClosedEmbedding (f := pr1 hd) (fun x => first_projection_insert_zero hd x) (continuous_first_projection hd)
        (continuous_insert_zero hd)
    exact ⟨hl.comp_continuous (continuous_insert_zero hd), hc.comp_isClosedEmbedding hemb⟩
  · intro φ₁ ⟨hl, hc⟩
    set P : Set (Fin n × Fin 2 → Fv F v) := Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) with hP
    have hPc : IsCompact P := isCompact_univ_pi fun _ => hOc
    have hPo : IsClopen P := by
      refine ⟨isClosed_set_pi fun _ _ => hOo.isClosed, ?_⟩
      exact isOpen_set_pi Set.finite_univ fun _ _ => hOo.isOpen
    let φ : (Fin n × Fin d → Fv F v) → ℂ := fun y => φ₁ (pr1 hd y) * P.indicator 1 (pr2 hd y)
    refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
    · exact (hl.comp_continuous (continuous_first_projection hd)).mul
        ((isLocallyConstant_indicator_one hPo).comp_continuous (continuous_second_projection hd))
    · have hK : IsCompact (glue hd '' (tsupport φ₁ ×ˢ P)) := (hc.isCompact.prod hPc).image (continuous_glue hd)
      refine HasCompactSupport.intro' hK hK.isClosed fun y hy => ?_
      by_contra h0
      apply hy
      have h1 : φ₁ (pr1 hd y) ≠ 0 := fun h => h0 (by simp [φ, h])
      have h2 : pr2 hd y ∈ P := by
        by_contra h; exact h0 (by simp [φ, Set.indicator_of_notMem h])
      exact ⟨(pr1 hd y, pr2 hd y), ⟨subset_tsupport _ h1, h2⟩, glue_pr hd y⟩
    · funext x
      have h0 : (0 : Fin n × Fin 2 → Fv F v) ∈ P := fun q _ => (v.adicCompletionIntegers F).zero_mem
      simp [φ, ev_apply, first_projection_insert_zero, second_projection_insert_zero, Set.indicator_of_mem h0]

end GlobalTheory.ThK.PlaneEvSB
