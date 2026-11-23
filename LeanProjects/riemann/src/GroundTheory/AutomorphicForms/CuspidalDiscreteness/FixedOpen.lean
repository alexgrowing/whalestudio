import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform

open MeasureTheory Set Filter Topology Function Module

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace BanachRep

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [CompactSpace L]
  [TotallyDisconnectedSpace L] [T2Space L]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def fixedIn (σ : BanachRep L E) (W : Submodule ℂ E) (U : Subgroup L) : Submodule ℂ E where
  carrier := {w | w ∈ W ∧ ∀ u ∈ U, σ u w = w}
  add_mem' := fun {a b} ha hb =>
    ⟨W.add_mem ha.1 hb.1, fun u hu => by rw [map_add, ha.2 u hu, hb.2 u hu]⟩
  zero_mem' := ⟨W.zero_mem, fun u _ => map_zero _⟩
  smul_mem' := fun c w hw => ⟨W.smul_mem c hw.1, fun u hu => by rw [map_smul, hw.2 u hu]⟩

theorem exists_isOpen_forall_eq_of_finiteDimensional (σ : BanachRep L E) (v : E)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g : L => σ g v))) :
    ∃ U : Subgroup L, IsOpen (U : Set L) ∧ ∀ u ∈ U, σ u v = v := by
  classical
  let _ : MeasurableSpace L := borel L
  have _ : BorelSpace L := ⟨rfl⟩
  set W := Submodule.span ℂ (Set.range fun g : L => σ g v) with hWdef
  have hWc : IsClosed (W : Set E) := Submodule.closed_of_finiteDimensional W
  have hσW : ∀ g, σ g v ∈ W := fun g => Submodule.subset_span ⟨g, rfl⟩
  set F : Subgroup L → Submodule ℂ E := fun U => fixedIn σ W U with hFdef
  have hFle : ∀ U, F U ≤ W := fun U w hw => hw.1
  have hFfin : ∀ U, FiniteDimensional ℂ (F U) := fun U => Submodule.finiteDimensional_of_le (hFle U)
  have hFanti : ∀ {U V : Subgroup L}, U ≤ V → F V ≤ F U :=
    fun hUV w hw => ⟨hw.1, fun u hu => hw.2 u (hUV hu)⟩

  set S : Set ℕ := {d | ∃ U : Subgroup L, IsOpen (U : Set L) ∧ finrank ℂ (F U) = d} with hSdef
  have hSne : S.Nonempty := ⟨_, ⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨finrank ℂ W, ?_⟩
    rintro _ ⟨U, -, rfl⟩
    exact Submodule.finrank_mono (hFle U)
  obtain ⟨U₀, hU₀, hU₀d⟩ := Nat.sSup_mem hSne hSbdd
  have hmax : ∀ U : Subgroup L, IsOpen (U : Set L) → finrank ℂ (F U) ≤ finrank ℂ (F U₀) :=
    fun U hU => hU₀d ▸ le_csSup hSbdd ⟨U, hU, rfl⟩
  have hstab : ∀ U : Subgroup L, IsOpen (U : Set L) → U ≤ U₀ → F U = F U₀ := by
    intro U hU hle
    have _ := hFfin U
    exact (Submodule.eq_of_le_of_finrank_le (hFanti hle) (hmax U hU)).symm
  have _ := hFfin U₀
  have hclosed : IsClosed (F U₀ : Set E) := Submodule.closed_of_finiteDimensional (F U₀)

  have hvF : v ∈ F U₀ := by
    change v ∈ (F U₀ : Set E)
    rw [← hclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hN : IsOpen ({g : L | ‖σ g v - v‖ < ε / 2} ∩ (U₀ : Set L)) :=
      (isOpen_lt ((σ.continuous_orbit v).sub continuous_const).norm continuous_const).inter hU₀
    have h1N : (1 : L) ∈ {g : L | ‖σ g v - v‖ < ε / 2} ∩ (U₀ : Set L) :=
      ⟨by simp [half_pos hε], U₀.one_mem⟩
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN h1N
    set U : Subgroup L := H.toOpenSubgroup.toSubgroup with hUdef
    have hU : IsOpen (U : Set L) := H.toOpenSubgroup.isOpen
    have hUU₀ : U ≤ U₀ := fun u hu => (hH hu).2
    have hUN : ∀ u ∈ U, ‖σ u v - v‖ < ε / 2 := fun u hu => (hH hu).1
    have _ : CompactSpace U := isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hU).isCompact
    set ρ : Measure U := CuspidalSpectrum.haarProb U with hρ
    have hcont : Continuous fun u : U => σ (u : L) v :=
      (σ.continuous_orbit v).comp continuous_subtype_val
    have hint : Integrable (fun u : U => σ (u : L) v) ρ :=
      integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
    set e : E := ∫ u : U, σ (u : L) v ∂ρ with hedef
    have heW : e ∈ W :=
      Convex.integral_mem (W.restrictScalars ℝ).convex hWc (ae_of_all _ fun u => hσW u) hint
    have hefix : ∀ u ∈ U, σ u e = e := by
      intro u hu
      rw [hedef, ← (σ u).integral_comp_comm hint]
      have := integral_mul_left_eq_self (μ := ρ) (fun x : U => σ (x : L) v) ⟨u, hu⟩
      rw [← this]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [Subgroup.coe_mul]
      rw [map_mul_apply]
    have heF : e ∈ F U₀ := by
      rw [← hstab U hU hUU₀]
      exact ⟨heW, hefix⟩
    refine ⟨e, heF, ?_⟩
    have hdiff : e - v = ∫ u : U, (σ (u : L) v - v) ∂ρ := by
      rw [integral_sub hint (integrable_const v), integral_const, probReal_univ, one_smul]
    rw [dist_comm, dist_eq_norm, hdiff]
    calc ‖∫ u : U, (σ (u : L) v - v) ∂ρ‖ ≤ ε / 2 * ρ.real univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun u => (hUN u u.2).le)
      _ = ε / 2 := by rw [probReal_univ, mul_one]
      _ < ε := half_lt_self hε
  exact ⟨U₀, hU₀, fun u hu => hvF.2 u hu⟩

end BanachRep

namespace UnitaryRep

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [CompactSpace L]
  [TotallyDisconnectedSpace L] [T2Space L]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_isOpen_forall_eq_of_finiteDimensional (σ : UnitaryRep L H) (v : H)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g : L => σ g v))) :
    ∃ U : Subgroup L, IsOpen (U : Set L) ∧ ∀ u ∈ U, σ u v = v := by
  have e : (Set.range fun g : L => BanachRep.ofUnitary σ g v) = Set.range fun g : L => σ g v := rfl
  rw [← e] at hv
  exact BanachRep.exists_isOpen_forall_eq_of_finiteDimensional (BanachRep.ofUnitary σ) v hv

variable {G : Type*} [Group G] [TopologicalSpace G]

def comapHom (σ : UnitaryRep G H) (f : L →* G) (hf : Continuous f) : UnitaryRep L H where
  toHom := σ.toHom.comp f
  continuous_orbit' v := (σ.continuous_orbit' v).comp hf

end UnitaryRep

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

theorem exists_isOpen_forall_cuspRep_finOne_eq (v : cuspidalL2 μ)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRep μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v))) :
    ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n),
      IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧ ∀ u ∈ U, cuspRep μ (finOne K n u) v = v := by
  have hle : Submodule.span ℂ (Set.range fun u : AdelicGLn.integralFiniteGL K n =>
      (cuspRep μ).comapHom (finOne K n) continuous_finOne u v) ≤
      Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRep μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨⟨finEmb K n u, finEmb_mem_maxCompact u.2⟩, rfl⟩
  have _ := hv
  exact UnitaryRep.exists_isOpen_forall_eq_of_finiteDimensional _ v
    (Submodule.finiteDimensional_of_le hle)

end CuspidalSpectrum

end

end GroundTheory.Automorphic
