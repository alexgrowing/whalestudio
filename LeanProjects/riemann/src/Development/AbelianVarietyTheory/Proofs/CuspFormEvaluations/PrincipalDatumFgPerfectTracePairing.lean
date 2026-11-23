import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem cc_eq_host_conj (D : D7) (x : D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem principalDatum_trace_perfect : ∀ D : D7, ∃ AA : Submodule (𝓞 D.host.E) D.host.E,
    AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * ReciprocityTheory.ChartRestriction.G.FD.cc b) = z) ↔
        IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hA := AA_ne_zero hP D
  have hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  refine ⟨(D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ?_, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  · intro h0
    exact hA (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  · have h1 : ∀ w ∈ D.host.AA * D.host.AAbar, ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z := by
      intro w hw
      refine FractionalIdeal.mul_induction_on (C := fun w => ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z) hw
        (fun a ha b hb c => ?_) (fun u v hu hv c => ?_)
      · obtain ⟨z, hz⟩ := h (c • a) (Submodule.smul_mem _ c ha) (D.host.conj b) (conj_mem_AA D hb)
        refine ⟨z, ?_⟩
        rw [cc_eq_host_conj, conj_conj] at hz
        rw [← hz, ← smul_mul_assoc, mul_assoc (D.host.xi0 * x)]
      · obtain ⟨z, hz⟩ := hu c
        obtain ⟨z', hz'⟩ := hv c
        refine ⟨z + z', ?_⟩
        rw [smul_add, mul_add, map_add, hz, hz', Int.cast_add]
    have h2 : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) := by
      rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ hone)]
      intro a ha
      rw [← dual_eq hP D, mul_assoc, FractionalIdeal.mem_singleton_mul] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨z, hz⟩ := h1 w hw 1
      rw [one_smul] at hz
      refine ⟨z, ?_⟩
      rw [Algebra.traceForm_apply, ← mul_assoc, mul_comm x, hz]
      exact eq_intCast _ _
    rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h2
    obtain ⟨c, rfl⟩ := h2
    exact c.isIntegral_coe
  · intro a ha b hb
    have hm : (⟨x, h⟩ : 𝓞 D.host.E) • (a * D.host.conj b) ∈ NAA D :=
      Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
    obtain ⟨z, hz⟩ := trace_int_of_mem hP D hm
    refine ⟨z, ?_⟩
    rw [← hz, cc_eq_host_conj, Algebra.smul_def]
    congr 1
    change _ = D.host.xi0 * (x * (a * D.host.conj b))
    ring

end GlobalTheory
