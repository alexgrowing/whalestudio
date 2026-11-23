import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn.PerfectTrace

open FractionalIdeal

theorem cc_eq_conj (D : D7) (z : D.host.E) : FD.cc z = D.host.conj z := by
  unfold FD.cc
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isIntegral_of_trace (D : D7) (x : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∀ b ∈ D.host.AA,
      ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * D.host.conj b) = z) :
    IsIntegral ℤ x := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    @one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _
  have key : ∀ e ∈ D.host.AA * D.host.AAbar, D.host.xi0 * x * e ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro e he
    refine FractionalIdeal.mul_induction_on (C := fun e => D.host.xi0 * x * e ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) he
      (fun a ha b hb => ?_) (fun u w hu hw => ?_)
    · show D.host.xi0 * x * (a * b) ∈ _
      rw [mem_dual h1ne]
      intro c hc
      rw [mem_one_iff] at hc
      obtain ⟨c, rfl⟩ := hc
      have hca : c • a ∈ D.host.AA := (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      obtain ⟨n, hn⟩ := h _ hca _ (conj_mem_AA D hb)
      rw [conj_conj, Algebra.smul_def] at hn
      rw [Algebra.traceForm_apply, show D.host.xi0 * x * (a * b) * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * x * (algebraMap (𝓞 D.host.E) D.host.E c * a) * b by ring, hn]
      exact ⟨n, eq_intCast (algebraMap ℤ ℚ) _⟩
    · show D.host.xi0 * x * (u + w) ∈ _
      rw [mul_add]
      exact (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).add_mem hu hw
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    conv_lhs => rw [← dual_eq hP D, mul_assoc, ← mul_assoc, spanSingleton_mul_spanSingleton, mul_comm x]
    rw [spanSingleton_mul_le_iff]
    exact key
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  generalize FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = J at hle hJ
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ 1 := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = J⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * J) := by
          rw [mul_comm _ J, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]
      _ ≤ J⁻¹ * J := CovariantClass.elim J⁻¹ hle
      _ = 1 := inv_mul_cancel₀ hJ
  have hx := hle2 (mem_spanSingleton_self _ _)
  obtain ⟨c, rfl⟩ := (mem_one_iff _).1 hx
  exact c.isIntegral_coe

theorem exists_perfect_trace_ideal :
    ∀ (D : D7), ∃ (ξ : D.host.E) (AA : Submodule (𝓞 D.host.E) D.host.E), FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧ AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ D.host.E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  refine ⟨D.host.xi0, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), conj_xi0_alt D, cmHost_imaginaryGenerator_ne_zero hP D,
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (AA_ne_zero hP D)), ?_, fun x => ⟨fun h => ?_, fun hx a ha b hb => ?_⟩⟩
  · intro h
    exact AA_ne_zero hP D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  · refine isIntegral_of_trace D x (fun a ha b hb => ?_)
    rw [← cc_eq_conj]
    exact h a ha b hb
  · have hxa : (⟨x, hx⟩ : 𝓞 D.host.E) • a ∈ D.host.AA :=
      (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha
    have hm : x * a * D.host.conj b ∈ NAA D := mul_mem_mul hxa (conj_mem_AAbar D hb)
    obtain ⟨n, hn⟩ := trace_int_of_mem hP D hm
    refine ⟨n, ?_⟩
    rw [cc_eq_conj, ← hn]
    congr 1; ring

end GlobalTheory.EtaAn.PerfectTrace
