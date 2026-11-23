import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure

open Finset
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.LK

open Formalism.REAL (Cas)
open ReciprocityTheory.ChartRestriction.DS

theorem cyclic_vectors_dense : CycDense := by
  intro n ε H _ _ _ σ D E hU hI hK v c hv hc
  have hD : IsDerivedOn ε σ D E :=
    ⟨hK.gl, fun k hk x hx => by
      obtain ⟨S, h1, h2, h3⟩ := (hK.mem x).1 hx
      exact (hK.mem _).2 ⟨S, h1, h3 k hk x h2, h3⟩,
    fun X hX x => by simpa [actM, LinearMap.sum_apply] using hK.real X hX x⟩
  have hre : c = (c.re : ℂ) := by
    have h1 : ⟪Cas E v, v⟫_ℂ = ⟪v, Cas E v⟫_ℂ := by
      simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hK.unit a b, hK.unit b a, ← mul_assoc]
      simp only [Formalism.REAL.sgn, eq_comm (a := ε b)]
      split_ifs <;> simp
    rw [hc, inner_smul_left, inner_smul_right] at h1
    exact (Complex.conj_eq_iff_re.1 (mul_right_cancel₀ (inner_self_ne_zero.2 hv) h1)).symm
  obtain ⟨S, hS, hSt, hvS⟩ := hK.locFin v
  let V : Submodule ℂ D := S ⊓ Cyc E v ⊓ LinearMap.ker (Cas E - c • 1)
  have hVf : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left : V ≤ S)
  have hst := closure_genSub_stable (V := V) (c := c.re) hU hD hVf
    (fun a b h x hx => ⟨⟨hSt a b h x hx.1.1, cyc_stab a b hx.1.2⟩, by
      have h1 : Cas E x - c • x = 0 := hx.2
      have h2 := LinearMap.congr_fun ((Formalism.REAL.casCentral _ n ε E hK.gl).1 a b) x
      simp only [Module.End.mul_apply] at h2
      show Cas E (E a b x) - c • E a b x = 0
      rw [h2, ← map_smul, ← map_sub, h1, map_zero]⟩)
    (fun x hx => by
      have h1 : Cas E x - c • x = 0 := hx.2
      rw [← hre]
      exact sub_eq_zero.1 h1)
  have hvV : v ∈ genSub E V := (le_sInf fun _ hT => hT.1 : V ≤ genSub E V)
    ⟨⟨hvS, mem_cyc.2 ⟨1, by simp⟩⟩, sub_eq_zero.2 hc⟩
  have htop := (hI _ (Submodule.isClosed_topologicalClosure _) hst).resolve_left fun hb => hv (by
    have : (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure :=
      Submodule.le_topologicalClosure _ ⟨v, hvV, rfl⟩
    rw [hb] at this
    exact Subtype.ext this)
  have hle : genSub E V ≤ Cyc E v := sInf_le ⟨inf_le_left.trans inf_le_right, fun a b x hx => cyc_stab a b hx⟩
  exact top_le_iff.1 (htop ▸ Submodule.topologicalClosure_mono (Submodule.map_mono hle))

end CompanionTheory.D.LK
