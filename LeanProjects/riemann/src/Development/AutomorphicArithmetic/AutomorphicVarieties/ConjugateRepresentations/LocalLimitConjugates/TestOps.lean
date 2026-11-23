import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private def stab (ψ : Sm E a) : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) where
  carrier := {k | rt E a (finGL E a k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_lie (X : Lie E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (lie E a X ψ) := by
  have hle : stab ψ ≤ stab (lie E a X ψ) := fun k hk =>
    (LinearMap.congr_fun (lie_rt_fin X k) ψ).symm.trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem lev_rt (g : GA E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (rt E a g ψ) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E a y * finGL E a l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E a (infGL E a y * finGL E a l) ψ)) (g := 1)
    (mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E a (finGL E a (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E a (finGL E a k) (rt E a (infGL E a y * finGL E a l) ψ) = rt E a (infGL E a y * finGL E a l) ψ
    have e : finGL E a k * (infGL E a y * finGL E a l) = infGL E a y * finGL E a l * finGL E a (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E a y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem supp_lie (X : Lie E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (lie E a X ψ).1 := by
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  refine HasCompactSupport.intro h fun g hg => ?_
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve ψ g c X c0 cder
  have hc : Continuous fun t : ℝ => g * infGL E a (c t) := continuous_const.mul ccont
  have ht : Tendsto (fun t : ℝ => g * infGL E a (c t)) (𝓝 0) (𝓝 g) := by
    simpa [c0] using hc.tendsto 0
  have hz : (fun t : ℝ => ψ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
    ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

private theorem supp_rt (g : GA E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (rt E a g ψ).1 :=
  h.comp_homeomorph (Homeomorph.mulRight g)

end

theorem UpperTheory.V.Cj.H.testOps :
    UpperTheory.V.Cj.H.TestOps := by
  intro E _ _ _ a ψ
  exact ⟨fun h => ⟨ContAut.continuous_of_isOpen_stab E a ψ h, fun X => lev_lie X ψ h, fun g => lev_rt g ψ h⟩,
    fun h => ⟨fun X => ⟨supp_lie X ψ h.1, lev_lie X ψ h.2⟩, fun g => ⟨supp_rt g ψ h.1, lev_rt g ψ h.2⟩⟩⟩
