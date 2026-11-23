import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private def evAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) (x : H E n 0) :
    π.V →ₗ[ℂ] ℂ where
  toFun ψ := ψ.1.1 x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finFac_pf :
    Basic → EvalBasis → FinGen → FinFac := by
  intro hB hE hG E _ _ _ n ι _ s
  obtain ⟨hl, hmul, -⟩ := hB E n s.pos
  obtain ⟨W, hWV, hWf, hW⟩ := hG E n ι s
  have sep : ∀ ψ : s.π.V, (∀ x : {x : H E n 0 // ldet x = 0}, evAt s.π x.1 ψ = 0) → ψ = 0 := by
    intro ψ h
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have hy : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hl]; ring
    have h0 := h ⟨_, hy⟩
    have h1 := s.fix.1 ψ.1 ψ.2 (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) g
    exact h1.symm.trans h0
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨d, xs, ws, hw, hrep⟩ := hE {x : H E n 0 // ldet x = 0} s.π.V (fun x => evAt s.π x.1) sep
    (LinearMap.range (Submodule.inclusion hWV)) inferInstance
  refine ⟨{ B := Fin d, w := fun b => (ws b).1, x := fun b => (xs b).1, mem := fun b => (ws b).2,
            zero := fun b => (xs b).2 }, ?_⟩
  have key : ∀ v : Hs (ι := ι) s.D, IsPiVec s.D s.π v → ∀ (x : H E n 0) (i : ι),
      inner ℂ (s.k₁ x i) v =
        ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v := by
    intro v hv x i
    obtain ⟨ψ, hψ, hval⟩ := hW v hv i (ldet x)
    have hb : ∀ b, inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v = ψ.1 (xs b).1.1 := by
      intro b
      rw [hval _ (by rw [hmul, hl, (xs b).2, add_zero])]
      exact s.fix.1 ψ (hWV hψ) _ _
    have hr := congrArg (evAt s.π x) (hrep ⟨ψ, hWV hψ⟩ ⟨⟨ψ, hψ⟩, rfl⟩)
    rw [map_sum] at hr
    rw [hval x rfl]
    refine hr.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul, hb b, smul_eq_mul, mul_comm]
    rfl
  intro v hv x i
  let L : Hs (ι := ι) s.D →L[ℂ] ℂ := innerSL ℂ (s.k₁ x i) -
    ∑ b, (ws b).1.1 x.1 • innerSL ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i)
  have hL : ∀ f, L f = inner ℂ (s.k₁ x i) f -
      ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) f := by
    intro f
    simp [L, ContinuousLinearMap.sum_apply]
  have hle : Submodule.span ℂ {f | IsPiVec s.D s.π f} ≤ LinearMap.ker (L : Hs (ι := ι) s.D →ₗ[ℂ] ℂ) :=
    Submodule.span_le.2 fun f hf => by
      have := key f hf x i
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [hL, this, sub_self]
  have hv' : v ∈ closure ((Submodule.span ℂ {f | IsPiVec s.D s.π f} : Submodule ℂ (Hs (ι := ι) s.D)) : Set (Hs (ι := ι) s.D)) := hv
  have h0 : L v = 0 :=
    closure_minimal (t := {f | L f = 0}) (fun f hf => LinearMap.mem_ker.1 (hle hf))
      (isClosed_eq L.continuous continuous_const) hv'
  rw [hL] at h0
  exact sub_eq_zero.1 h0

end
