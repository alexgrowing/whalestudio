import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tst_trM (D : Dom E n 0) {ι : Type} [Fintype ι] {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ)
    (M : Matrix ι ι ℂ) : PositivityTheory.Rg.BcB.E1.Tst (G := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).G) (trM Φ M) := by
  have h := (PositivityTheory.Rg.BcB.E1.kerLin (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) (ι × ι)
    (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
    funext y
    rw [Fintype.sum_prod_type]
    rfl
  rw [e]
  exact h

private theorem cusp_projection_self (D : Dom E n 0) (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) {w : ℝ → ℂ}
    (hw : Continuous w) (hws : HasCompactSupport w) (v : Lp ℂ 2 D.ν)
    (hv : (v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * w (ldet x)) : P0 D π v = v := by
  have hvec : IsPiVec D π (vecM v fun _ : Unit => (1 : ℂ)) := fun _ => ⟨ψ, hψ, w, hw, hws, by
    have e : (vecM v fun _ : Unit => (1 : ℂ)) () = v := one_smul ℂ v
    simpa [e] using hv⟩
  have hmem : (vecM v fun _ : Unit => (1 : ℂ)) ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hvec)
  unfold P0
  rw [Submodule.starProjection_eq_self_iff.2 hmem]
  exact one_smul ℂ v

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rep_pf :
    Basic → ThetaInt → KInv → PDiag → Ker → Rep := by
  intro hB hTI hK _ hKer E _ _ _ n ι _ s m ψ hψ u hu hus x₀
  obtain ⟨-, bMul, -, -, -, -, bThL, bThTh, bThMul, bRat, -, -⟩ := hB E n s.pos
  obtain ⟨ψ₁, hψ₁, hψe⟩ := s.fix.2 ψ hψ
  have hw : Continuous fun t : ℝ => u (-t) := hu.comp continuous_neg
  have hws : HasCompactSupport fun t : ℝ => u (-t) := hus.comp_homeomorph (Homeomorph.neg ℝ)
  set f : H E n 0 → ℂ := fun x => ψ₁.1 x.1 * u (-ldet x) with hf
  have hmem : MemLp f 2 s.D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n s.pos s.D s.π s.fix ψ₁ hψ₁ _ hw hws).1
  set v : Lp ℂ 2 s.D.ν := hmem.toLp f with hvdef
  have hv : (v : H E n 0 → ℂ) =ᵐ[s.D.ν] f := hmem.coeFn_toLp
  have hP : P0 s.D s.π v = v := cusp_projection_self s.D s.π hψ₁ hw hws v hv
  obtain ⟨kI, kE⟩ := hKer E n ι s m v x₀
  rw [hP] at kE
  have hψinv : ∀ (γ : ratH E n 0) (y : H E n 0), ψ₁.1 ((γ : H E n 0) * y).1 = ψ₁.1 y.1 := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp ψ₁ hψ₁).1.left γ₁ y.1
  have hfinv : ∀ (γ : ratH E n 0) (y : H E n 0), f ((γ : H E n 0) * y) = f y := by
    intro γ y
    simp only [hf]
    rw [hψinv γ y, bMul, (bRat γ).1, zero_add]
  have hGinv : ∀ (γ : ratH E n 0) (y : H E n 0), m.G x₀ (th ((γ : H E n 0) * y)) = m.G x₀ (th y) := by
    intro γ y
    have h2 := hK E n ι s |>.2 ⟨th (γ : H E n 0), (bRat γ).2⟩ (th y)
    simp only [Mid.G, Gk]
    rw [bThMul, h2]
  set F : H E n 0 → ℂ := fun y => f y * m.G x₀ (th y) with hF
  have hFinv : Inv F := fun γ y => by
    simp only [hF]
    rw [hfinv, hGinv]
  have hFint : Integrable F s.D.ν := kI.congr (hv.mono fun y hy => by simp only [hF, hy])
  obtain ⟨tI, tE⟩ := hTI E n s.D F hFinv hFint
  have hFth : ∀ x, F (th x) = ψ.1 x.1 * m.G x₀ x * u (ldet x) := by
    intro x
    have h1 : ψ₁.1 (th x).1 = ψ.1 x.1 := by
      have e : thetaA E n (th x).1 = x.1 := congrArg Prod.fst (bThTh x)
      rw [hψe, e]
    simp only [hF, hf]
    rw [h1, bThL, neg_neg, bThTh]
    ring
  refine ⟨tI.congr (Filter.Eventually.of_forall hFth), ?_⟩
  have hμl : s.D.μ.IsMulLeftInvariant := s.D.haar.1
  haveI hmm : MeasurableMul (H E n 0) :=
    (inferInstance : MeasurableMul (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D).G)
  have hun := (DiscreteGroups.T1.G.unfold (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D)
    PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (tst_trM s.D m.t s.M) (f := f) hfinv hmem x₀).2
  have hun' : ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun
  calc ∫ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) ∂s.D.ν
      = ∫ x, F (th x) ∂s.D.ν := integral_congr_ae (Filter.Eventually.of_forall fun x => (hFth x).symm)
    _ = ∫ x, F x ∂s.D.ν := tE
    _ = ∫ y, (v : H E n 0 → ℂ) y * m.G x₀ (th y) ∂s.D.ν :=
        integral_congr_ae (hv.mono fun y hy => by simp only [hF, hy])
    _ = ∫ y, kerH m.φ x₀ y * (v : H E n 0 → ℂ) y ∂s.D.ν := kE
    _ = ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν := integral_congr_ae (hv.mono fun y hy => by simp only [hy])
    _ = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun'
    _ = ∫ z, m.φ (x₀⁻¹ * (x₀ * z)) * f (x₀ * z) ∂s.D.μ :=
        (integral_mul_left_eq_self (fun y => m.φ (x₀⁻¹ * y) * f y) x₀).symm
    _ = ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(ldet x₀ + ldet z)) ∂s.D.μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hf]
        rw [inv_mul_cancel_left, bMul, Prod.fst_mul, hψe]
        ring

end
