import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : Dom E n 0} {ι : Type}

private lemma vecM_apply (v : Lp ℂ 2 D.ν) (c : ι → ℂ) (l : ι) : vecM v c l = c l • v := rfl

private lemma vecM_zero (c : ι → ℂ) : vecM (0 : Lp ℂ 2 D.ν) c = 0 := by
  ext1 l
  simp [vecM_apply]

private lemma vecM_add (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a + b) c = vecM a c + vecM b c := by
  ext1 l
  simp [vecM_apply, smul_add]

private lemma vecM_sub (a b : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (a - b) c = vecM a c - vecM b c := by
  ext1 l
  simp [vecM_apply, smul_sub]

private lemma vecM_smul (r : ℂ) (a : Lp ℂ 2 D.ν) (c : ι → ℂ) : vecM (r • a) c = r • vecM a c := by
  ext1 l
  simp [vecM_apply, smul_comm r]

private lemma vecM_unit (f : Hs (ι := Unit) D) : vecM (f ()) (fun _ : Unit => 1) = f := by
  ext1 l
  simp [vecM_apply]

private lemma continuous_vecM [Fintype ι] (c : ι → ℂ) :
    Continuous fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun l => (continuous_const_smul (c l)).comp (PiLp.continuous_apply 2 _ ()))

private lemma isPiVec_vecM (π : CuspSub E n) {f : Hs (ι := Unit) D} (hf : IsPiVec D π f) (c : ι → ℂ) :
    IsPiVec D π (vecM (f ()) c : Hs (ι := ι) D) := by
  intro l
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hf ()
  refine ⟨c l • ψ, π.V.smul_mem _ hψ, u, hu, hc, ?_⟩
  have h1 := Lp.coeFn_smul (c l) (f ())
  filter_upwards [h1, he] with x h1 h2
  rw [vecM_apply, h1, Pi.smul_apply, h2]
  simp [mul_assoc]

private lemma isPiVec_comp (π : CuspSub E n) {g : Hs (ι := ι) D} (hg : IsPiVec D π g) (l : ι) :
    IsPiVec D π (vecM (g l) (fun _ : Unit => 1) : Hs (ι := Unit) D) := by
  intro _
  obtain ⟨ψ, hψ, u, hu, hc, he⟩ := hg l
  refine ⟨ψ, hψ, u, hu, hc, ?_⟩
  simpa [vecM_apply] using he

private lemma vecM_mem [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {f : Hs (ι := Unit) D}
    (hf : f ∈ piSp D π Unit) : (vecM (f ()) c : Hs (ι := ι) D) ∈ piSp D π ι := by
  have hspan : ∀ f ∈ Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f},
      (vecM (f ()) c : Hs (ι := ι) D) ∈ Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (isPiVec_vecM π hx c)
    | zero => simpa [vecM_zero] using Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (x + y) () = x () + y () := rfl
      rw [this, vecM_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (r • x) () = r • x () := rfl
      rw [this, vecM_smul]
      exact Submodule.smul_mem _ _ hx
  have hf' : f ∈ closure (Submodule.span ℂ {f : Hs (ι := Unit) D | IsPiVec D π f} : Set (Hs (ι := Unit) D)) := hf
  have : (vecM (f ()) c : Hs (ι := ι) D) ∈
      closure (Submodule.span ℂ {f : Hs (ι := ι) D | IsPiVec D π f} : Set (Hs (ι := ι) D)) :=
    map_mem_closure (f := fun f : Hs (ι := Unit) D => (vecM (f ()) c : Hs (ι := ι) D))
      (continuous_vecM c) hf' hspan
  exact this

private lemma vecM_orth [Fintype ι] (π : CuspSub E n) (c : ι → ℂ) {w : Lp ℂ 2 D.ν}
    (hw : (vecM w fun _ : Unit => 1 : Hs (ι := Unit) D) ∈ (piSp D π Unit)ᗮ) :
    (vecM w c : Hs (ι := ι) D) ∈ (piSp D π ι)ᗮ := by
  rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h := (Submodule.mem_orthogonal _ _).1 hw _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (isPiVec_comp π hg l)))
    rw [PiLp.inner_apply] at h
    simp only [vecM_apply, one_smul, Finset.univ_unique, Finset.sum_singleton] at h
    rw [vecM_apply, inner_smul_right, h, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pDiag_pf :
    PDiag := by
  intro E _ _ _ n D π ι _ v c
  show _ = vecM ((piSp D π Unit).starProjection (vecM v fun _ : Unit => 1) ()) c
  have hmem := (piSp D π Unit).starProjection_apply_mem (vecM v fun _ : Unit => 1)
  have horth := (piSp D π Unit).sub_starProjection_mem_orthogonal (vecM v fun _ : Unit => 1)
  refine Submodule.eq_starProjection_of_mem_orthogonal (vecM_mem π c hmem) ?_
  rw [← vecM_sub]
  refine vecM_orth π c ?_
  rw [vecM_sub, vecM_unit]
  exact horth

end
