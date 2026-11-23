import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev tfL2n (ε : Fin n → Bool) : Type := PiLp 2 (fun _ : Fin n => L2 ε)

def tfRdiag (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : tfL2n ε →L[ℂ] tfL2n ε :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun c => rreg ε g ∘L ContinuousLinearMap.proj c) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).toContinuousLinearMap

theorem tfRdiag_apply (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (v : tfL2n ε) (c : Fin n) :
    tfRdiag ε g v c = rreg ε g (v c) := rfl

theorem vectorL2_ext {ε : Fin n → Bool} {v w : tfL2n ε} (h : ∀ c, v c = w c) : v = w := by
  apply WithLp.ofLp_injective
  funext c
  exact h c

theorem tfRdiag_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (tfRdiag ε) := by
  have hr := rreg_isURepOn ε
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun v => vectorL2_ext fun c => ?_
    rw [tfRdiag_apply, hr.1.1]; rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun v => vectorL2_ext fun c => ?_
    rw [tfRdiag_apply, hr.1.2 a ha b hb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      tfRdiag_apply, tfRdiag_apply]
  · intro g hg v
    have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => L2 ε) (tfRdiag ε g v)
    have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => L2 ε) v
    simp only [tfRdiag_apply, hr.2.1 g hg] at h1
    rw [← h2] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
  · intro v
    have e : (fun g => tfRdiag ε g v) =
        fun g => (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm (fun c => rreg ε g (v c)) := rfl
    rw [e]
    exact (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous.comp_continuousOn
      (continuousOn_pi.2 fun c => hr.2.2 _)

theorem tfRdiag_smooth {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε)) :
    v ∈ smD ε (tfRdiag ε) := by
  rw [mem_smD_iff]
  have hc : ∀ c, S7.SmoothOnGV ε (fun g => rreg ε g (v c)) := fun c => (mem_smD_iff ε (rreg ε) _).1 (hv c)
  intro g₀ hg₀
  choose U F hU hg hF hEq using fun c => hc c g₀ hg₀
  refine ⟨⋂ c, U c, fun g => WithLp.toLp 2 (fun c => F c g), isOpen_iInter_of_finite hU,
    Set.mem_iInter.2 hg, ?_, ?_⟩
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => L2 ε)).symm.contDiff.comp_contDiffOn
      (contDiffOn_pi.2 fun c => (hF c).mono (Set.iInter_subset _ c))
  · intro g hgU hgJ
    refine vectorL2_ext fun c => ?_
    exact hEq c g (Set.mem_iInter.1 hgU c) hgJ

theorem tfRdiag_hasDerivAt {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => tfRdiag ε (NormedSpace.exp ((t : ℂ) • X)) v)
      (WithLp.toLp 2 (fun c => dS (rreg ε) X (v c))) 0 := by
  have hd : ∀ c, HasDerivAt (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (v c))
      (dS (rreg ε) X (v c)) 0 := by
    intro c
    have h := (isDerivedOn_smE (rreg_isURepOn ε)).deriv X hX ⟨v c, hv c⟩
    rw [dS_eq_actM (isDerivedOn_smE (rreg_isURepOn ε)) hX ⟨v c, hv c⟩]
    exact h
  have hp : HasDerivAt (fun t : ℝ => fun c => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (v c))
      (fun c => dS (rreg ε) X (v c)) 0 := hasDerivAt_pi.2 hd
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => L2 ε)).symm.hasFDerivAt.comp_hasDerivAt 0 hp

theorem tfRdiag_dS {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (c : Fin n) :
    dS (tfRdiag ε) X v c = dS (rreg ε) X (v c) := by
  have h := (tfRdiag_hasDerivAt hv hX).deriv
  have h2 := congrArg (fun w : tfL2n ε => w c) h
  exact h2

theorem tfRdiag_smE {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε)) (a b c : Fin n) :
    ((smE ε (tfRdiag ε) a b ⟨v, tfRdiag_smooth hv⟩ : smD ε (tfRdiag ε)) : tfL2n ε) c =
      ((smE ε (rreg ε) a b ⟨v c, hv c⟩ : smD ε (rreg ε)) : L2 ε) := by
  rw [smE_apply (tfRdiag_isURepOn ε), smE_apply (rreg_isURepOn ε)]
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [tfRdiag_dS hv (SmDerA.inG_cpart1 ε _), tfRdiag_dS hv (SmDerA.inG_cpart2 ε _)]

def tfJ (ε : Fin n → Bool) : tfL2n ε →L[ℂ] tfL2n ε :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun c => tfSgn ε c • ContinuousLinearMap.proj c) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).toContinuousLinearMap

theorem tfJ_apply (ε : Fin n → Bool) (v : tfL2n ε) (c : Fin n) : tfJ ε v c = tfSgn ε c • v c := rfl

theorem tfRdiag_tfJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (v : tfL2n ε) :
    tfRdiag ε g (tfJ ε v) = tfJ ε (tfRdiag ε g v) :=
  vectorL2_ext fun c => by rw [tfRdiag_apply, tfJ_apply, tfJ_apply, tfRdiag_apply, map_smul]

theorem toL2_congr_of_eq_on_UJset {ε : Fin n → Bool} {F F' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = F' g) : toL2 ε F = toL2 ε F' := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => F' (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (umat_mem_UJset ε g)
  unfold toL2
  simp only [e]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (e ▸ h1) h2
  · exact absurd (e.symm ▸ h2) h1
  · rfl

section Ph

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tfPh (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H)
    (ζ : Fin n → H) : tfL2n ε :=
  WithLp.toLp 2 (fun c => toL2 ε (coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ))

theorem tfPh_apply (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H)
    (ζ : Fin n → H) (c : Fin n) :
    tfPh dual ε σ y ζ c = toL2 ε (coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ) := rfl

end Ph

end ReciprocityTheory.ChartRestriction.DS
