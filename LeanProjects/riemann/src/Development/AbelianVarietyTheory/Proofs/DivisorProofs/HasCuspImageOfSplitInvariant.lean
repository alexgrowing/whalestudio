import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped InnerProductSpace

namespace GlobalTheory.CuspQuot

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem hasCuspImage_of_disjoint (π : CuspSub E a) {N : Submodule ℂ (Sm E a)} (hN : IsStable N) (hd : Disjoint N π.V)
    {f ψ : Sm E a} (hψ : ψ ∈ π.V) (h0 : ψ ≠ 0) (hf : f - ψ ∈ N) : HasCuspImage f := by
  obtain ⟨C, hC, hc⟩ := hd.exists_isCompl
  let p := π.V.projectionOnto C hc.symm
  have hp : ∀ (x : π.V) n, n ∈ N → p (x.1 + n) = x := fun x n hn => by
    rw [map_add, Submodule.projectionOnto_apply_left, (Submodule.projectionOnto_apply_eq_zero_iff _).2 (hC hn), add_zero]
  refine ⟨π.V ⊔ N, π, p, Submodule.mem_sup.2 ⟨ψ, hψ, _, hf, add_sub_cancel _ _⟩, fun o g hg => ?_, ?_, fun o g hg => ?_⟩
  · obtain ⟨x, hx, n, hn, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add]
    exact Submodule.add_mem_sup (π.stable o x hx) (hN o n hn)
  · rw [← add_sub_cancel ψ f, hp ⟨ψ, hψ⟩ _ hf]
    exact fun e => h0 (congrArg Subtype.val e)
  · obtain ⟨x, hx, n, hn, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add, hp ⟨x, hx⟩ n hn]
    exact hp (π.op o ⟨x, hx⟩) _ (hN o n hn)

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isKFinL2_toL2 {φ : Sm E a} (h : IsAutForm φ) (hm : MemL2Quotient (latticeGL E a) μ φ.1) : IsKFinL2 μ hm.toL2 := by
  constructor
  · let T : Subgroup (GL (Fin a) (Af E)) :=
      (MulAction.stabilizer (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ)ˣ hm.toL2).comap
        ((R (latticeGL E a) μ).toHomUnits.comp (finGL E a))
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (h.level.mem_nhds (by simp)) fun k hk => ?_)
    refine (right_translate_toL2 hm _).trans (((hm.mul_right _).toL2_eq_iff_ae_eq hm).2 (.of_forall fun g => ?_))
    exact congrFun (congrArg Subtype.val hk) g
  · have := h.kfin
    have hV : ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ), MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hm.mul_right _
      | zero => exact ⟨fun _ _ _ => rfl, MemLp.zero⟩
      | add x y _ _ hx hy => exact ⟨fun γ hγ g => congrArg₂ (· + ·) (hx.1 γ hγ g) (hy.1 γ hγ g), hx.2.add hy.2⟩
      | smul c x _ hx => exact ⟨fun γ hγ g => congrArg (c • ·) (hx.1 γ hγ g), hx.2.const_smul c⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (toL2ₗ μ _ hV)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨_, Submodule.subset_span ⟨k, rfl⟩⟩, (right_translate_toL2 hm _).symm⟩

theorem isKFinL2_map {P : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ}
    (hP : ∀ g F, P (R (latticeGL E a) μ g F) = R (latticeGL E a) μ g (P F)) {F : L2 (latticeGL E a) μ}
    (h : IsKFinL2 μ F) : IsKFinL2 μ (P F) := by
  constructor
  · let T : Subgroup (GL (Fin a) (Af E)) :=
      (MulAction.stabilizer (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ)ˣ (P F)).comap
        ((R (latticeGL E a) μ).toHomUnits.comp (finGL E a))
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (h.1.mem_nhds (by simp)) fun k hk => ?_)
    exact (hP _ F).symm.trans (congrArg P hk)
  · have := h.2
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : Kinf E a =>
      R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)).map P.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, hP _ F⟩

theorem hasCuspImage_of_splitInvariant (hP : GlobalTheory.Published.CuspidalSpectrumGL) {φ : Sm E a} (h : IsCuspForm φ) (hne : φ ≠ 0)
    (hi : ∀ (t : ℝ) g, φ.1 (splitCentre E a t * g) = φ.1 g) : HasCuspImage φ := by
  let μ : Measure (GA E a) := Measure.haar
  obtain ⟨_, _⟩ := GlobalTheory.CovolGL.finvol E a μ
  have hc := mem_cuspCont_of_isCuspForm h hi
  obtain ⟨C, hC⟩ := hP.2.2.of_invariant h hi
  have hl := leftInv_of_mem_cuspCont hc
  have hm : MemL2Quotient (latticeGL E a) μ φ.1 := memL2_of_bound hc.1 hl hC
  have h0 : hm.toL2 ≠ 0 := toL2_ne_zero hm hc.1 fun e => hne (Subtype.ext e)
  obtain ⟨ι, W, hW, hs⟩ := (hP.1 E a μ).1
  obtain ⟨i, y, hy, hyi⟩ : ∃ i, ∃ y ∈ W i, ⟪y, (⟨hm.toL2, toL2_mem_cuspidal hm hc⟩ : L2cusp μ)⟫_ℂ ≠ 0 := by
    by_contra! h
    exact h0 (congrArg Subtype.val (GlobalTheory.DiscreteSum.eq_zero_of_isHilbertSum hs h))
  obtain ⟨π, hπ⟩ := hP.2.1.of_Rcusp (hW i)
  have hH := (isIrredSubrep_map (hW i)).1
  have hy' : y.1 ∈ (W i).map (L2cusp μ).subtype := ⟨y, hy, rfl⟩
  generalize (W i).map (L2cusp μ).subtype = H at hπ hH hy'
  have := hH.completeSpace
  have hu := isUnitaryRep_R (latticeGL E a) μ
  have hV : ∀ ψ ∈ π.V, Continuous ψ.1 ∧ LeftInv (latticeGL E a) ψ.1 ∧ ∃ C : ℝ, ∀ g, ‖ψ.1 g‖ ≤ C := fun ψ hψ =>
    have h1 := mem_cuspCont_of_isCuspForm (π.cusp ψ hψ) (hπ.normalised ψ hψ)
    ⟨h1.1, leftInv_of_mem_cuspCont h1, hP.2.2.of_invariant (π.cusp ψ hψ) (hπ.normalised ψ hψ)⟩
  obtain ⟨ψ, hψ, e⟩ := hπ.kfin _ (H.starProjection_apply_mem hm.toL2)
    (isKFinL2_map (hH.starProjection_apply hu) (isKFinL2_toL2 h.1 hm))
  obtain ⟨p1, p2, C', p3⟩ := hV ψ hψ
  refine hasCuspImage_of_disjoint π (isStable_weakIn (hH.orthogonal hu)) (Submodule.disjoint_def.2 fun x h1 h2 => ?_) hψ
    (fun e0 => hyi ?_) ?_
  · obtain ⟨q1, q2, C, q3⟩ := hV x h2
    exact eq_zero_of_mem_weakIn q1 q3 (mem_weakIn hH q1 q2 q3
      (hπ.classes_le (toL2_mem_classes h2 (hπ.finitePartMemL2 x h2))) (hπ.finitePartMemL2 x h2).lift_toL2_ae_eq) h1
  · subst e0
    have e1 : H.starProjection hm.toL2 = 0 :=
      l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (Filter.EventuallyEq.symm (ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _))))
    exact (Submodule.starProjection_apply_eq_zero_iff _).1 e1 y.1 hy'
  · exact mem_weakIn (C := C + C') (hH.orthogonal hu) (hc.1.sub p1)
      (fun γ hγ g => congrArg₂ (· - ·) (hl γ hγ g) (p2 γ hγ g))
      (fun g => (norm_sub_le _ _).trans (add_le_add (hC g) (p3 g))) (H.sub_starProjection_mem_orthogonal hm.toL2)
      (Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_sub _ _)) (hm.lift_toL2_ae_eq.sub e))

theorem exists_cuspSub_map : GlobalTheory.Published.CuspidalSpectrumGL →
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ) (f : GlobalTheory.CuspRep.Sm E d),
    GlobalTheory.CuspRep.IsCuspForm f → f ≠ 0 →
    ∃ (W : Submodule ℂ (GlobalTheory.CuspRep.Sm E d)) (τ : GlobalTheory.CuspRep.CuspSub E d) (p : GlobalTheory.CuspRep.Sm E d →ₗ[ℂ] τ.V),
      f ∈ W ∧ GlobalTheory.CuspRep.IsStable W ∧ p f ≠ 0 ∧
      ∀ (o : GlobalTheory.CuspRep.Op E d), ∀ g ∈ W, p (GlobalTheory.CuspRep.act o g) = τ.op o (p g) :=
  fun hP _ _ _ _ _ _ h h0 => hasCuspImage_of_invariant (fun _ => hasCuspImage_of_splitInvariant hP) h h0

end GlobalTheory.CuspQuot

end
