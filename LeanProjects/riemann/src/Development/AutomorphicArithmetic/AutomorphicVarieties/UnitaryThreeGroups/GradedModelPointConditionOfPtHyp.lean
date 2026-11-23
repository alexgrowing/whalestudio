import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelSigns
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  classical
  haveI := c.dvr
  haveI := c.fin
  by_cases h0 : b = 0
  · subst h0
    simp
  have key := UpperTheory.V.Base.normO l c.O b h0
  have hv0 : IsDiscreteValuationRing.addVal c.O b ≠ 0 := fun h =>
    hb ((IsDiscreteValuationRing.addVal_eq_zero_iff).1 h)
  have hvt : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := fun h =>
    h0 ((IsDiscreteValuationRing.addVal_eq_top_iff).1 h)
  have hn : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    intro h
    rw [ENat.toNat_eq_zero] at h
    tauto
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hn
  rw [← key] at hr
  by_cases he : (UpperTheory.V.Base.eO l c.O).toNat = 0
  · rw [he, pow_zero] at hr
    exact absurd hr (lt_irrefl 1)
  · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 hr

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  refine norm_lt_one_of_nonunit c (x y) fun hu => ?_
  have h2 : IsUnit (y - algebraMap c.O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap c.O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem hom_ext_gr {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] [CommRing K] [Algebra O K] (ξ ξ' : A →ₐ[O] K) (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  refine AlgHom.ext fun f => ?_
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem UpperTheory.V.U3.gradedModel_pointCondition_of_ptHyp :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      M2 M.𝒜 M.Q.ideal → PtHyp η S.r.hom M.x₀ → M3 M.𝒜 (PadicAlgCl l) M.x M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hm h2 hpt
  intro x₁ hS hN hP hne
  exfalso
  apply hne
  obtain ⟨t, f, hf, hact⟩ := M.pts h2 x₁ hS
  have sg := model_signs S M hl hm f hf
  have hN' : NegZero M.𝒜 (f.comp M.q) := by
    intro j hj a ha
    rw [← hact, act_of_mem _ _ _ ha, hN j hj a ha, mul_zero]
  have hP' : PosZero M.𝒜 (f.comp M.q) := by
    intro j hj a ha
    rw [← hact, act_of_mem _ _ _ ha, hP j hj a ha, mul_zero]
  have hfix := hpt.fixed f hf (sg.1.1 hN') (sg.2.1.1 hP')
  have hb : IsLocPt (toBar M.x₀) := isLocPt_toBar M.x₀
  have hconj : push (toBar M.x₀) S.r.hom = conjBy ((tor (PadicAlgCl l)) 1) (push f S.r.hom) := by
    rw [hfix]
    ext g : 1
    simp [conjBy]
  have heq := sg.2.2 (toBar M.x₀) hb 1 hconj
  apply hom_ext_gr M.𝒜
  intro j a ha
  by_cases hj : j = 0
  · subst hj
    have e1 := congrArg (fun φ => φ a) hact
    have e2 := congrArg (fun φ => φ a) heq
    simp only [act_of_mem _ _ _ ha] at e1 e2
    simp at e1 e2
    rw [← M.x₀_q]
    simp
    rw [e1, e2]
  · rcases lt_or_gt_of_ne hj with h | h
    · rw [hN j h a ha, AlgHom.comp_apply, M.wring.fixed j hj a ha, map_zero]
    · rw [hP j h a ha, AlgHom.comp_apply, M.wring.fixed j hj a ha, map_zero]
