import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd
private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i
private theorem transport_rho {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {n : ℕ} (a : WDRep h W) (b : Basis (Fin n) ℂ W) (σ : ↥(Weil h))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : LinearMap.toMatrix b b (a.ρ σ) = X) :
    (a.transport b.equivFun).ρ σ = Matrix.toLin' X := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := b.equivFun.surjective v
  change b.equivFun (a.ρ σ (b.equivFun.symm (b.equivFun x))) = _
  rw [LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, ← hX]
  exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ σ) x).symm
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Af.weil_deligne_above_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAbove := by
  rintro - F Ω _ _ _ _ _ l _ - ι n M hM m r hr w A h O _ _ _ Bw hj κ ⟨χ, hχ, hfl, hI⟩ hp hor
  have hκc := cont_diag hr hfl
  obtain ⟨L, ρ, κL, χL, hV, e, htri, hκ, hχL⟩ := UpperTheory.galois_representation_model_over_finite_extension F Ω l ι n r w A h O Bw hj κ χ
    (fun i => UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ (hχ i)) hfl hp
  obtain ⟨-, hcyc, hK⟩ := UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj
  obtain ⟨K', hK'⟩ := hK M hM
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => κ i * ε ^ (-m i)
  let μ : ↥(Weil h) → Fin n → ℂ := fun σ i => ((normV w : ℕ) : ℂ) ^ (m i * deg σ) * ι (ψ i (inc σ) : Qbar l)
  have hεc : Continuous fun s => (ε s : Qbar l) := by
    have h0 : Continuous fun g : GQ l => (((Loc.PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
      obtain ⟨hc, -, hq⟩ := Loc.cycFacts l l
      simp only [hq]
      have h0 : Continuous fun g : GQ l => ((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) := Units.continuous_val.comp hc
      exact continuous_subtype_val.comp h0
    exact ((continuous_algebraMap ℚ_[l] (Om l)).comp (h0.comp (continuous_subtype_val.comp Bw.e_cont))).congr
      fun s => hcyc L s
  have hψc : ∀ i, Continuous fun s => (ψ i s : Qbar l) := fun i => by
    refine ((hκc i).mul (hεc.zpow₀ (-m i) fun s => Or.inl (Units.ne_zero _))).congr fun s => ?_
    simp [ψ]
  haveI := hV.finite
  have T := UpperTheory.weilDeligne_triangularizable F Ω l ι w A h O Bw hj L n _ ρ κL μ htri (fun i hi σ y => by
    refine (UpperTheory.cyclotomicWeilChar_properties F Ω l ι w A h O Bw hj L (κL i) (χL i) (m i) ?_ ⟨K', fun g hg => ?_⟩ (fun g hg => ?_) hi σ y).trans ?_
    · refine ((hκc i).comp Bw.e_symm_cont).congr fun g => ?_
      rw [Function.comp_apply, ← hκ, MulEquiv.apply_symm_apply]
    · obtain ⟨s, rfl⟩ := Bw.e.surjective g
      refine Units.ext (Subtype.ext ?_)
      rw [hχL, hχ i s (hK' s hg)]
      rfl
    · obtain ⟨s, rfl⟩ := GlobalTheory.PstLaws.exists_ine_of_fix Bw h hj g hg
      refine Units.ext (Subtype.ext ?_)
      have h1 := congrArg Units.val (hI i (inc (ineIncl h s)) s.2)
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, ← hκ, ← hχL, ← hcyc L] at h1
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      exact h1.trans (by congr 1)
    · congr 3
      have h1 : (ψ i (inc σ) : Qbar l) = (κ i (inc σ) : Qbar l) * (cycBar F Ω l (inc σ) : Qbar l) ^ (-m i) := by
        simp [ψ, ε]
      rw [h1, ← hκ, ← hcyc L, Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      congr 1) hV
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hN : wdN (Loc.PP l) ι ρ = 0 := by
    rcases hor with hne | ⟨O', _, _, _, Bw', hj', hpc⟩
    · by_contra h0
      obtain ⟨i, j, hij⟩ := UpperTheory.weilDeligne_monodromy_upperTriangular ℂ _ _ n _ _ _ μ (wdRho_wdN (Loc.PP l) ι Bw h hj ρ) T h0
      obtain ⟨ha, h1⟩ := UpperTheory.continuous_character_compact_unit_values F Ω l ι w A h (hj.mem_placesOver h) (ψ i * (ψ j)⁻¹) (1 + m j - m i)
        (by
          refine ((hψc i).mul ((hψc j).inv₀ fun s => Units.ne_zero _)).congr fun s => ?_
          simp) (fun σ => by
          have h2 := hij σ
          have h3 : ι (ψ j (inc σ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero _)
          have h4 : ((normV w : ℕ) : ℂ) ^ (m i * deg σ) ≠ 0 := zpow_ne_zero _ hq
          change ι ((ψ i (inc σ) * (ψ j (inc σ))⁻¹ : (Qbar l)ˣ) : Qbar l) = _
          rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, sub_mul, add_mul, one_mul, zpow_sub₀ hq,
            zpow_add₀ hq, mul_inv_eq_iff_eq_mul₀ h3, div_mul_eq_mul_div, eq_div_iff h4, mul_comm, mul_assoc]
          exact h2)
      refine hne i j ?_
      have h5 : ψ i = ψ j := mul_inv_eq_one.mp h1
      have h6 : -m j = 1 + -m i := by omega
      simp only [ψ] at h5
      rw [h6, zpow_add, zpow_one, ← mul_assoc] at h5
      exact mul_right_cancel h5
    · have hc : Continuous fun g : ↥(Dec (F := F) A) =>
          ((r.comp (Dec (F := F) A).subtype g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
        Units.continuous_val.comp (hr.comp continuous_subtype_val)
      have hp' := GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding l _ _ (Loc.tiedP l) F Ω A O O' Bw Bw' hj hj' n _ hc hp
      have h1 := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw' h hj' (Loc.PP l) ι _ hp').2 hpc
      rw [← GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding l _ _ (Loc.tiedP l) ι F Ω A w O O' Bw Bw' h hj hj' n _ hc hp hp', e] at h1
      exact (mono0_wdPst ι Bw h hj hV).1 h1
  obtain ⟨b₀, hb₀⟩ := T
  obtain ⟨b, hb⟩ := UpperTheory.tridiagonal_weil_deligne _ ↥(Ine (F := F) A) n ((wdRho (Loc.PP l) ι Bw h hj ρ).comp (ineIncl h))
    (fun s => μ (ineIncl h s)) (isSmooth_wdRho (Loc.PP l) ι Bw h hj ρ).finite_range
    ⟨b₀, fun s => hb₀ (some (ineIncl h s))⟩
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), (wdRep (Loc.PP l) ι Bw h hj ρ).transport b.equivFun,
    fun i s hs => ?_, ?_, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [e, wdPst_of_isPst ι Bw h hj hV]
    exact (WD.sound (WDRep.iso_transport _ _)).symm
  · simp [WDRep.transport, hN]
  · have h1 : μ (ineIncl h s) = fun i => ι (χ i s : Qbar l) := funext fun i => by
      have h2 := hI i (inc (ineIncl h s)) s.2
      have h3 : ψ i (inc (ineIncl h s)) = χ i s := by
        have h6 : κ i (inc (ineIncl h s)) = cycBar F Ω l s ^ m i * χ i s := h2
        have h7 : ε (inc (ineIncl h s)) = cycBar F Ω l s := rfl
        simp only [ψ, MonoidHom.mul_apply, MonoidHom.zpow_apply]
        rw [h6, h7, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      simp [μ, h3]
    have h4 := (hb s).trans (congrArg Matrix.diagonal h1)
    have h5 : LinearMap.toMatrix b b ((wdRep (Loc.PP l) ι Bw h hj ρ).ρ (ineIncl h s)) =
        Matrix.diagonal fun i => ι (χ i s : Qbar l) :=
      (congrArg (LinearMap.toMatrix b b) (wdRep_ineIncl (Loc.PP l) ι Bw h hj ρ s)).trans h4
    exact transport_rho (wdRep (Loc.PP l) ι Bw h hj ρ) b (ineIncl h s) _ h5
end
