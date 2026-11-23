import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Lev.flagPol :
    UpperTheory.V.Lev.FlagPol := by
  rintro F Ω _ _ _ _ _ l _ ι n M hM m r hr w A h O _ _ _ Bw hj κ ⟨χ, hχ, hfl, hI⟩ hp
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
  have hμ0 : ∀ σ i, μ σ i ≠ 0 := fun σ i =>
    mul_ne_zero (zpow_ne_zero _ hq) ((map_ne_zero ι).mpr (Units.ne_zero _))
  have hμm : ∀ i σ τ, μ (σ * τ) i = μ σ i * μ τ i := fun i σ τ => by
    simp only [μ, deg_mul, mul_add, zpow_add₀ hq, map_mul, Units.val_mul]
    ring
  let ν : Fin n → ↥(Weil h) →* ℂˣ := fun i => MonoidHom.mk' (fun σ => Units.mk0 (μ σ i) (hμ0 σ i))
    fun σ τ => Units.ext (hμm i σ τ)
  have hν : ∀ i σ, (ν i σ : ℂ) = μ σ i := fun _ _ => rfl
  obtain ⟨b, hb⟩ := T
  refine ⟨ν, fun s => ?_, fun i s hs => Units.ext ?_, fun i j hij => Or.inl ?_⟩
  · rw [e, DpstMap.charPol_wdPst _ ι Bw h hj _ hV, ← LinearMap.charpoly_toMatrix _ b]
    refine (Matrix.charpoly_of_upperTriangular _ (fun i j hlt => (hb (some s)).1 i j hlt)).trans ?_
    exact Finset.prod_congr rfl fun i _ => congrArg (fun c => Polynomial.X - Polynomial.C c) ((hb (some s)).2 i)
  · have h2 := hI i (inc (ineIncl h s)) s.2
    have h3 : ψ i (inc (ineIncl h s)) = χ i s := by
      have h6 : κ i (inc (ineIncl h s)) = cycBar F Ω l s ^ m i * χ i s := h2
      have h7 : ε (inc (ineIncl h s)) = cycBar F Ω l s := rfl
      simp only [ψ, MonoidHom.mul_apply, MonoidHom.zpow_apply]
      rw [h6, h7, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [hν]
    simp [μ, h3, hχ i s hs]
  · simp only [hν] at hij
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
    have h5 : ψ i = ψ j := mul_inv_eq_one.mp h1
    have h6 : -m j = 1 + -m i := by omega
    simp only [ψ] at h5
    rw [h6, zpow_add, zpow_one, ← mul_assoc] at h5
    exact mul_right_cancel h5
