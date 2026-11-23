import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BaseWeightLineBundleIsNef

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open Filter
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompProport
section Flag
open GlobalTheory.VarFlag
open GlobalTheory.ShFam (EigFrame FlagCpt FlagTor)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal HasToricChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end Flag
section Good
open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegCmp
open GlobalTheory.Toroidal (genBd HasToricChart)
theorem growth_eq_top_self_intersection (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    [IsIntegral (Y₀ TF.X Z)] (hd : topologicalKrullDim (Y₀ TF.X Z) = CompHt.dimFlag (T.Q.Dw j))
    {la : AllWt.Weight (T.Q.Dw j)} (hla : ∀ τ, StrictAnti (la τ)) :
    CompHt.growthOn Y.U Z (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
      ((letI := algebraΓOfHom (str₀ TF.X Z); topSelfIntersection Y.d.c₂.F (L₀ TF.X Z la) (CompHt.dimFlag (T.Q.Dw j)) : ℤ) : ℝ) := by
  have hg : genericPoint (Y₀ TF.X Z) ∉ bd₀ TF.X Z := fun h => by
    obtain ⟨y, hy⟩ := (dense_U₀ TF.X Z).nonempty
    exact h ((genericPoint_specializes y).mem_open (U₀ TF.X Z).isOpen hy)
  have hc : ∀ m : ℕ, cls (L₀ TF.X Z (m • la)) (isLB_L₀ _ _ _) = m • cls (L₀ TF.X Z la) (isLB_L₀ _ _ _) := fun m => by
    have a := cls_common_add (common₀ TF.X Z)
    induction m with
    | zero =>
      have := a 0 0
      simp only [add_zero] at this
      rw [zero_nsmul, zero_nsmul]
      exact left_eq_add.1 this
    | succ m ih => rw [succ_nsmul, succ_nsmul, ← ih]; exact a _ _
  rw [← growth_vanishing hN _ _ (str₀ TF.X Z) _ (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo).2.1 hd _ hg _
    (isLB_L₀ _ _ la) (_root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL _ _ _ _ _ _ TF Z hY.geo la (gapGe_of_strictAnti hla)) _ _ hc
    (fun m => vanBd TF.X Z (m • la)) fun _ _ => Iff.rfl, CompHt.growthOn]
  congr 1
  funext m
  have h1 := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T j Y e o hY hf Z TF (m • la)
  have h2 := le_antisymm h1.space_le (vanBd_le_space D T j Y e o hY hf Z TF (m • la))
  rw [CompHt.nsmul_wtOf, smul_zero, ← h2]
  exact congrArg _ h1.equiv.rank_eq
theorem growth_eq_covolume (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k (la : AllWt.Weight (T.Q.Dw j)), (∀ τ, StrictAnti (la τ)) →
        CompHt.growthOn Y.U (q k) (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
          (GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
            (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) * (CompHt.vdm la : ℤ)) := by
  obtain ⟨q, hq, h⟩ := topSelf_eq_covol hP.p16 TF hc hY.geo (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) hσ (hY.unf σ hσ)
  refine ⟨q, hq, fun k la hla => ?_⟩
  obtain ⟨_, hd, h⟩ := h k
  refine (_root_.GlobalTheory.CompProport.growth_eq_top_self_intersection hP hN hL hY hf _ TF hd hla).trans ?_
  rw [h, GlobalTheory.FlagPoly.flagDegFormula, CompHt.weylProd_eq,
    show ((CompHt.vdm la : ℤ) : ℝ) = _ from CompHt.map_vdm (Int.castRingHom ℝ) la]
  congr 1
  simp only [CompHt.dimFlag, eq_intCast]
  change GlobalTheory.TrueCx.covol ((Y.U σ).X k) * _ = _
  ring
theorem invariant_volume_eq_covolume (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    Proport Y.U ∧ ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
        (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := by
  obtain ⟨q, hq, h⟩ := _root_.GlobalTheory.CompProport.growth_eq_covolume hP hN hL hY hf TF hc hσ
  have hs : (0 : ℝ) < (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) :=
    Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt)
  have hv : ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
      (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := fun k => by
    have := GlobalTheory.TrueCx.covol_pos ((Y.U σ).X k)
    rw [CompHt.vZero, h k _ CompHt.strictAnti_stdWt, ENNReal.toReal_ofReal (by positivity), mul_div_cancel_right₀ _ hs.ne']
  refine ⟨fun Z la hla => ?_, q, hq, hv⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [h k la hla, CompHt.topDeg, hv]
theorem proportionality_of_local_charts (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) : Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  obtain ⟨h, q, -, hv⟩ := _root_.GlobalTheory.CompProport.invariant_volume_eq_covolume hP hN hL hY hf TF hc (σ := Y.d.c₂.F.val.toRingHom) rfl
  refine ⟨h, fun Z => ?_⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [hv]
  exact div_pos (mul_pos (GlobalTheory.TrueCx.covol_pos _) (by positivity)) (Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt))
end Good
end GlobalTheory.CompProport
end
end
