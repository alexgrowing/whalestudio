import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LineInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DdRLeFilAndInfFilEqBotOfHodgeTateMult
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonVEqZeroIffMemRangeCrisIncl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights :
    ∀ {l : ℕ} [Fact l.Prime] {K L : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V), FiniteDimensional ↥L.1 ↥(DdR ((UpperTheory.V.Loc.PP l).PD K) ρ) → (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → multV ((UpperTheory.V.Loc.PP l).PD K) ρ τ c = 0) → ∀ z : ↥(Dpst (UpperTheory.V.Loc.PP l) ρ), z ≠ 0 → monD (UpperTheory.V.Loc.PP l) ρ z = 0 → phiD (UpperTheory.V.Loc.PP l) ρ z = z → (∀ g, actD (UpperTheory.V.Loc.PP l) ρ g z = z) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  intro l _ K L key V _ _ _ _ _ ρ hfin hm z hz hN hφ hG
  let P := UpperTheory.V.Loc.PP l
  obtain ⟨y, hy, e⟩ := (mem_Dst_and_monV_eq_zero_iff l P K L V ρ z.1).mp
    ⟨(mem_Dst P ρ).mpr fun g => congrArg Subtype.val (hG g), congrArg Subtype.val hN⟩
  have hy' : ∀ g, actVB (P.PD K) ρ g y = y := by
    intro g
    have := (Submodule.mem_iInf _).mp hy g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  have c1 : ∀ x : TensorProduct ℚ_[l] V P.R.B, phiV P ↥L.1 V (crisIncl P ↥L.1 V x) =
      crisIncl P ↥L.1 V (LinearMap.lTensor V P.φB.toLinearMap x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  have h1 : LinearMap.lTensor V P.φB.toLinearMap y = y := by
    apply crisIncl_injective (LL := ↥L.1) P
    rw [← c1, e]
    exact congrArg Subtype.val hφ
  have c2 : ∀ g (x : TensorProduct ℚ_[l] V P.R.B),
      actVdR (P.PD K) ρ g (LinearMap.lTensor V P.ιB.toLinearMap x) =
      LinearMap.lTensor V P.ιB.toLinearMap (actVB (P.PD K) ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have := (P.PD K).ι_comm g b
      rw [P.PD_ι, P.PD_ι] at this
      simp [actVdR, actVB, this]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ DdR (P.PD K) ρ := by
    refine (Submodule.mem_iInf _).mpr fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, c2, hy']
  have h3 := (UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult P key ρ hfin).1 0 hm h2
  have hF : ((P.PD (UpperTheory.V.Loc.botExt l)).Fil 0).restrictScalars ℚ_[l] =
      ((P.PD K).Fil 0).restrictScalars ℚ_[l] := SetLike.coe_injective (P.PD_Fil _ _ 0)
  have h4 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ UpperTheory.V.Loc.FilT ↥L.1 V 0 := by
    unfold UpperTheory.V.Loc.FilT
    unfold FilV at h3
    rw [← hF] at h3
    exact h3
  obtain ⟨v, hv, hu⟩ := UpperTheory.V.Loc.lineInv (A := ↥L.1) y h1 h4
  refine ⟨v, ?_, fun g => hu _ ?_⟩
  · rintro rfl
    apply hz
    apply Subtype.ext
    rw [← e, hv]
    simp
  · have := hy' g
    rw [← this, hv]
    simp [actVB]
