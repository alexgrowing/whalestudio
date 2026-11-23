import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepModelWeightSection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerIsoFlagTangentPsiSet
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleSandwichBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepModelWeightSectionStatement

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem exists_weight_sections_nonvanishing : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)), WtBig P → (∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) → ∃ (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif), Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict := by
  intro hP hGD hQ hN hPr hS hT hL D T j Y e o hY hf Z P hB hG
  have hD := hB.one_le
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ _ _ _ TF Z hY.geo
  have hC : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T j Y e o hY hf Z TF la, @GlobalTheory.HSApp.vanBd_le_space D T j Y e o hY hf Z TF la⟩
  have hW := GlobalTheory.HSApp.gaps_of_wtBig _ _ _ P hB
  have h₁ : FreeOnOpen TF.X Z Y.U P.u₁ :=
    _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hN hPr hS hT hL _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (hW _ (by simp)).2 (hC _)
  have h₂ : FreeOnOpen TF.X Z Y.U P.u₂ :=
    _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hN hPr hS hT hL _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (hW _ (by simp)).2 (hC _)
  obtain ⟨R⟩ := GlobalTheory.CompHS.nonempty_choice hPr _ _ _ _ _ _ TF Z _ Y.U P hV h₁ h₂
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    by_contra h
    have h0 : (T.Q.Dw j).p + (T.Q.Dw j).q = 0 := by omega
    have : dimFlag (T.Q.Dw j) = 0 := by simp [dimFlag, h0]
    omega
  obtain ⟨ω⟩ := @GlobalTheory.CompHS.canId_nonempty hP.p5 _ _ _ _ _ _ _ _ _ TF.Y TF.X Z R.toModif
    (fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hGD _ _ _ _ _ _ K y hpq)
  obtain ⟨w₁, w₂⟩ := _root_.GlobalTheory.T.hodge_bundle_degree_squeeze hP hGD _ _ _ _ _ _ TF Z _ Y.U P R ω hY.geo h₁
  exact ⟨TF, R, ω,
    { conn := GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ R.toModif hV.1 hV.2.2 (dense_U₀ _ _)
      one_le := hD
      le_T := hB.le_T
      ext₁ := (hC _).1
      ext₂ := (hC _).1
      free₁ := h₁
      free₂ := h₂
      good := fun i hi => GlobalTheory.HSApp.goodOn_of_goodAt D T j Y e o hY hf Z _ (hG i hi)
      global_le := fun i _ => w₁ i (hC _)
      le_global := w₂ (hC _) }⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)), WtBig P → (∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) → ∃ (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif), Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict := by
  first | exact @_root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing | exact _root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing | (intros; apply _root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing <;> assumption)
end
