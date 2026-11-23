import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvariance
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BaseWeightLineBundleIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvarianceStatement

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open Limits
namespace GlobalTheory.JetRank
section Nef
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
end Nef
section
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
section Moving
open GlobalTheory.Vanishing.H0 GlobalTheory.LB GlobalTheory.TangentOrigin
open GlobalTheory.AllWt (secZ exOf)
open GlobalTheory.CompHt (genVal)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
end Moving
section Comp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
end Comp
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
theorem jet_bundle_rank_le : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u la : AllWt.Weight (T.Q.Dw j)) (n a : ℕ), GapGe (((CompHt.dimFlag (T.Q.Dw j) + 3) * ((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 + 4 * ((T.Q.Dw j).p + (T.Q.Dw j).q) + CompHt.dimFlag (T.Q.Dw j) + 3) : ℕ) : ℤ) u → (∀ τ, Antitone (la τ)) → (∀ τ, Antitone ((n : ℤ) • u τ - la τ)) → (n : ℝ) * CompHt.topDeg Y.U Z u < (a + 1) * Y.dg u Z → Y.rkC la Z ≤ ((a + CompHt.dimFlag (T.Q.Dw j)).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) * Y.dg u Z := by
  intro hX hP2 hSi hTo hGD hQ hSe D T hT j hp hq hf hj Y e o hY Z u la n a hu hla hnu hlt
  have hP := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hDe := dimFlag_eq (T.Q.Dw j)
  have hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) :=
    Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨TF⟩ := _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hV := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo
  have hC : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T.toCore j Y e o hY hf Z TF la, GlobalTheory.HSApp.vanBd_le_space D T.toCore j Y e o hY hf Z TF la⟩
  have hC0 : (0 : ℤ) ≤ (((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (CompHt.dimFlag (T.Q.Dw j) : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ ((T.Q.Dw j).p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ ((T.Q.Dw j).q : ℤ) := Int.natCast_nonneg _
  have hF : FreeOnOpen TF.X Z Y.U u := by
    refine _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hP2.q15 hP2.q16 hSi hTo.toroidalChartsForFan hSe _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (fun τ k hk => ?_) (hC _)
    have h₁ := hu τ k hk
    have h₂ := gap_kap_le (Dw := T.Q.Dw j) τ hk
    rw [Pi.sub_apply, gap_sub, ← hDe]
    push_cast at h₁ h₂ ⊢
    nlinarith
  have hB : BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
    refine _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hGD hQ hSi hP hP2.q15 hP2.q16 D T hT j hp hq Y e o hY u (fun τ a b hab => ?_) Z
    have h₁ := hu τ a (hab ▸ b.2)
    rw [gap_eq _ hab] at h₁
    push_cast at h₁ ⊢
    nlinarith
  have hu1 : GapGe 1 u := hu.mono (by push_cast; nlinarith)
  have hsa : ∀ τ, StrictAnti (u τ) := fun τ => by
    have key : ∀ (m : ℕ) (w : Fin m → ℤ), (∀ k, k + 1 < m → 1 ≤ gap w k) → StrictAnti w := fun m w hw => by
      cases m with
      | zero => exact fun a => a.elim0
      | succ m =>
        refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
        have := hw i (by omega)
        rw [show (i : ℕ) = (i.castSucc : ℕ) from rfl, gap_eq w (j := i.succ) rfl] at this
        omega
    exact key _ _ (hu1 τ)
  obtain ⟨hPr, hv⟩ := _root_.GlobalTheory.T.proportionality_principle_compactification hP2 hSi hTo hSe D T hT j hp hq hf hj Y e o hY
  have hnef := _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hQ.nef hSe _ _ _ _ _ _ TF Z hY.geo
  have key := finrank_cusp_le (n := n) (a := a) (la := la) hQ hP2.q16 hV hD hC hF hB
    (mul_nonneg (hv Z).le (Int.cast_pos.2 (CompHt.vdm_pos hsa)).le) (hPr Z u hsa)
    ⟨hnef _ (hu1.mono zero_le_one), hnef _ (gapGe_zero_of_antitone hla), hnef _ (gapGe_zero_of_antitone fun τ => by
      simpa using hnu τ)⟩ hlt
  rw [← hDe] at key
  have := Vanishing.finite_top hV.2.1 (isLB_L₀ TF.X Z la)
  have : Module.Finite Y.d.c₂.F (Cusp Z Y.U la) := .equiv (hC la).1.equiv.symm
  exact_mod_cast (Submodule.finrank_le _).trans key
end
end GlobalTheory.JetRank
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_rank_complex_le : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u la : AllWt.Weight (T.Q.Dw j)) (n a : ℕ), GapGe (((CompHt.dimFlag (T.Q.Dw j) + 3) * ((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 + 4 * ((T.Q.Dw j).p + (T.Q.Dw j).q) + CompHt.dimFlag (T.Q.Dw j) + 3) : ℕ) : ℤ) u → (∀ τ, Antitone (la τ)) → (∀ τ, Antitone ((n : ℤ) • u τ - la τ)) → (n : ℝ) * CompHt.topDeg Y.U Z u < (a + 1) * Y.dg u Z → Y.rkC la Z ≤ ((a + CompHt.dimFlag (T.Q.Dw j)).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) * Y.dg u Z := by
  first | exact @_root_.GlobalTheory.JetRank.jet_bundle_rank_le | exact _root_.GlobalTheory.JetRank.jet_bundle_rank_le | (intros; apply _root_.GlobalTheory.JetRank.jet_bundle_rank_le <;> assumption)
end
