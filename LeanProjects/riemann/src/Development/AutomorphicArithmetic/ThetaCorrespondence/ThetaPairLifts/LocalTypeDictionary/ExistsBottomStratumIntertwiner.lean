import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantExistsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotIntertw
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
variable {D : D7}
theorem bottom_stratum_intertwining : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  intro _ _ _ hInp _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hstd i j A A' WW X δ t0 hX
  by_cases hC : Crv D ⊤ δ
  swap
  · refine ⟨1, 2 * Formalism.L2.Pj.xiR D, one_ne_zero, fun h => absurd h hC, fun τ => ?_, fun s Q P P' _ => absurd P.crv hC⟩
    rw [GlobalTheory.FockPos.norm_embedding_xi0_eq]; simp
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  refine ⟨-δ, (area (lamOf D ⊤ δ))⁻¹, neg_ne_zero.2 hδ, fun _ => rfl, fun τ => ?_, fun s Q P P' hB ea ed => ?_⟩
  · have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq]
    field_simp
  have hSet : Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hstd, W.θ_is, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hw := GlobalTheory.ConjWeilBack.weil_conjRep_of_neg W.ψ A WW _ _ (X.ω s) (hX.is.weil s)
  obtain ⟨hth, hfock⟩ := conj_datum hX s
  obtain ⟨G₀, hG₀, hR₀⟩ := reads_of_fock ea.symm ed.symm hSet hw hth hfock
  obtain ⟨hcS, hcT⟩ := bottom_finParts G hL hB
  have hTT0 : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := GlobalTheory.NormSum.VacMove.vac_TT (hInp D).g1 P.crv P.vac.1
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet _ hTT0
  refine ⟨?_, fun h g x y hg hy => ?_⟩
  · rw [xiN_of_reads W.θ_is _ _ hδ hR₀]; exact hG₀
  · have hv := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw (hInp D) t0 P.pt0
      P.even_mul P.vac hcS hcT x h y g hy hg f₀ hf₀
    have hm := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw P.vac.1 x h y g hy hg 1
      f₀ hf₀ (by rw [one_smul]; exact hv) G₀ hG₀ _ hR₀
    rw [one_smul] at hm
    have e1 : (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
        GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (fun w => starRingEnd ℂ (X.f s w)) := by
      change _ = GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (X.f s))
      rw [GlobalTheory.AdjTr.conjRep_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rfl
    rw [e1, xiN_of_reads W.θ_is _ _ hδ hm, xiN_of_reads W.θ_is _ _ hδ hR₀]
end GlobalTheory.BotIntertw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottom_stratum_intertwiner : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  first | exact @_root_.GlobalTheory.BotIntertw.bottom_stratum_intertwining | exact _root_.GlobalTheory.BotIntertw.bottom_stratum_intertwining | (intros; apply _root_.GlobalTheory.BotIntertw.bottom_stratum_intertwining <;> assumption)
end
