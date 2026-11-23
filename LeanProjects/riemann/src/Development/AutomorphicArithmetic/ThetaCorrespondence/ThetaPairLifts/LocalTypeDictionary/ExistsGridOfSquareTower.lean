import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExistsStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SqTower.TopGridExists
set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.SqTower.TopExists in
theorem square_tower_grid_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W i j => ?_⟩⟩
  have hi := i.2
  have hj := j.2
  have a := node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  have a' := node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩
  have b := node_isV G hL (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  have b' := node_isV G hL (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  have ng : ∀ {X : LSp D} {ν q : ℕ}, X.IsV ν q → NegIdx X.sp q := fun h =>
    GlobalTheory.Grid.Vertex.negIdx_of_sig _ _ h.sigOK fun τ => by rw [h.sig, h.rank]
  have ho : ∀ (x : (G.V (.grid i (j + 1))).V) (y : (G.V (.grid (i + 1) j)).V),
      (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).hD (LinearMap.inl D.host.E _ _ x) (LinearMap.inr D.host.E _ _ y) = 0 :=
    fun x y => by simp [HSpace.hD, orthSum_apply]
  have hsig := sigOK_hsum b.sigOK b'.sigOK
  have hsd := GlobalTheory.Twist.OrthSum.selfDual_hsum b.sd b'.sd
  have hneg := negIdx_of_orth rfl _ _ (isIsomEmb_inl _ _) (isIsomEmb_inr _ _) ho (ng b) (ng b')
  obtain ⟨FA, hFA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FA', hFA'⟩ := exists_isGridFr W (X := .grid i j) ⟨by omega, by omega⟩
  obtain ⟨FV, hFV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FV', hFV'⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  obtain ⟨rA, eA, sA, hA⟩ := exists_rig_of_frame FA _ a.sd
  obtain ⟨rA', eA', sA', hA'⟩ := exists_rig_of_frame FA' _ a'.sd
  obtain ⟨rW, eW, sW, hW⟩ := exists_rig_of_frame (frSum FV FV') _ hsd
  have hrk : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank = rankV D (i + 1) (j + 1) + rankV D i j := by
    have h0 : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank =
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank := rfl
    have h1 : (G.V (.grid i (j + 1))).rank = rankV D i (j + 1) := b.rank
    have h2 : (G.V (.grid (i + 1) j)).rank = rankV D (i + 1) j := b'.rank
    rw [h0, h1, h2]; simp only [rankV]; ring
  have htg : ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      rW.s = (frSum AV AV₁).cart := fun AV AV₁ h h₁ => by
    rw [sW]; funext τ
    rw [GlobalTheory.SquareAlg.cart_frSum, GlobalTheory.SquareAlg.cart_frSum, (h τ).2, (h₁ τ).2, (hFV τ).2, (hFV' τ).2]
  have ch := chars G hL W i j
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have rA1 : (G.V (.grid (i + 1) (j + 1))).rank = rankV D (i + 1) (j + 1) := a.rank
  have rA2 : (G.V (.grid i j)).rank = rankV D i j := a'.rank
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true (G.V (.grid (i + 1) (j + 1))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).2.1
    (ch t).2.2.2.1 (by rw [rA1]; exact (ch t).2.2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.2)
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).1
    (ch t).2.2.1 (by rw [rA2]; exact (ch t).2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.1)
  have hneg' : IsSelfDualC (neg (G.V (.grid (i + 1) (j + 1)))) rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg (G.V (.grid (i + 1) (j + 1)))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (fun τ => -rA.s τ) rW.s
    (sigOK_sgn true a.sigOK) hsig (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA.Λ rW.Λ hneg' hW.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA'.s rW.s
    a'.sigOK hsig (fun τ => (hA'.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA'.Λ rW.Λ hA'.1 hW.1
  choose e he using idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA' rW _ _ _ _ (G.V (.grid (i + 1) (j + 1))).rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid (i + 1) (j + 1)))
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid i j))
  refine ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨eA, eA', eW, sA.trans (funext fun τ => (hFA τ).2), sA'.trans (funext fun τ => (hFA' τ).2), htg⟩,
    le_rfl, le_rfl, by rw [rA1], by rw [rA2], ng a, ng a', hneg,
    ⟨by rw [hrk, rA1, rA2], hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩
end GlobalTheory.SqTower.TopGridExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grid_of_square_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  first | exact @_root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists | exact _root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists | (intros; apply _root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists <;> assumption)
end
