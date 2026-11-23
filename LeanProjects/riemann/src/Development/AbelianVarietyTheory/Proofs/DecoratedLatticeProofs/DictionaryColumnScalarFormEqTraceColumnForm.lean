import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalRepLevelDecompositionFiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelRealPartMatrixFrameStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelImageRationalStabilizerPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi

set_option maxHeartbeats 1000000 in

theorem colForm_of_dec {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u)
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0))
    (hθ : IsInfFam θ) (hE : IdE X) (hAd : B.Adapted tr.wt) (hH0 : IsTransportAdelicCorrection tr a₀)
    (hLM : Formalism.L2.SG.ColDict.LevelMatch X tr hK) (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0))
    (c : (D.mem u).C.cls 0) (γ : GL (Fin (D.R.N 0)) D.host.E) (κ : F.cls0.lev.U)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)))
    (hx : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1) :
    (F.cls0.lev.chi κ : ℂ) * GlobalTheory.AdForm.atFr (fun z => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z)
        (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) := by
  obtain ⟨aγ, hQ, hfγ, hiγ⟩ := GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace D θ hθ γ hγ
  obtain ⟨γ', hγ'1, hγ'2⟩ := GlobalTheory.T.secondModel_image_rational_stabilizerPoint D X h u ψ B aγ hQ
  have finv : ∀ (a : GA D (D.sp.X 0)) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)),
      Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1 →
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = Bm := by
    intro a Bm hB
    have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
      rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have iinv : ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ),
      Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 →
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = Bm := by
    intro a τ Bm hB
    have h1 : GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = 1 := by
      rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ) *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have hfγi : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 := by
    apply finv
    rw [hfγ, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hh : ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    have : (tr.h0⁻¹).1.1 * tr.h0.1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    exact this
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ = (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hfa0i : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ = ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    finv _ _ (by rw [e0]; exact hh)
  have hiγi : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ := by
    intro τ
    apply iinv
    rw [hiγ τ]
    unfold Formalism.L2.Forms.atInf
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨r, hr⟩ : ∃ r, r = aγ⁻¹ * g * a₀⁻¹ := ⟨_, rfl⟩
  have hg : g * a₀⁻¹ = aγ * r := by rw [hr]; group
  have hκP : κ.1 ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((F.cls0.lev.U_eq κ.1).1 κ.2).1
  obtain ⟨yk, hyk⟩ : ∃ yk : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), yk = tr.h0 * ⟨κ.1, hκP⟩ * tr.h0⁻¹ := ⟨_, rfl⟩
  have hfr : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r =
      ((F.cls0.y c * tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    rw [hr, unitaryAdelicPointFiniteMatrix_base_space_mul, unitaryAdelicPointFiniteMatrix_base_space_mul, hfγi, hx, hfa0i]
    have : (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 *
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1 *
        (tr.h0⁻¹).1.1 = (F.cls0.y c * tr.h0⁻¹).1.1 * yk.1.1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hyk]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
      group
    exact this
  have hir : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ := by
    intro τ
    rw [hr, unitaryAdelicPointInfiniteMatrices_base_space_mul, unitaryAdelicPointInfiniteMatrices_base_space_mul, hiγi, unitaryAdelicPointInfiniteMatrices_eq_one_of_finite θ a₀⁻¹ (inv_mem hH0.1), mul_one]

  have hRfin := GlobalTheory.T.secondModel_finitePart_frameActionMatrix D X h u ψ B F tr hE hAd r
  have hreal := GlobalTheory.T.secondModel_realPart_matrix_frame D X h u ψ B F tr θ hθ hE hAd r
  obtain ⟨κ'', hκ''⟩ : ∃ κ'' : Hfin X u, κ'' = (tr.hc c)⁻¹ * (B.toH r).2 := ⟨_, rfl⟩
  have hmulκ : ((tr.hc c : Hfin X u) : X.B.I.Gf) * (κ'' : X.B.I.Gf) = ((B.toH r).2 : X.B.I.Gf) := by
    rw [hκ'', ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hRk : RepM X tr.wt tr.ιA (κ'' : X.B.I.Gf) (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine RepM_cancel (tr.hc_rep c) ?_
    rw [hmulκ, ← hfr]
    exact hRfin
  have hRF : Formalism.L2.SG.ColDict.RepF X tr.wt tr.ιA (κ'' : X.B.I.Gf) yk := hRk
  have hconj : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) = κ.1 := by
    rw [hyk]
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  have hκU : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈ F.cls0.lev.U := hconj ▸ κ.2
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 κ'' yk hRF
  have hmem : κ'' ∈ Ku X u hK := hmemIff.2 hκU
  have hpsiv := hpsi hmem hκU
  have hchi : ((F.cls0.lev.chi ⟨_, hκU⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi κ : ℂˣ) : ℂ) := by
    congr 2
    exact Subtype.ext hconj

  have hdet : ∀ τ, IsUnit (GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ((F.val0.eY y).2 τ)
    refine Matrix.isUnit_det_of_right_inverse (B := GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r⁻¹ τ) ?_
    rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
  let z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) :=
    ⟨fun τ => GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ, hdet⟩
  have htr : Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH r).1 : X.B.I.Ginf)) (F.val0.eY y) z' := by
    intro τ
    show _ = _ * _
    rw [hreal τ]
  have hriesz := GlobalTheory.T.realRepresentation_moves_rieszVector_frame D X u F tr ((B.toH r).1 : X.B.I.Ginf) (B.toH r).1.2 (F.val0.eY y) z' htr

  have hlhs : GlobalTheory.AdForm.atFr (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w)
      (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hfun : (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) = z'.1 := by
      funext τ
      show _ = _ * _
      rw [hir τ]
    unfold GlobalTheory.AdForm.atFr
    rw [dif_pos (by rw [hfun]; exact z'.2)]
    congr 1
    exact Subtype.ext hfun
  refine Eq.trans (congrArg (fun t => ((F.cls0.lev.chi κ : ℂˣ) : ℂ) * t) hlhs) ?_

  have hT := T.2
  have hT1 := hT.1 (rieszJ tr (F.val0.eY y))
  have htoHaγ : B.toH aγ = (iotaI X u γ', iotaF X u γ') := Prod.ext hγ'1.symm hγ'2.symm
  have hdec : B.toH r = ((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'') := by
    ext
    · simp
    · simp [hκ'']
  have eR : B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) =
      ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hx1 : B.toH (g * a₀⁻¹) = (iotaI X u γ', iotaF X u γ') *
        (((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'')) :=
      (congrArg B.toH hg).trans ((toH_mul B aγ r).trans (congrArg₂ (· * ·) htoHaγ hdec))
    unfold SBes.colForm
    rewrite [hx1, hT1.1 γ', hT1.2 _ ⟨κ'', hmem⟩]
    have h3 := hT.2 (B.toH r).1 (rieszJ tr (F.val0.eY y)) ((1 : Hinf X u), tr.hc c)
    have h4 := Formalism.L2.SG.ColDict.inner_shP X u T.1 (tr.hc c) (rieszJ tr z')
    have h5 := inner_rieszJ tr z' (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c))
    have h6 := congrArg (fun v => T.1 v ((1 : Hinf X u), tr.hc c)) hriesz
    refine congrArg (fun t => ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * t) ?_
    exact h3.symm.trans (h6.trans (h4.symm.trans h5))
  refine Eq.trans ?_ eR.symm
  exact congrArg (fun t => t * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z') (hchi.symm.trans hpsiv.symm)

end GlobalTheory.Core.Mi

theorem GlobalTheory.Core.Mi.colDict_rd_eq_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  intro D X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM
  refine ⟨fun y => GlobalTheory.Core.Mi.rieszJ tr (F.val0.eY y), GlobalTheory.Core.Mi.span_rieszJ tr, ?_⟩
  intro T y g
  unfold GlobalTheory.AdForm.Chart.rd chart0 GlobalTheory.AdForm.rdS
  simp only
  have hd : ∃ p, GlobalTheory.AdForm.IsDec F.cls0.toChart.lev F.cls0.toChart.y
      (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := GlobalTheory.T.exists_rationalRepLevelDecomposition_finiteUnitary D u F g
  rw [dif_pos hd]
  have hfe : (fun z => Formalism.L2.SG.ColDict.colDictL X tr hK T (id hd.choose.1) (F.val0.eY.symm z)) =
      (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc hd.choose.1)) w) :=
    funext (GlobalTheory.Core.Mi.colDictL_eY_symm tr hK T hd.choose.1)
  rw [hfe]
  exact GlobalTheory.Core.Mi.colForm_of_dec X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM T y g hd.choose.1 hd.choose.2.1 hd.choose.2.2
    hd.choose_spec.1 hd.choose_spec.2

end
