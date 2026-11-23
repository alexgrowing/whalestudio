import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ClassSumLift
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefDown_dW_eq_finrank_WL (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (P.A3.indefDown P.S0).dW i = Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) := by
  have hz := Q.zs
  have hs := Q.s0
  have key : ∀ (Z : DefSub P.A3.fam3.amb3) (S' : IndefData (P.A3.side3 P.P0 P.ψ0 Z)), Z = P.Zs → HEq S' P.S0 →
      P.S0.dW i = S'.dW i := by
    intro Z S' h1 h2
    subst h1
    rw [eq_of_heq h2]
  exact key _ _ hz hs
theorem exists_sum_smul_eq_of_isKsForm (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (hk : (Q.Rl.FW i).IsKsForm)
    (v : Fin (Q.Rl.nW i) → D.what₂.LL) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx ((i : ℕ) + 1)),
      (Q.nexp.fi i).e (∑ k, a k • (show ↥(Q.Sx.A ((i : ℕ) + 1)).WK from f k).1) = v := by
  obtain ⟨n, b, hb, -, -, -, hs⟩ := hk
  have hv : v ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hs]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨n, a, fun k => (⟨(Q.nexp.fi i).e.symm (b k), ((Q.nexp.fi i).wk _).2 (by
    rw [LinearEquiv.apply_symm_apply]; exact hb k)⟩ : ↥(Q.Sx.A ((i : ℕ) + 1)).WK), ?_⟩
  rw [map_sum, ← ha]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  exact (Q.nexp.fi i).e.apply_symm_apply _
set_option synthInstance.maxHeartbeats 400000 in
theorem at_index_alt (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (hP : _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q)
    (hD : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I)
    (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (jD : (Y.MjH ((i : ℕ) + 1)).V → B.Q.Sx.WL ((i : ℕ) + 1))
    (hjD : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL),
      HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD x) = jDL B.Q.Rl B.Q.F.lv2 i y)
    (eMj : (Y.MjH ((i : ℕ) + 1)).V → FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w))
    (hsum : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1)),
      jD x = ∑ k, a k • (show ↥(B.Q.Sx.A ((i : ℕ) + 1)).WK from f k).1 →
      eMj x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (B.Q.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k))
    (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)) (hx : x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1))
    (z : (Y.MjH ((i : ℕ) + 1)).V)
    (hz : Y.jM _ z = D.what₂.thetaP (D.what₂.muTw w) _ (D.what₂.jMt (D.what₂.muTw w) _ x)) :
    eMj z = NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) := by
  have ht : P.I.tup (Qr.tupT (D.what₂.muAt w)) = D.what₂.muTw w :=
    (Qr.tupTie _ (Or.inr ⟨w, rfl⟩)).trans ((D.what₂.muAt_or w).resolve_left hw)
  obtain ⟨x', e1⟩ := exists_cast ((i : ℕ) + 1) _ _ ht x
  obtain ⟨c, rfl⟩ := (P.I.eMt i _).surjective x'
  obtain ⟨y, e2⟩ := exists_heq_fin (_root_.GlobalTheory.ClassSumLift.indefDown_dW_eq_finrank_WL B.Q i) (((P.A3.indefDown P.S0).θ i _).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i _).mulVec c))
  obtain ⟨n, a, f, e3⟩ := _root_.GlobalTheory.ClassSumLift.exists_sum_smul_eq_of_isKsForm B.Q i (B.fw.ks i) (jDL B.Q.Rl B.Q.F.lv2 i y)
  rw [hP w i h1 h2 _ ht hw c x e1 hx y e2 n a f e3]
  apply hsum
  apply (B.Q.nexp.fi i).e.injective
  rw [e3]
  apply hjD
  have : z = P.JM.eW i (((P.A3.indefDown P.S0).θ i (Qr.tupT (D.what₂.muAt w))).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i (Qr.tupT (D.what₂.muAt w))).mulVec c)) := by
    apply Idx.jM_inj Y
    rw [hz, P.tied.mjH.j_eq, ← hD.thTheta, e1]
    exact theta_cast _ _ _ ht _
  rw [this, LinearEquiv.symm_apply_apply]
  exact e2
end GlobalTheory.ClassSumLift
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.ClassSumLift.eM_eq_thPe_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x ∈ Idx.TjV D (D.what₂.muTw w) j, ∀ y : (Y.MjH j).V, Y.jM j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) → eM w j y = NChoice.thPe D ex.nch w j (ex.nch.eMt w j x) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B _ Qr jD eM hD hP hread hsum w j hw h1 h2 x hx y hy
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, (i : ℕ) + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  exact _root_.GlobalTheory.ClassSumLift.at_index_alt B Qr hP hD w i h1 h2 hw (jD ((i : ℕ) + 1)) (fun x y h => hread i x y h) (eM w ((i : ℕ) + 1))
    (fun x n a f h => hsum w ((i : ℕ) + 1) h1 h2 x n a f h) x hx y hy
end
end
