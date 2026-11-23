import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
namespace LinearIndependenceOfCarries
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.ReadingExt
open Module
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def finrankCoordinateEquiv (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      (Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL) :=
  LinearEquiv.funCongrLeft D.what₂.LL D.what₂.LL (finCongr (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
def embeddingAtIndex (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (Y.MjH ((i : ℕ) + 1)).V →ₗ[D.what₂.LL] Q.Sx.WL ((i : ℕ) + 1) :=
  (Q.nexp.fi i).e.symm.toLinearMap ∘ₗ jDL Q.Rl Q.F.lv2 i ∘ₗ (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i).toLinearMap ∘ₗ (P.JM.eW i).symm.toLinearMap
def embeddingAtLevel (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] Q.Sx.WL j
  | 0 => 0
  | k + 1 => if h : k < D.R.m then _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex Q ⟨k, h⟩ else 0
theorem embeddingAtLevel_succ_eq_embeddingAtIndex (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel (Y := Y) Q ((i : ℕ) + 1) = _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex Q i := by
  obtain ⟨k, h⟩ := i
  simp [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel, h]
theorem jDL_injective_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Function.Injective (jDL Q.Rl Q.F.lv2 i) := by
  have h : LinearIndependent D.what₂.LL (Q.Rl.toRealDat.bL Q.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)).linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _)
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 h
theorem embeddingAtIndex_injective (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Function.Injective (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex (Y := Y) Q i) := by
  intro x y h
  have h1 := (Q.nexp.fi i).e.symm.injective h
  have h2 := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.jDL_injective_alt Q i h1
  exact (P.JM.eW i).symm.injective ((_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i).injective h2)
theorem e_embeddingAtLevel_succ_eq_jDL_of_heq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
    (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL)
    (h : HEq ((P.JM.eW i).symm x) y) : (Q.nexp.fi i).e (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel Q ((i : ℕ) + 1) x) = jDL Q.Rl Q.F.lv2 i y := by
  rw [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel_succ_eq_embeddingAtIndex]
  have h1 : _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i ((P.JM.eW i).symm x) = y := comp_cast_of_heq (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i) _ y h
  simp only [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h1]
theorem jDa_injective_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Function.Injective (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel (Y := Y) Q j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < D.R.m := by omega
  have e := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel_succ_eq_embeddingAtIndex (Y := Y) Q ⟨k, hk⟩
  have h := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex_injective (Y := Y) Q ⟨k, hk⟩
  rw [← e] at h
  exact h
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem embW_comp_algebraMap_eq_fracExt_comp_iotaK (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) :
    (ex.nch.embW w).comp (algebraMap Q.Sx.Ks D.what₂.LL) =
      (fracExt ex.nch w).comp (ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w)) :=
  GlobalTheory.Proof.FractionFieldEmbeddingCompat.embCompat D ex.nch hc Q.Sx.Ks Q.Sx.kKs Q.Sx.kKs_spec w _ rfl
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_ext_alt (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hk : (Q.Sx.A j).IsKsForm) :
    ∃ e : Q.Sx.WL j →ₛₗ[ex.nch.embW w]
        FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w),
      (∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx j),
        e (∑ k, a k • (show ↥(Q.Sx.A j).WK from f k).1) =
          ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
            (Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm
              ((1 : KB Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[Q.Sx.Ks] f k)) ∧
      (∀ (ι : Type) (v : ι → Q.Sx.WL j), LinearIndependent D.what₂.LL v →
        LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => e (v a))) := by
  letI aK : Algebra Q.Sx.Ks (FractionRing (D.ntw.O (ex.nch.twI w))) := (ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w)).toAlgebra
  letI aE : Algebra (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) := (fracExt ex.nch w).toAlgebra
  haveI : IsScalarTower (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) :=
    IsScalarTower.of_algebraMap_eq fun x => (fracExt_algebraMap ex.nch w x).symm
  obtain ⟨⟨e, he, -⟩, hC, -⟩ := GlobalTheory.SemilinearExt.semilinearExtension Q.Sx.Ks D.what₂.LL (Q.Sx.WL j) (Q.Sx.A j).WK hk
    (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) (ex.nch.embW w)
    (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_comp_algebraMap_eq_fracExt_comp_iotaK hc Q w) (D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) (Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2)
  exact ⟨e, fun n a f => he (Fin n) a f, fun ι v hv => li_of_carries e (hC e he) hv⟩
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem embW_Ks_alt (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) (j : ℕ) (a : Q.Sx.Ks)
    (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) :
    (ex.nch.embW w (algebraMap Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m :
        FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) =
      (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
        ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m) := by
  letI aE : Algebra (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) := (fracExt ex.nch w).toAlgebra
  haveI : IsScalarTower (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) :=
    IsScalarTower.of_algebraMap_eq fun x => (fracExt_algebraMap ex.nch w x).symm
  have e1 : ex.nch.embW w (algebraMap Q.Sx.Ks D.what₂.LL a) =
      algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w))
        (show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) :=
    RingHom.congr_fun (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_comp_algebraMap_eq_fracExt_comp_iotaK hc Q w) a
  rw [e1]
  exact GlobalTheory.SemilinearExt.algebraMap_tmul (O := D.ntw.O (ex.nch.twI w)) _ m
set_option synthInstance.maxHeartbeats 400000 in
theorem reading_ext_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B _ _ hc
  have hks : ∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm := by
    intro j h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < D.R.m := by omega
    exact GlobalTheory.isKsForm_of_formsIso _ _ (B.Q.nexp.fi ⟨k, hk⟩) (B.fw.ks ⟨k, hk⟩)
  have hE := fun w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.exists_ext_alt hc B.Q w j h1 h2 (hks j h1 h2)
  choose E hE1 hE2 using hE
  classical
  let eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w) := fun w j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then (E w j h.1 h.2).comp (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j) else 0
  have heM : ∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V), eM w j x = E w j h1 h2 (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j x) := by
    intro w j h1 h2 x
    simp only [eM, dif_pos (And.intro h1 h2)]
    rfl
  refine ⟨_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q, eM, fun i x y h => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.e_embeddingAtLevel_succ_eq_jDL_of_heq B.Q i x y h, hks, ?_, fun w j a m => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_Ks_alt hc B.Q w j a m, ?_⟩
  · intro w j h1 h2 x n a f hx
    rw [heM w j h1 h2, hx]
    exact hE1 w j h1 h2 n a f
  · intro w j _ h1 h2
    have hv : LinearIndependent D.what₂.LL (fun a => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j ((Y.MjH j).b a)) :=
      (Y.MjH j).b.linearIndependent.map' (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j) (LinearMap.ker_eq_bot.2 (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.jDa_injective_alt B.Q j h1 h2))
    have h := hE2 w j h1 h2 _ _ hv
    simp only [heM w j h1 h2]
    exact h
end GlobalTheory.CompanionTheory.ReadingExt
end
end
end LinearIndependenceOfCarries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_first_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  first | exact @_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt | exact _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt | (intros; apply _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt <;> assumption)
end
end
