import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepChartsPlacesFirstFactorEqStepZeroStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

theorem det_reGL' {R : Type} [CommRing R] {a b : ℕ} (e : Fin a ≃ Fin b) (x : GL (Fin a) R) :
    Matrix.GeneralLinearGroup.det (reGL e x) = Matrix.GeneralLinearGroup.det x := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_reindex_self e _

theorem det_bc' {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (φ : A →+* B) (x : GL m A) :
    ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc φ x) : Bˣ) : B) = φ ((Matrix.GeneralLinearGroup.det x : Aˣ) : A) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

theorem det_castGL' {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    ((Matrix.GeneralLinearGroup.det (castGL h R g) : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) := by
  subst h
  simp [castGL, Matrix.GeneralLinearGroup.val_det_apply]

theorem phiA_det_eps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n k p : ℕ} {G : GAtP p}
    (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (S : Set (GL (Fin n) (AfE F E)))
    (hex : ∃ x, A.IsPt i g x ∧ x ∈ S) (e : Fin n ≃ Fin k) (v : Fin G.P.nV) :
    phiA A v ((Matrix.GeneralLinearGroup.det (reGL e (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S)) : (AfE F E)ˣ) : AfE F E) =
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)).det := by
  rw [det_reGL']
  have hx := (Classical.epsilon_spec hex).1
  have h := congrArg (fun y => ((Matrix.GeneralLinearGroup.det y : _ˣ) : (A.pl v).1.adicCompletion F)) (hx.2 v)
  have e : ∀ (a b : ((A.pl v).1.adicCompletion F)ˣ), a * b * a⁻¹ = b := fun a b => by
    rw [mul_comm a b, mul_inv_cancel_right]
  simp only [map_mul, map_inv] at h
  rw [det_bc', det_bc'] at h
  have h2 : A.ph v (prV (E := E) (A.pl v).1 ((Matrix.GeneralLinearGroup.det (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S) : _ˣ) : _)) =
      A.eQ v ((Matrix.GeneralLinearGroup.det (g v) : _ˣ) : _) := by
    rw [h, e, det_bc', det_castGL']
    rfl
  show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 _)) = _
  rw [h2, RingEquiv.symm_apply_apply, Matrix.GeneralLinearGroup.val_det_apply]

end GlobalTheory.TwV.Xc.PtOrd

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

open Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem latAt_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) ((basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v : GL _ _) : Matrix _ _ _) := by
  have hx : ∃ g : GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v), (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _) := by
    cases j with
    | zero =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
    | succ i =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
  exact Classical.epsilon_spec hx

theorem len_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    len (sysAt Ch std vp unif eO eO_spec dG dG_spec om) v j Lt = -ordP ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w)
      ((Matrix.GeneralLinearGroup.det (basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v) : _ˣ) : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) := by
  have hS := (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.setting v
  have := hS.frac_alt
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  cases j with
  | zero =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v 0 Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om 0 Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om 0 Lt v).isUnit)]
  | succ i =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt v).isUnit)]

theorem cpAt_y_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).y (i + 1) La =
      reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
          (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).y = _
  simp only [chAt, dif_pos hi]

end GlobalTheory.TwV.Xc.PtOrd
end
namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem latticeTuplePoint_det_normOne_order_eq_neg_length : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → (J.fd std).dt j La ∈ U1 (sigD D) ∧ ∀ v : (sysS H X std).Pl, ordA (A0 J) v ((J.fd std).dt j La) = -len (sysS H X std) v j La.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj La hLa
  obtain ⟨⟨hr, hpt⟩, -, -, hdt⟩ := hD j hj La hLa
  refine ⟨hdt ▸ Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) _ (J.pt std j hj La).2, fun v => ?_⟩
  rw [PtOrd.len_bases (chainAt H hT) std _ _ _ _ _ _ _ j La.2 hLa v, neg_neg, hdt]
  unfold ordA
  rw [hpt]
  erw [PtOrd.det_reGL']
  cases j with
  | zero =>
    exact congrArg _ (PtOrd.phiA_det_eps (A0 J) La.1 _ _ (let hG := J.one.good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)
  | succ i =>
    have hP := (GlobalTheory.T.stepCharts_places_firstFactor_eq_stepZero S hD hS i hj ((I.at' i hj).st.eC.symm La.1).1 v).2
    rw [PtOrd.cpAt_y_succ (chainAt H hT) std _ _ _ _ _ _ _ I _ _ _ _ i hj La, ← hP]
    exact congrArg _ (PtOrd.phiA_det_eps _ _ _ _ (let hG := (H.core i hj ((I.at' i hj).st.eC.symm La.1).1).good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)

end GlobalTheory.TwV.Xc
end
