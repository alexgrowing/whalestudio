import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TermCoset

open Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence

section Bessel

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem q_e (C : Choice X θ) (τ : D.what₂.Tau) (b : Fin D.R.rS) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS b) = frS D ^ (D.R.rS - (b : ℕ)) • rv X.B.I (vOf X τ) (X.eR b) := by
  exact ((C.isT τ).2.2.2 b b rfl).1

theorem qi_e (C : Choice X θ) (τ : D.what₂.Tau) (b : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.eR b) = (frS D ^ (D.R.rS - (b : ℕ)))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS b) := by
  have h1 := (C.isT τ).1
  have hc : (frS D ^ (D.R.rS - (b : ℕ))) ≠ 0 := pow_ne_zero _ (Formalism.L2.SG.Pf.Choice.frS_ne D)
  have h2 : C.Qi τ *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS b)) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS b) := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [q_e C τ b, Matrix.mulVec_smul] at h2
  rw [← h2, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem bvec_supSub' (a : ℕ) (b : Fin D.R.rS) (hb : b.val < a) :
    Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS b) ∈ supSub D.R.k D.R.rS a := by
  rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.mem_supSub]
  intro i hi
  simp only [Formalism.QuantumDeterminants.bvec]
  rw [Pi.single_apply, if_neg]
  intro h
  have h' : i.val = b.val := congrArg Fin.val h
  omega

theorem qi_span (C : Choice X θ) (τ : D.what₂.Tau) (a : ℕ) (w : Fin X.B.I.n → ℂ)
    (hw : w ∈ spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a) :
    C.Qi τ *ᵥ w ∈ supSub D.R.k D.R.rS a := by
  have hle : spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a ≤
      (supSub D.R.k D.R.rS a).comap (C.Qi τ).mulVecLin := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [qi_e C τ b]
    exact Submodule.smul_mem _ _ (bvec_supSub' a b hb)
  exact hle hw

theorem sset_of_sinf (C : Choice X θ) (τ : D.what₂.Tau) (u : D.what₂.Word) {x : X.B.I.Ginf} (hx : x ∈ X.SinfU u) :
    Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)) ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hS : Formalism.L2.SG.HidaSetting.InS (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u))
      (uMat (x (vOf X τ))) := hx (vOf X τ)
  have hU : (uMat (x (vOf X τ)))ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (x (vOf X τ)) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := (x (vOf X τ)).2
  have key : ∀ v, (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)) - 1) *ᵥ v =
      C.Qi τ *ᵥ ((uMat (x (vOf X τ)) - 1) *ᵥ (C.Q τ *ᵥ v)) := by
    intro v
    have hM : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)) - 1 =
        C.Qi τ * (uMat (x (vOf X τ)) - 1) * C.Q τ := by
      show C.Qi τ * uMat (x (vOf X τ)) * C.Q τ - 1 = _
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  apply Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.fwd
  · have hmid : (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
      rw [← hg]
      calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
          = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
            rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    show (C.Qi τ * uMat (x (vOf X τ)) * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *
      (C.Qi τ * uMat (x (vOf X τ)) * C.Q τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
    calc (C.Qi τ * uMat (x (vOf X τ)) * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *
          (C.Qi τ * uMat (x (vOf X τ)) * C.Q τ)
        = (C.Q τ)ᴴ * ((uMat (x (vOf X τ)))ᴴ *
            (((C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ) * uMat (x (vOf X τ)))) * C.Q τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C.Q τ)ᴴ * ((uMat (x (vOf X τ)))ᴴ * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (x (vOf X τ)))) *
            C.Q τ := by rw [hmid]
      _ = (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ := by
          rw [← Matrix.mul_assoc (uMat (x (vOf X τ)))ᴴ, hU]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hg
  · exact (Formalism.L2.SG.Pf.zTr C u τ).1
  · refine ⟨fun a => ?_, ?_⟩
    · have he : C.Q τ *ᵥ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.stdX D.R.k D.R.rS a =
          frS D ^ (D.R.rS - (a : ℕ)) • rv X.B.I (vOf X τ) (X.eR a) := q_e C τ a
      rw [key, he, Matrix.mulVec_smul, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (qi_span C τ a.1 _ (hS.1 a))
    · have hz' : C.Q τ *ᵥ zB X (C.Qi τ) u τ = rv X.B.I (vOf X τ) (X.zR u) := by
        simp only [zB]
        rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
      rw [key, hz']
      exact qi_span C τ D.R.rS _ hS.2

end Bessel

end GlobalTheory.TermCoset

namespace GlobalTheory.TermCoset

section Main

open Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.FinXP

theorem trG_mul {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (a b : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi (a * b) = Formalism.L2.SG.RealObj.trG Q Qi a * Formalism.L2.SG.RealObj.trG Q Qi b := by
  show Qi * uMat (a * b) * Q = Qi * uMat a * Q * (Qi * uMat b * Q)
  have hm : uMat (a * b) = uMat a * uMat b := rfl
  rw [hm]
  calc Qi * (uMat a * uMat b) * Q = Qi * uMat a * (Q * Qi) * uMat b * Q := by
        rw [hQ, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = Qi * uMat a * Q * (Qi * uMat b * Q) := by simp only [Matrix.mul_assoc]

theorem trG_inv {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (h1 : Qi * Q = 1) (hQ : Q * Qi = 1) (a : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi a⁻¹ = (Formalism.L2.SG.RealObj.trG Q Qi a)⁻¹ := by
  show Qi * uMat a⁻¹ * Q = (Qi * uMat a * Q)⁻¹
  symm
  apply Matrix.inv_eq_right_inv
  have hm : uMat a * uMat a⁻¹ = 1 := by
    show ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((a⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  calc Qi * uMat a * Q * (Qi * uMat a⁻¹ * Q) = Qi * uMat a * (Q * Qi) * uMat a⁻¹ * Q := by
        simp only [Matrix.mul_assoc]
    _ = Qi * Q := by rw [hQ, Matrix.mul_one, Matrix.mul_assoc Qi (uMat a), hm, Matrix.mul_one]
    _ = 1 := h1

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem dc_repF {u u' : D.what₂.Word} (s : TT Y u u') {T : RT Y u u'} (hs : s.toTerm = T) :
    Formalism.L2.SG.TermDef.DCRel s.lam (lf D (X.Fu u)) s.frame (repF T) := by
  subst hs
  exact (Formalism.L2.SG.TermTieOf.eqIff_base (Y := Y) (u' := u') s.lam s.mem ⟨s.frame, s.rep.2.2.2.2⟩
    (Quot.out s.toTerm.cls)).1 (Quot.out_eq _).symm

end Main

end GlobalTheory.TermCoset

namespace GlobalTheory.TermCoset

section Top

open Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.FinXP Formalism.MainNotions.S.Lat

theorem dcoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → ∀ τ, ∃ a ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∃ a' ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u' τ), Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ)) = a * gamR hI C t τ * a'⁻¹ := by
  intro D X Y hF hI θ C u u' t s hst τ
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hex := frameLiftEx_holds hI u u' t
  have hL : IsFrameLift hI t (linOf hI t) := by
    unfold linOf
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨hgI, hge, hgz⟩ := hL
  have hexg := Formalism.L2.SG.Pf.ratPt_holds D X (linOf hI t) hgI
  have hxg : RatLink X (ptR hI t) (linOf hI t) := by
    unfold ptR
    rw [dif_pos hexg]
    exact hexg.choose_spec
  obtain ⟨n, hn, m, hm, hfr, -⟩ := dc_repF s hst
  obtain ⟨xn, hxn⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hn.1.1
  obtain ⟨xm, hxm⟩ := Formalism.L2.SG.Pf.ratPt_holds D X m hm.1.1
  have hxs : RatLink X s.pt s.lin := s.rep.2.1

  have hse : ∀ i, s.frame.fl.e i = s.lin (X.eX i) := by
    intro i
    have h := frame_apply s (Fin.castSucc i)
    simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] at h
    rw [h]
    exact congrArg s.lin (congrFun (X.Fu_e u') i)
  have hsz : s.frame.fl.z = s.lin (X.zu u') := by
    have h := frame_apply s (Fin.last D.R.rS)
    simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] at h
    rw [h]
    exact congrArg s.lin (X.flagZVector u')
  have hinv : ∀ (φ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (v : (VS D).V), φ⁻¹ (φ v) = v := by
    intro φ v
    show (φ⁻¹ * φ) v = v
    rw [inv_mul_cancel]
    rfl

  have hce : ∀ i, ((linOf hI t)⁻¹ * n * m * s.lin) (X.eX i) = X.eX i := by
    intro i
    show (linOf hI t)⁻¹ (n (m (s.lin (X.eX i)))) = X.eX i
    have h := hfr (Fin.castSucc i)
    simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] at h
    rw [hse] at h
    rw [← h, ← hge i, hinv]
    exact congrFun (X.Fu_e u') i
  have hcz : ((linOf hI t)⁻¹ * n * m * s.lin) (X.zu u') = X.zu u' := by
    show (linOf hI t)⁻¹ (n (m (s.lin (X.zu u')))) = X.zu u'
    have h := hfr (Fin.last D.R.rS)
    simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] at h
    rw [hsz] at h
    rw [← h, ← hgz, hinv]
    exact X.flagZVector u'

  have hXu : ∀ j, Xflag (lf D (X.Fu u)) j = Submodule.span D.host.E (X.eX '' {i | i.1 < j}) := by
    intro j
    show Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j}) = _
    rw [X.Fu_e u]
  have hXsu : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e u]
  have hnE : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
    intro a
    have h := hn.2.1 a.val _ (Formalism.L2.SG.FourParts.e_mem_Xflag (lf D (X.Fu u)) a)
    rw [hXu, show (lf D (X.Fu u)).fl.e a = X.eX a from congrFun (X.Fu_e u) a] at h
    exact h
  have hnZ : n (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have h := hn.2.2 _ (Formalism.L2.SG.FourParts.z_mem_orth (lf D (X.Fu u)))
    rw [hXsu, show (lf D (X.Fu u)).fl.z = X.zu u from X.flagZVector u] at h
    exact h

  have hpull : ∀ (S : Set (Fin D.R.rS)) (y : (VS D).V), y ∈ Submodule.span D.host.E (s.frame.fl.e '' S) →
      s.lin⁻¹ y ∈ Submodule.span D.host.E (X.eX '' S) := by
    intro S y hy
    have hle : Submodule.span D.host.E (s.frame.fl.e '' S) ≤
        (Submodule.span D.host.E (X.eX '' S)).comap (s.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [hse i, hinv]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    exact hle hy
  have hμE : ∀ a : Fin D.R.rS, (s.lin⁻¹ * m * s.lin) (X.eX a) - X.eX a ∈
      Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
    intro a
    have h := hpull _ _ (hm.2.1 a.val _ (Formalism.L2.SG.FourParts.e_mem_Xflag s.frame a))
    rw [map_sub, hse a, hinv] at h
    exact h
  have hμZ : (s.lin⁻¹ * m * s.lin) (X.zu u') - X.zu u' ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have h0 := hm.2.2 _ (Formalism.L2.SG.FourParts.z_mem_orth s.frame)
    have h0' : m s.frame.fl.z - s.frame.fl.z ∈ Submodule.span D.host.E (s.frame.fl.e '' Set.univ) := by
      rw [Set.image_univ]
      exact h0
    have h := hpull _ _ h0'
    rw [Set.image_univ, map_sub, hsz, hinv] at h
    exact h

  have hxc : RatLink X ((ptR hI t)⁻¹ * xn * xm * s.pt) ((linOf hI t)⁻¹ * n * m * s.lin) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hxg) hxn) hxm) hxs
  have hxμ : RatLink X (s.pt⁻¹ * xm * s.pt) (s.lin⁻¹ * m * s.lin) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hxs) hxm) hxs
  have hSn := Formalism.L2.SG.Pf.IdMeet.pt_srat X hxn hnE hnZ
  have hSc := Formalism.L2.SG.Pf.IdMeet.pt_srat X hxc (fun i => by rw [hce i, sub_self]; exact Submodule.zero_mem _)
    (by rw [hcz, sub_self]; exact Submodule.zero_mem _)
  have hSμ := Formalism.L2.SG.Pf.IdMeet.pt_srat X hxμ hμE hμZ
  have hA := (Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u _ (inv_mem hSn)).1
  have hA' := (Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ (mul_mem hSμ (inv_mem hSc))).1
  have hpt : s.pt = xn⁻¹ * ptR hI t * ((s.pt⁻¹ * xm * s.pt) * ((ptR hI t)⁻¹ * xn * xm * s.pt)⁻¹)⁻¹ := by
    group
  refine ⟨_, sset_of_sinf C τ u hA, _, sset_of_sinf C τ u' hA', ?_⟩
  have hv : s.pt.1 (vOf X τ) = (xn⁻¹).1 (vOf X τ) * (ptR hI t).1 (vOf X τ) *
      (((s.pt⁻¹ * xm * s.pt) * ((ptR hI t)⁻¹ * xn * xm * s.pt)⁻¹).1 (vOf X τ))⁻¹ := by
    conv_lhs => rw [hpt]
    rfl
  rw [hv, trG_mul (C.Q τ) (C.Qi τ) h2, trG_mul (C.Q τ) (C.Qi τ) h2, trG_inv (C.Q τ) (C.Qi τ) h1 h2]
  rfl

end Top

end GlobalTheory.TermCoset
