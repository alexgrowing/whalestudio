import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

theorem smul_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B X Bi : Matrix n n R) :
    c • (B * X * Bi) = B * (c • X) * Bi := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem smul_one_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B Bi : Matrix n n R)
    (h : B * Bi = 1) : B * (c • (1 : Matrix n n R)) * Bi = c • (1 : Matrix n n R) := by
  rw [← smul_conj, Matrix.mul_one, h]

theorem suppAt_inv_of {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  intro i j
  have h := congrFun (congrFun (GlobalTheory.SplitScalar.off_smul_mt_inv hg) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.sub_apply]
  linear_combination (-1 : AE D) * h

theorem chart_idem_one {D : D7} {e : AE D} {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v} {ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (hL : LevChart e PP v φ ι) : φ (toEAf D e) = 1 := by
  have h0 : φ (toEAf D e - 1) = 0 := by
    rw [hL.2.1, mul_sub, mul_one, ← map_mul, he.1.1, sub_self]
  rwa [map_sub, map_one, sub_eq_zero] at h0

set_option maxHeartbeats 1000000 in

theorem exists_supp_rdAdj_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ g : GA D T, SuppAt e T g ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T 1 g x) = rdAdj S T βS βT φ x * γ.val := by
  intro D S T βS βT e PP v φ ι he hL γ
  have hfin : GlobalTheory.LevSplit.finSw D = toEAf D := rfl
  have h1 : φ (toEAf D e) = 1 := chart_idem_one he hL
  choose M hM using fun i j => hL.1 (γ.val i j)
  choose M' hM' using fun i j => hL.1 ((γ⁻¹).val i j)
  set A : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M with hA
  set A' : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M' with hA'
  have eA : A.map φ = γ.val := Matrix.ext hM
  have eA' : A'.map φ = (γ⁻¹).val := Matrix.ext hM'
  set c := toEAf D e with hc
  have hAA : c • (A * A') = c • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    ext i j
    have hm : (A * A').map φ = (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v)) := by
      rw [Matrix.map_mul, eA, eA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hz : φ ((A * A') i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) i j) = 0 := by
      rw [map_sub]
      have := congrFun (congrFun hm i) j
      rw [Matrix.map_apply] at this
      rw [this, ← Matrix.map_apply (f := φ), Matrix.map_one φ (map_zero φ) (map_one φ), sub_self]
    have := (hL.2.1 _).1 hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at this
    exact this
  have hb : (βT⁻¹).val * βT.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hb' : βT.val * (βT⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmm : GlobalTheory.LevSplit.finSw D e • ((βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val)) =
      GlobalTheory.LevSplit.finSw D e • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    rw [hfin, ← hc]
    have : (βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val) = βT.val * (A * A') * (βT⁻¹).val := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (βT⁻¹).val βT.val, hb, Matrix.one_mul]
    rw [this, smul_conj, hAA, smul_one_conj _ _ _ hb']
  obtain ⟨g₀, hs, hg₀⟩ := GlobalTheory.ParahoricLift.split_lift_fin T he.1 _ _ hmm
  rw [hfin, ← hc] at hg₀
  have hX : ((βT⁻¹).val * (Formalism.L2.Theta.mt T g₀).map (toEAf D) * βT.val).map φ = γ.val := by
    have hfe : (Formalism.L2.Theta.mt T g₀).map (toEAf D) = (finE T g₀).val := rfl
    have h2 : c • ((βT⁻¹).val * (finE T g₀).val * βT.val) = c • A := by
      rw [smul_conj, hg₀, ← smul_conj]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [hb, Matrix.mul_one, ← Matrix.mul_assoc, hb, Matrix.one_mul]
    rw [hfe, ← eA]
    refine Matrix.ext fun i j => ?_
    show φ _ = φ _
    have := congrArg φ (congrFun (congrFun h2 i) j)
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, h1, one_mul] using this
  refine ⟨g₀⁻¹, suppAt_inv_of hs, fun x => ?_⟩
  rw [rdAdj, rdAdj, GlobalTheory.TranslateAdj.frMapAdj_actO_inv, Matrix.map_mul, hX]

end GlobalTheory.DownLift.SplitCoef
