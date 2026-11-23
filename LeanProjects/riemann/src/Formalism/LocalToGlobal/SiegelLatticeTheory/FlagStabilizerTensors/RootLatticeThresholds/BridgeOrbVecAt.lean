import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

section Gen

variable {n : ℕ} {ε : Fin n → Bool} {r : ℕ}

theorem zhat_conj_frames {f f' : Fin (r + 1) → Fin n → ℂ} {G H Hi H' : Matrix (Fin n) (Fin n) ℂ}
    (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε) (hHi : H * Hi = 1)
    (hf : ∀ a, H *ᵥ f a = f a) (hf' : ∀ b, H' *ᵥ f' b = f' b) :
    RealObj.Zhat ε f f' (Hi * G * H') = RealObj.Zhat ε f f' G := by
  ext a b
  show hJ ε (f a) ((Hi * G * H') *ᵥ f' b) = hJ ε (f a) (G *ᵥ f' b)
  rw [← Matrix.mulVec_mulVec, hf' b, ← Matrix.mulVec_mulVec,
    ← Bridge.fixed_left hH (hf a) (Hi *ᵥ (G *ᵥ f' b)), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]

end Gen

section AtCarrier

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
  (he : PlaceTie X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
  (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
  (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
  (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
  (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
  (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
  (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
  (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
    List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
  (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))

local notation "PP" => CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo

theorem orbVec_vecV (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hFX : (PP).FromX) (hB : (PP).Base i0 i0')
    (hemb : ∀ j x, (PP).S.emb j (X.ιE x) = X.B.I.φ ((PP).τ j) x)
    (hbase : ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame ((PP).T ((PP).τ.symm v)).base ((PP).ν' ((PP).τ.symm v))
      ((PP).m₀ ((PP).τ.symm v)))
    (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) (hp : ptOfL (D := D) (D.R.rS + 1) p = some w)
    (hw : OkPt X u u' w) (h h' : X.B.I.Ginf) (hD : IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h')
    (v : InfinitePlace X.B.I.F)
    (F : Formalism.FourierDecayAlt.B.Mat (PP).S.G.k (PP).S.G.r →
      ((PP).Wq ((PP).S.pl ((PP).τ.symm v)) →L[ℂ] (PP).Wp ((PP).S.pl ((PP).τ.symm v))))
    (hloc : Formalism.FourierDecayAlt.D.IsLocPt (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1
      (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) ((PP).S.G.r + 1)) :
    Formalism.FourierDecayAlt.D.vecV ((PP).T ((PP).τ.symm v)).base ((PP).ν' ((PP).τ.symm v)) ((PP).m₀ ((PP).τ.symm v)) F
              (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) =
      Formalism.FourierDecayAlt.D.orbJ ((PP).T ((PP).τ.symm v)).base
        (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))
        (Formalism.FourierDecayAlt.D.muR ((PP).T ((PP).τ.symm v)).base
          (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)) (hloc.2 ▸ Formalism.FourierDecayAlt.D.ptPerm _)) F := by
  set j := (tauE X e).symm v with hj
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  have hz2 : (T j).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
  have hz2' : (T j).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v) with hQm
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v) with hQim
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hggdef
  have hgg0 : (0 : ℝ) < gg := by
    rw [hggdef]; push_cast
    exact mul_pos (by exact_mod_cast (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1) (by exact_mod_cast (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2)
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor (gg : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a; unfold cTor; congr 1; rw [hκ]; push_cast; field_simp
  have hκstar : star κ = -κ := by
    rw [hκ, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]; ring
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    exact_mod_cast (div_pos hgg0 (by positivity)).ne'
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) Qm Qim (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) Qm Qim (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hfix : ∀ (w : D.what₂.Word) (s : X.B.I.Ginf), s ∈ HsetU X w →
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).e a = (PtRepPf.frU X w v).e a) ∧
      Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).z = (PtRepPf.frU X w v).z := by
    intro w s hs
    exact ⟨fun a => hs v _ (Or.inl (Or.inl ⟨a, rfl⟩)), hs v _ (Or.inr rfl)⟩
  obtain ⟨hHe, hHz⟩ := hfix u h hD.1
  obtain ⟨hH'e, hH'z⟩ := hfix u' h' hD.2.1
  set γ := gamW X u u' w
  have hrep : IsPtRep X u u' w γ := by
    show IsPtRep X u u' w (gamW X u u' w)
    unfold gamW; rw [dif_pos hw.1]; exact hw.1.choose_spec
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hσ

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : 0 + (p.map Prod.fst).sum ≤ D.R.rS + 1 := by rw [← hfst, hPtL.1]; omega
  have hlt := Bridge.lptOf_toStd σ D.R.rS (gg : ℝ) p 0 hblk hsum
  have hloceq : Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p = Formalism.FourierDecayAlt.C.loc σ p := by
    unfold Formalism.FourierDecayAlt.C.loc
    refine List.map_congr_left fun b _ => ?_
    congr 1
    have := hemb j (X.ιE.symm b.2)
    rw [RingEquiv.apply_symm_apply] at this
    rw [this]
    show X.B.I.φ ((tauE X e) j) (X.ιE.symm b.2) = X.B.I.φ v (X.ιE.symm b.2)
    rw [hj, Equiv.apply_symm_apply]
  have hstd : Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p) =
      Bridge.lptOf σ κ D.R.rS 0 w.1 := by
    rw [hloceq, hw1]
    exact hlt.symm

  have hA := Formalism.L2.SG.Pf.CarrierTop.zhatO_eq_mul (ZX X u u' 1 γ v)
  rw [hrep v] at hA
  have hM : Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) =
      Matrix.diagonal (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1) * ZX X u u' 1 γ v *
        Matrix.diagonal (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) := by
    rw [Bridge.ptMatN_lptOf σ κ D.R.rS hκstar w]
    show Matrix.diagonal _ * ptC X v w * Matrix.diagonal _ = _
    rw [hA]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring

  have h1 := Bridge.zhat_cs hTr hTr' (sc := sc) hsc.ne' (Formalism.MainNotions.S.uMat ((h v)⁻¹ * γ v * h' v))
  have h2 : RealObj.Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (Formalism.MainNotions.S.uMat ((h v)⁻¹ * γ v * h' v)) =
      ZX X u u' sc γ v :=
    zhat_conj_frames (uMat_unitary (h v)) (uMat_mul_inv (h v))
      (Bridge.fix_famSc (PtRepPf.frU X u v).e (PtRepPf.frU X u v).z hHe hHz sc)
      (Bridge.fix_famSc (PtRepPf.frU X u' v).e (PtRepPf.frU X u' v).z hH'e hH'z sc)
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T j).base.z (T j).base.z'
      (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) = Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) := by
    rw [hz2, hz2']
    have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u)) (Qim *ᵥ rv X.B.I v (X.zR u'))
        (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) =
        Matrix.diagonal (fun a => star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc a)) *
          RealObj.Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (Formalism.MainNotions.S.uMat ((h v)⁻¹ * γ v * h' v)) *
          Matrix.diagonal (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc) := h1
    rw [h1', h2, Formalism.L2.SG.Pf.CarrierTop.zx_sc, hM]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have ha := (Bridge.cS_lam hc hsc.ne' a).2
    have hb := (Bridge.cS_lam hc hsc.ne' b).1
    calc star (Bridge.lam _ sc a) * (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc a * ZX X u u' 1 γ v a b *
          Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc b) * Bridge.lam _ sc b
        = (star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc a) * Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc a) *
            ZX X u u' 1 γ v a b *
            (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc b * Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc b) := by ring
      _ = _ := by
        rw [ha, hb]
        simp only [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV]
        have : ((-1 : ℂ) ^ (D.R.rS - b.val)) * ((-1 : ℂ) ^ (D.R.rS - b.val)) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        linear_combination (star (κ ^ (D.R.rS - a.val)) * ZX X u u' 1 γ v a b * κ ^ (D.R.rS - b.val)) * this.symm

  have hG1 : 0 < ‖RealObj.Dl (ZX X u u' 1 γ v) (D.R.rS + 1)‖ ^ 2 -
      Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (ZX X u u' 1 γ v) D.R.rS‖ ^ 2 := by
    have hGX := hw.2 v
    change 0 < Gv (Tw (D := D) u) (Tw (D := D) u') (ZX X u u' D.host.rdE γ v) at hGX
    unfold Gv at hGX
    have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
      simp [Formalism.L2.SG.Pf.CarrierTop.cS]
    have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 γ v) (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE)
      (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE) (Tw (D := D) u * Tw (D := D) u') (by rw [hcl]; simp)
    rw [Formalism.L2.SG.Pf.CarrierTop.zx_sc, hGd] at hGX
    by_contra hle
    push_neg at hle
    have : (‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖ *
        ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 *
        (‖RealObj.Dl (ZX X u u' 1 γ v) (D.R.rS + 1)‖ ^ 2 -
          Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (ZX X u u' 1 γ v) D.R.rS‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
    linarith
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z')
      D.R.rS (Bridge.lptOf σ κ D.R.rS 0 w.1) := by
    rw [(hT j).1, (hT j).2]
    have hdet1 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)).det =
        RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) (D.R.rS + 1) :=
      (Bridge.dl_top' _).symm
    have hdet2 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) D.R.rS).det =
        RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) D.R.rS := by
      unfold RealObj.Dl; rw [dif_pos (Nat.le_succ _)]; rfl
    unfold Formalism.FourierDecayAlt.D.ptG
    have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 γ v) (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1)
      (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b)
      (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ))
      (by simp [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV])
    rw [hdet1, hdet2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hM, hGd]
    have hne1 : (∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        simp [Bridge.Af, hκ0]
    have hne2 : (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
        Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        simp [Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV, hκ0]
    have hpos : 0 < (‖∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1‖ *
        ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
          Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 :=
      pow_pos (mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)) 2
    unfold Tw at hG1
    exact mul_pos hpos hG1
  have hGV := Bridge.delta_GV hTr (uMat_unitary ((h v)⁻¹ * γ v * h' v))
  have hDF := dFrameBridge_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc
    hsc.ne' i0 i0' hFX hB γ h h' hD v
  have hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T j).base.z (T j).base.z' (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) =
      Formalism.FourierDecayAlt.D.ptMatN (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p)) (D.R.rS + 1) := by
    rw [hstd]; exact hZ
  have hGpos : 0 < Formalism.FourierDecayAlt.D.ptG (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z')
      D.R.rS (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p)) := by
    rw [hstd]; exact hG
  exact Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep D.R.k D.R.rS _ _ (T j).base (ν' j) (m₀ j) F _ hloc
    (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) (hbase v) hGpos hGV hZ' hDF

theorem orbVec_data (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hFX : (PP).FromX) (hB : (PP).Base i0 i0')
    (hemb : ∀ j x, (PP).S.emb j (X.ιE x) = X.B.I.φ ((PP).τ j) x)
    (hbase : ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame ((PP).T ((PP).τ.symm v)).base ((PP).ν' ((PP).τ.symm v))
      ((PP).m₀ ((PP).τ.symm v)))
    (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) (hp : ptOfL (D := D) (D.R.rS + 1) p = some w)
    (hw : OkPt X u u' w) (h h' : X.B.I.Ginf) (hD : IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h')
    (v : InfinitePlace X.B.I.F) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS ((PP).T ((PP).τ.symm v)).base.z ((PP).T ((PP).τ.symm v)).base.z'
              (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)) =
              Formalism.FourierDecayAlt.D.ptMatN (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1
                (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) (D.R.rS + 1) ∧
      0 < Formalism.FourierDecayAlt.D.ptG (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS ((PP).T ((PP).τ.symm v)).base.z *
        Formalism.QuantumDeterminants.Tz D.R.k D.R.rS ((PP).T ((PP).τ.symm v)).base.z') D.R.rS
        (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) ∧
      Formalism.FourierDecayAlt.D.IsLocPt (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1
        (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) (D.R.rS + 1) ∧
      trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v) ∈ Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS := by
  set j := (tauE X e).symm v with hj
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  have hz2 : (T j).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
  have hz2' : (T j).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v) with hQm
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v) with hQim
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hggdef
  have hgg0 : (0 : ℝ) < gg := by
    rw [hggdef]; push_cast
    exact mul_pos (by exact_mod_cast (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1) (by exact_mod_cast (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2)
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor (gg : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a; unfold cTor; congr 1; rw [hκ]; push_cast; field_simp
  have hκstar : star κ = -κ := by
    rw [hκ, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]; ring
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    exact_mod_cast (div_pos hgg0 (by positivity)).ne'
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) Qm Qim (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) Qm Qim (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hfix : ∀ (w : D.what₂.Word) (s : X.B.I.Ginf), s ∈ HsetU X w →
      (∀ a, Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).e a = (PtRepPf.frU X w v).e a) ∧
      Formalism.MainNotions.S.uMat (s v) *ᵥ (PtRepPf.frU X w v).z = (PtRepPf.frU X w v).z := by
    intro w s hs
    exact ⟨fun a => hs v _ (Or.inl (Or.inl ⟨a, rfl⟩)), hs v _ (Or.inr rfl)⟩
  obtain ⟨hHe, hHz⟩ := hfix u h hD.1
  obtain ⟨hH'e, hH'z⟩ := hfix u' h' hD.2.1
  set γ := gamW X u u' w
  have hrep : IsPtRep X u u' w γ := by
    show IsPtRep X u u' w (gamW X u u' w)
    unfold gamW; rw [dif_pos hw.1]; exact hw.1.choose_spec
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hσ

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : 0 + (p.map Prod.fst).sum ≤ D.R.rS + 1 := by rw [← hfst, hPtL.1]; omega
  have hlt := Bridge.lptOf_toStd σ D.R.rS (gg : ℝ) p 0 hblk hsum
  have hloceq : Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p = Formalism.FourierDecayAlt.C.loc σ p := by
    unfold Formalism.FourierDecayAlt.C.loc
    refine List.map_congr_left fun b _ => ?_
    congr 1
    have := hemb j (X.ιE.symm b.2)
    rw [RingEquiv.apply_symm_apply] at this
    rw [this]
    show X.B.I.φ ((tauE X e) j) (X.ιE.symm b.2) = X.B.I.φ v (X.ιE.symm b.2)
    rw [hj, Equiv.apply_symm_apply]
  have hstd : Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p) =
      Bridge.lptOf σ κ D.R.rS 0 w.1 := by
    rw [hloceq, hw1]
    exact hlt.symm

  have hA := Formalism.L2.SG.Pf.CarrierTop.zhatO_eq_mul (ZX X u u' 1 γ v)
  rw [hrep v] at hA
  have hM : Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) =
      Matrix.diagonal (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1) * ZX X u u' 1 γ v *
        Matrix.diagonal (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) := by
    rw [Bridge.ptMatN_lptOf σ κ D.R.rS hκstar w]
    show Matrix.diagonal _ * ptC X v w * Matrix.diagonal _ = _
    rw [hA]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring

  have h1 := Bridge.zhat_cs hTr hTr' (sc := sc) hsc.ne' (Formalism.MainNotions.S.uMat ((h v)⁻¹ * γ v * h' v))
  have h2 : RealObj.Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (Formalism.MainNotions.S.uMat ((h v)⁻¹ * γ v * h' v)) =
      ZX X u u' sc γ v :=
    zhat_conj_frames (uMat_unitary (h v)) (uMat_mul_inv (h v))
      (Bridge.fix_famSc (PtRepPf.frU X u v).e (PtRepPf.frU X u v).z hHe hHz sc)
      (Bridge.fix_famSc (PtRepPf.frU X u' v).e (PtRepPf.frU X u' v).z hH'e hH'z sc)
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T j).base.z (T j).base.z'
      (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) = Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) := by
    rw [hz2, hz2']
    have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qim *ᵥ rv X.B.I v (X.zR u)) (Qim *ᵥ rv X.B.I v (X.zR u'))
        (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) =
        Matrix.diagonal (fun a => star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc a)) *
          RealObj.Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (Formalism.MainNotions.S.uMat ((h v)⁻¹ * γ v * h' v)) *
          Matrix.diagonal (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc) := h1
    rw [h1', h2, Formalism.L2.SG.Pf.CarrierTop.zx_sc, hM]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have ha := (Bridge.cS_lam hc hsc.ne' a).2
    have hb := (Bridge.cS_lam hc hsc.ne' b).1
    calc star (Bridge.lam _ sc a) * (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc a * ZX X u u' 1 γ v a b *
          Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc b) * Bridge.lam _ sc b
        = (star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc a) * Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc a) *
            ZX X u u' 1 γ v a b *
            (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS sc b * Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) sc b) := by ring
      _ = _ := by
        rw [ha, hb]
        simp only [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV]
        have : ((-1 : ℂ) ^ (D.R.rS - b.val)) * ((-1 : ℂ) ^ (D.R.rS - b.val)) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        linear_combination (star (κ ^ (D.R.rS - a.val)) * ZX X u u' 1 γ v a b * κ ^ (D.R.rS - b.val)) * this.symm

  have hG1 : 0 < ‖RealObj.Dl (ZX X u u' 1 γ v) (D.R.rS + 1)‖ ^ 2 -
      Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (ZX X u u' 1 γ v) D.R.rS‖ ^ 2 := by
    have hGX := hw.2 v
    change 0 < Gv (Tw (D := D) u) (Tw (D := D) u') (ZX X u u' D.host.rdE γ v) at hGX
    unfold Gv at hGX
    have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
      simp [Formalism.L2.SG.Pf.CarrierTop.cS]
    have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 γ v) (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE)
      (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE) (Tw (D := D) u * Tw (D := D) u') (by rw [hcl]; simp)
    rw [Formalism.L2.SG.Pf.CarrierTop.zx_sc, hGd] at hGX
    by_contra hle
    push_neg at hle
    have : (‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖ *
        ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 *
        (‖RealObj.Dl (ZX X u u' 1 γ v) (D.R.rS + 1)‖ ^ 2 -
          Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (ZX X u u' 1 γ v) D.R.rS‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
    linarith
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z')
      D.R.rS (Bridge.lptOf σ κ D.R.rS 0 w.1) := by
    rw [(hT j).1, (hT j).2]
    have hdet1 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)).det =
        RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) (D.R.rS + 1) :=
      (Bridge.dl_top' _).symm
    have hdet2 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) D.R.rS).det =
        RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) D.R.rS := by
      unfold RealObj.Dl; rw [dif_pos (Nat.le_succ _)]; rfl
    unfold Formalism.FourierDecayAlt.D.ptG
    have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 γ v) (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1)
      (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b)
      (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ))
      (by simp [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV])
    rw [hdet1, hdet2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hM, hGd]
    have hne1 : (∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        simp [Bridge.Af, hκ0]
    have hne2 : (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
        Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        simp [Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV, hκ0]
    have hpos : 0 < (‖∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1‖ *
        ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
          Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 :=
      pow_pos (mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)) 2
    unfold Tw at hG1
    exact mul_pos hpos hG1
  have hGV := Bridge.delta_GV hTr (uMat_unitary ((h v)⁻¹ * γ v * h' v))
  have hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T j).base.z (T j).base.z' (trG Qm Qim ((h v)⁻¹ * γ v * h' v)) =
      Formalism.FourierDecayAlt.D.ptMatN (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p)) (D.R.rS + 1) := by
    rw [hstd]; exact hZ
  have hGpos : 0 < Formalism.FourierDecayAlt.D.ptG (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z')
      D.R.rS (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb j) p)) := by
    rw [hstd]; exact hG
  refine ⟨hZ', hGpos, ?_, hGV⟩
  rw [show (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) =
    Bridge.lptOf σ κ D.R.rS 0 w.1 from hstd]
  exact Bridge.isLocPt_lptOf σ κ D.R.rS hκ0 w
end AtCarrier

end Formalism.L2.SG.Pf.Carrier
