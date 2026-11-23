import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableSliceAppendSingle

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem asm_omLong_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (β : ℂ) (Φ : G.Mat 1 → V) (z : ℂ) :
    G.OmLong β 0 Φ z = Φ (fun _ _ => z) := by
  unfold G.OmLong
  have : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  have hμ : G.muPi β (G.UT (0 + 1)) = Measure.dirac (fun q => isEmptyElim q) := Measure.pi_of_empty _ _
  rw [hμ, integral_dirac]
  have h1 : G.superSum (G.upper (fun q : G.UT (0 + 1) => isEmptyElim q)) = 0 := by
    simp [G.superSum]
  have h2 : (G.ptLong (0 + 1) z * G.upper (fun q : G.UT (0 + 1) => isEmptyElim q) : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.of fun _ _ => z := by
    ext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.ptLong, G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  rw [h1, h2]
  simp [G.psi]
  rfl

theorem asm_psi_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) (cc : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h z) cc (D.castM h g) = psi k a z cc g := by
  subst h; rw [P.JCTx5.castV_rfl, P.JCTx5.castM_rfl]

theorem asm_castM_mul {a b : ℕ} (h : a = b) (g g' : B.Mat k a) : D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_inv {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_castM {a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem asm_castM_symm {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h.symm (D.castM h g) = g := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_lowV_lift (a ρ m r : ℕ) (hm : 1 + ρ = m) (h1 : a + m = r) (h5 : a + 1 + ρ = a + (1 + ρ))
    (er : r = a + 1 + ρ) (zj : Fin (2 * m + k + 1) → ℂ) :
    U.lowV k a (1 + ρ) (D.castV h5 (D.castV er (D.castV h1 (liftVec k a m zj)))) = D.castV hm.symm zj := by
  subst hm; subst h1
  funext i
  simp only [U.lowV, D.castV, liftVec, Fin.val_cast]
  rw [dif_pos (by omega)]
  congr 1; ext; simp

theorem asm_phiFun_lev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a r ρa ρb : ℕ} (e : ρa = ρb)
    (ha : r = a + 0 + ρa) (hb : r = a + 0 + ρb) (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (z0 z0' : Fin (2 * r + k + 1) → ℂ) (F0 : B.Mat k r → E) (g : B.Mat k ρa) :
    U.PhiFun (s := 0) k ρa σ d (D.castV ha z0) (D.castV ha z0') (D.castF ha.symm F0) (fun q => q.elim0) g =
      U.PhiFun (s := 0) k ρb σ d (D.castV hb z0) (D.castV hb z0') (D.castF hb.symm F0) (fun q => q.elim0)
        (D.castM e g) := by
  subst e; rw [P.JCTx5.castM_rfl]

theorem asm_bridge {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a ρ1 ρ2 m r : ℕ) (e12 : ρ1 = ρ2) (e : ρ2 + 1 = m) (er : r = a + 1 + ρ1)
    (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (zb zb' : Fin (2 * r + k + 1) → ℂ) (zj zj' : Fin (2 * m + k + 1) → ℂ)
    (hzj : D.castV (show a + m = r by omega) (liftVec k a m zj) = zb)
    (hzj' : D.castV (show a + m = r by omega) (liftVec k a m zj') = zb')
    (Fb : B.Mat k r → E) (c : ℂ) (γ : B.Mat k ρ2)
    (zA zA' : Fin (2 * (a + 1 + ρ1) + k + 1) → ℂ) (hzA : zA = D.castV er zb) (hzA' : zA' = D.castV er zb')
    (FA : B.Mat k (a + 1 + ρ1) → E) (hFA : FA = D.castF er.symm Fb) (γ1 : B.Mat k ρ1)
    (hγ1 : γ1 = D.castM e12.symm γ) :
    ∫ yy : U.RC k 1 ρ1 × U.RC k 1 ρ1,
        (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)) cStd
            (U.Rn k 1 ρ1 yy.1) *
          star (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA')) cStd
            (U.Rn k 1 ρ1 yy.2))) •
        U.PhiFun (p := a) (s := 0) k (1 + ρ1) σ d (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)
          (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA') (D.castF (by omega : a + (1 + ρ1) = a + 1 + ρ1) FA)
          (fun q => q.elim0)
          ((U.Rn k 1 ρ1 yy.1)⁻¹ * U.mMap k 1 ρ1 (Matrix.of fun _ _ => c) γ1 * U.Rn k 1 ρ1 yy.2)
        ∂((U.muRC k 1 ρ1).prod (U.muRC k 1 ρ1)) =
      ∫ xx : U.RC k 1 ρ2 × U.RC k 1 ρ2,
        (psi k m zj cStd (rn1 e xx.1) * star (psi k m zj' cStd (rn1 e xx.2))) •
          U.PhiFun (p := a) (s := 0) k (r - a) σ d (D.castV (by omega : r = a + 0 + (r - a)) zb)
            (D.castV (by omega : r = a + 0 + (r - a)) zb') (D.castF (by omega : a + 0 + (r - a) = r) Fb)
            (fun q => q.elim0)
            (D.castM (by omega : m = r - a) ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2))
        ∂((U.muRC k 1 ρ2).prod (U.muRC k 1 ρ2)) := by
  subst e12; subst e; subst hzA; subst hzA'; subst hFA; subst hγ1; subst er
  rw [P.JCTx5.castM_rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  simp only [rn1, mc, P.JCTx5.castM_rfl]
  have hl := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj
  have hl' := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj'
  subst hzj; subst hzj'
  rw [hl, hl', ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.1),
    ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.2)]
  congr 1
  rw [← asm_castM_inv, ← asm_castM_mul, ← asm_castM_mul, asm_castM_castM]
  exact asm_phiFun_lev (by omega) _ _ σ d _ _ _ _

theorem asm_pointStepT (hPS : PointStep) : PointStepT := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ
  obtain ⟨hhb, rfl⟩ := hh
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hP' : D.ptSize (h ++ [(1, c)]) = D.ptSize h + 1 := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h 1 c
  have hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])) := ⟨hc.1, rfl⟩
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨hhb, rfl⟩
  have hle : D.ptSize (h ++ [(1, c)]) ≤ P.r := by omega
  have e2 : D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])) = P.r := by omega
  have hFs : B.CkOn ⊤ (B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])))) (D.castF e2 F) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hF.1
  obtain ⟨R, hR⟩ := hF.2.1
  have hRs : ∀ g ∈ B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)]))), D.castF e2 F g ≠ 0 →
      B.gN g ≤ R := fun g hg hne => by
    have := hR _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at this
  have hγ' : D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ ∈
      B.GV P.k (P.r - D.ptSize (h ++ [(1, c)])) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  have hI := asm_gInt_int (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c hd0 hc0
    (D.castV e2.symm p.T.base.z) (D.castV e2.symm p.T.base.z') (D.castF e2 F) hFs R hRs _ hγ'
  have hS := Formalism.FourierDecayAlt.P.slice_measure_identity P.k P.r (Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' F h (h ++ [(1, c)]) 0 c rfl hle
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) hloc
    (integrable_slice_append_single p.T.base.z p.T.base.z' F h c hle hloc _ hI)
  rw [asm_omLong_zero] at hS
  have hPS' := hPS P.k (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) hd0 c hc0
    (D.castV (by omega) p.T.base.z) (D.castV (by omega) p.T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z'_mem)
    (Wq →L[ℂ] Wp) (D.castF (by omega) F)
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ)
    (integrable_unipotent_rank_one (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c _ _ _ _ hI)
  have hB := asm_bridge (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (P.r - (D.ptSize h + 1))
    (P.r - D.ptSize h) P.r (by omega) (by omega) (by omega) (D.ptPerm h) (D.ptDiag h) p.T.base.z p.T.base.z'
    (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' (p.T.z_lev _ (by omega)) (p.T.z'_lev _ (by omega)) F c γ
    _ _ rfl rfl _ rfl _ rfl
  have hπ : ((Real.pi ^ ((0 + 1) * 0 / 2) : ℝ) : ℂ) = 1 := by norm_num
  rw [hπ, one_smul] at hS
  refine ((show KB.slv p.T F (D.ptSize h + 1) hj [] (h ++ [(1, c)]) hc.2 (fun a => a.elim0) γ =
      D.sliceAt P.k P.r p.T.base.z p.T.base.z' F (h ++ [(1, c)])
        (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) from rfl).trans
    (hS.trans (hPS'.trans (hB.trans ?_))))
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  dsimp only
  congr 1
  show _ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h (D.castM _ _)
  unfold D.sliceAt
  rw [dif_pos (by omega)]

end Formalism.FourierDecayAlt.P.PBH
