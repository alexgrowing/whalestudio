import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimEvT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCV

namespace Formalism.FourierDecayAlt.P.CutBP

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section loc

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_congr_level (Bs : B.RealPlaceData k r Wp Wq) {X Y : B.Mat k r → (Wq →L[ℂ] Wp)} {g : B.Mat k r}
    (hg : g ∈ B.GV k r) (h : ∀ x ∈ B.GV k r, Gf k r Bs.z Bs.z' x = Gf k r Bs.z Bs.z' g → X x = Y x) :
    B.JF Bs X g = B.JF Bs Y g := by
  rw [← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs X g, ← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs Y g]
  unfold B.Jtau
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq
  simp only [B.rho]
  rw [h _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hq hg) (Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hq g)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_inter {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E} (n : ℕ)
    (hf : B.CkOn ⊤ (B.GV k r) f) (U : Set (B.Mat k r)) : B.CkOn (n : ℕ∞) (U ∩ B.GV k r) f := by
  intro g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hff⟩ := hf g₀ hg₀.2
  exact ⟨V, f', hV, hgV, hf'.of_le (by exact_mod_cast le_top), hff⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fold_ckOn (s : ℂ) : ∀ (w : List C.Letter) (H : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) H →
    B.CkOn ⊤ (B.GV k r) (w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) H)
  | [], _, h => h
  | a :: w, H, h => Formalism.FourierDecayAlt.P.CutMP.ER.coefficient_vector_smoothness k r Wp Wq s (a.2 : ℂ) _ (fold_ckOn s w H h)

theorem fold_congr_open (s : ℂ) {U : Set (B.Mat k r)} (hU : IsOpen U) {X Y : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hX : B.CkOn ⊤ (B.GV k r) X) (hY : B.CkOn ⊤ (B.GV k r) Y) (he : ∀ x ∈ U ∩ B.GV k r, X x = Y x) :
    ∀ (w : List C.Letter), ∀ x ∈ U ∩ B.GV k r,
      w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) X x = w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) Y x
  | [], x, hx => he x hx
  | a :: w, x, hx => by
    show (s • Q.CV k r (a.2 : ℂ) (w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) X)) x =
      (s • Q.CV k r (a.2 : ℂ) (w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) Y)) x
    simp only [Pi.smul_apply]
    rw [Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r _ U _ _ (a.2 : ℂ) hU (ckOn_inter _ (fold_ckOn s w X hX) U)
      (ckOn_inter _ (fold_ckOn s w Y hY) U) (fold_congr_open s hU hX hY he w) x hx]

end loc

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bigCell_pos (p : KB.Pl P Wp Wq) (q : (Fin P.r → ℂ) × ℂ)
    (hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q ≠ 0) :
    bigCell P.k P.r q.1 (p.T.base.μsec q.2) ∈ B.GV P.k P.r ∧
      0 < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) := by
  set c : Fin (P.r + 1) → ℂ := Fin.snoc q.1 q.2 with hcdef
  have hq1 : (fun j : Fin P.r => c j.castSucc) = q.1 := funext fun j => by simp [c]
  have hq2 : c (Fin.last P.r) = q.2 := by simp [c]
  have hqc : q = ((fun j => c j.castSucc), c (Fin.last P.r)) := by rw [hq1, hq2]
  rw [hqc] at hw
  rw [← hq1, ← hq2]
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG' : 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    have hsec := p.T.base.sec.2 _ hlt
    have hγ' : bigCell P.k P.r (fun i => c i.castSucc) (p.T.base.μsec (c (Fin.last P.r))) ∈ B.GV P.k P.r :=
      bigCellMem P.k P.r _ _ hc hsec.1
    have hZγ' := Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base c hlt
    refine ⟨hγ', ?_⟩
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZγ']
    exact hG'
  · exact absurd rfl hw'

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem pointwise_truncation_locality (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (w : List C.Letter) : PtwCut p χ F w := by
  refine Filter.Eventually.of_forall fun q => ?_
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · exact Filter.Eventually.of_forall fun ε => by simp [levelZeroRadialIntegral, hq]
  obtain ⟨hgG, hpos⟩ := bigCell_pos p q hq
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  have hU : IsOpen {x : B.Mat P.k P.r | ε < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have he : ∀ x ∈ {x : B.Mat P.k P.r | ε < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r,
      D.cutF p.T.base χ F ε x = F x := by
    intro x hx
    unfold D.cutF
    rw [hχ.2.2 _ ((one_le_div hε.1).2 (le_of_lt hx.1))]
    simp
  have hcut := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε
  have hlev : ∀ x ∈ B.GV P.k P.r, Gf P.k P.r p.T.base.z p.T.base.z' x =
      Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) →
      x ∈ {x : B.Mat P.k P.r | ε < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r :=
    fun x hx hGx => ⟨by show ε < _; rw [hGx]; exact hε.2, hx⟩
  unfold levelZeroRadialIntegral
  rw [jf_congr_level p.T.base hgG (fun x hx hGx => he x (hlev x hx hGx)),
    jf_congr_level p.T.base hgG (fun x hx hGx =>
      fold_congr_open (M.sgn P p.l0) hU hcut hF he w x (hlev x hx hGx))]

theorem limEvT_of_dom (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (Y : Finset ℝ) (N : ℕ)
    (hD : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → DomCut p χ F w) : LimEvT p χ F Y N :=
  limEvT_of_cut p hχ hF Y N (fun w _ _ => pointwise_truncation_locality p hχ hF w) hD

end place

end

end Formalism.FourierDecayAlt.P.CutBP
