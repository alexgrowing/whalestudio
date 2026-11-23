import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.SecondNormalTransport
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.OrthogonalComplementRational
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux
  Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition

open scoped Matrix

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameFirstNormalAdjugate

section Coord

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

theorem hE_comb (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (c : Fin (D.R.rS + 1) → X.B.I.E)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.hE X (famE X u a) (∑ b, c b • (M *ᵥ famE X u' b)) = (ZE X u u' M *ᵥ c) a := by
  rw [← Formalism.L2.SG.Pf.Level.hEl_apply, map_sum]
  simp only [map_smul, Formalism.L2.SG.Pf.Level.hEl_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ZE]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem firstNormal_eq_adjugate (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    nu1E X u u' M = ∑ b, ((ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate b (Fin.last _)) • (M *ᵥ famE X u' b) := by
  unfold nu1E xPrE
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem hermitian_firstNormal (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (hdet : (ZE X u u' M).det ≠ 0)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.hE X (famE X u a) (nu1E X u u' M) = if a = Fin.last _ then 1 else 0 := by
  rw [firstNormal_eq_adjugate, hE_comb]
  simp only [Matrix.mulVec, dotProduct]
  have h1 : ∑ b, ZE X u u' M a b * ((ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate b (Fin.last _)) =
      (ZE X u u' M).det⁻¹ * (ZE X u u' M * (ZE X u u' M).adjugate) a (Fin.last _) := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · field_simp
  · simp

def x2E (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  (star (ZE X u u' M).det)⁻¹ • xUnE X u u' M

theorem hE_sum_left {m : ℕ} (k : Fin m → X.B.I.E) (f : Fin m → Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.hE X (∑ a, star (k a) • f a) y = ∑ a, k a * Formalism.L2.SG.Pf.Level.hE X (f a) y := by
  conv_lhs => rw [Formalism.L2.SG.Pf.Level.hE_symm]
  rw [← Formalism.L2.SG.Pf.Level.hEl_apply, map_sum, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Formalism.L2.SG.Pf.Level.hEl_apply, smul_eq_mul, star_mul', star_star, ← Formalism.L2.SG.Pf.Level.hE_symm]

theorem secondNormal_eq_adjugate (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    x2E X u u' M = ∑ a, star ((ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate (Fin.last _) a) • famE X u a := by
  unfold x2E xUnE
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, star_mul', star_inv₀]

theorem hermitian_secondNormal (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (hdet : (ZE X u u' M).det ≠ 0)
    (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.hE X (x2E X u u' M) (M *ᵥ famE X u' b) = if b = Fin.last _ then 1 else 0 := by
  rw [secondNormal_eq_adjugate, hE_sum_left]
  have h1 : ∑ a, (ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate (Fin.last _) a *
      Formalism.L2.SG.Pf.Level.hE X (famE X u a) (M *ᵥ famE X u' b) =
      (ZE X u u' M).det⁻¹ * ((ZE X u u' M).adjugate * ZE X u u' M) (Fin.last _) b := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by simp only [ZE]; ring
  rw [h1, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with h h' h'
  · field_simp
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · simp

theorem secondNormal_eq_mulVec (M Mi : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : nu2E X u u' M Mi = Mi *ᵥ x2E X u u' M := by
  unfold nu2E x2E
  rw [Matrix.mulVec_smul]

end Coord

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem fvec_mem_xplus (F : FlagG S r T) (a : Fin (r + 1)) : F.fvec a ∈ F.Xplus := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem sum_mem_xplus (F : FlagG S r T) (c : Fin (r + 1) → E) : ∑ a, c a • F.fvec a ∈ F.Xplus :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (fvec_mem_xplus F a)

theorem orth_fvec (F : FlagG S r T) {v : S.V} : v ∈ orth S F.Xplus ↔ ∀ a, S.hT (F.fvec a) v = 0 := by
  rw [PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F]
  constructor
  · rintro ⟨h1, h2⟩ a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa [FlagG.fvec] using h2
    · simpa [FlagG.fvec] using h1 i
  · intro h
    exact ⟨fun i => by simpa [FlagG.fvec] using h i.castSucc, by simpa [FlagG.fvec] using h (Fin.last r)⟩

theorem xplus_sum (F : FlagG S r T) {v : S.V} (hv : v ∈ F.Xplus) : ∃ C : Fin (r + 1) → E, ∑ a, C a • F.fvec a = v := by
  obtain ⟨a', x', hx', e'⟩ := xplus_dec F hv
  obtain ⟨c', hc'⟩ := x_sum F hx'
  exact ⟨Fin.snoc (α := fun _ => E) c' a', by rw [sum_fvec, hc', e']⟩

end Flag

section GT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))

abbrev Mof : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  ((ratM X Y u u' s : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)

abbrev Miof : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (((ratM X Y u u' s)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)

theorem toV_famE (w : D.what₂.Word) (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.toV X (famE X w a) = (X.Fu w).fvec a := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [famE, FlagG.fvec, HidaSetting.zR, Formalism.L2.SG.Pf.Level.toV_crd, X.flagZVector]
  · simp [famE, FlagG.fvec, HidaSetting.eR, Formalism.L2.SG.Pf.Level.toV_crd, X.Fu_e]

theorem lin_iso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem frame_e (b : Fin D.R.rS) : s.frame.fl.e b = s.lin (X.eX b) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dif_pos (lin_iso X Y u u' s)]
  show s.lin ((X.Fu u').e b) = _
  rw [X.Fu_e]

theorem frame_z_eq_lin_zu : s.frame.fl.z = s.lin (X.zu u') := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dif_pos (lin_iso X Y u u' s)]
  show s.lin ((X.Fu u').z) = _
  rw [X.flagZVector]

theorem frame_zt : s.frame.zt = s.frame.fl.z := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dif_pos (lin_iso X Y u u' s)]
  rfl

theorem frame_fvec (b : Fin (D.R.rS + 1)) : s.frame.fl.fvec b = s.lin ((X.Fu u').fvec b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]; rw [frame_z_eq_lin_zu, X.flagZVector]
  · simp only [FlagG.fvec, Fin.snoc_castSucc]; rw [frame_e, X.Fu_e]

theorem lin_toV (x : Fin X.B.I.n → X.B.I.E) :
    s.lin (Formalism.L2.SG.Pf.Level.toV X x) = Formalism.L2.SG.Pf.Level.toV X (Mof X Y u u' s *ᵥ x) := by
  have h := s.rep.2.1.choose_spec.2.2.2 (Formalism.L2.SG.Pf.Level.toV X x)
  rw [Formalism.L2.SG.Pf.Level.crd_toV] at h
  rw [← Formalism.L2.SG.Pf.Level.toV_crd X (s.lin (Formalism.L2.SG.Pf.Level.toV X x))]
  exact congrArg (Formalism.L2.SG.Pf.Level.toV X) h

theorem linsymm_toV (x : Fin X.B.I.n → X.B.I.E) :
    s.lin.symm (Formalism.L2.SG.Pf.Level.toV X x) = Formalism.L2.SG.Pf.Level.toV X (Miof X Y u u' s *ᵥ x) := by
  rw [LinearEquiv.symm_apply_eq, lin_toV, Matrix.mulVec_mulVec, Mof, Miof, Units.mul_inv, Matrix.one_mulVec]

theorem toV_Mfam (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.toV X (Mof X Y u u' s *ᵥ famE X u' b) = s.frame.fl.fvec b := by
  rw [← lin_toV, toV_famE, frame_fvec]

theorem toV_comb (c : Fin (D.R.rS + 1) → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.toV X (∑ b, c b • (Mof X Y u u' s *ᵥ famE X u' b)) = ∑ b, X.ιE (c b) • s.frame.fl.fvec b := by
  rw [Formalism.L2.SG.Pf.Level.toV_sum]
  simp only [Formalism.L2.SG.Pf.Level.toV_smul, toV_Mfam]

theorem toV_combL (c : Fin (D.R.rS + 1) → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.toV X (∑ a, c a • famE X u a) = ∑ a, X.ιE (c a) • (X.Fu u).fvec a := by
  rw [Formalism.L2.SG.Pf.Level.toV_sum]
  simp only [Formalism.L2.SG.Pf.Level.toV_smul, toV_famE]

theorem iota_if (p : Prop) [Decidable p] : X.ιE (if p then 1 else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

theorem firstNormal_mem_Xplus : Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s)) ∈ s.frame.fl.Xplus := by
  rw [firstNormal_eq_adjugate, toV_comb]
  exact sum_mem_xplus _ _

theorem firstNormal_pairing (hdet : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (a : Fin (D.R.rS + 1)) :
    (VS D).hT ((X.Fu u).fvec a) (Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s))) =
      if a = Fin.last _ then 1 else 0 := by
  rw [← toV_famE, ← Formalism.L2.SG.Pf.Level.iota_hE, hermitian_firstNormal X u u' _ hdet, iota_if]

theorem secondNormal_mem_Xplus : Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s)) ∈ (X.Fu u).Xplus := by
  rw [secondNormal_eq_adjugate, toV_combL]
  exact sum_mem_xplus _ _

theorem secondNormal_pairing (hdet : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) (s.frame.fl.fvec b) =
      if b = Fin.last _ then 1 else 0 := by
  rw [← toV_Mfam, ← Formalism.L2.SG.Pf.Level.iota_hE, hermitian_secondNormal X u u' _ hdet, iota_if]

theorem secondNormal_toV : Formalism.L2.SG.Pf.Level.toV X (nu2E X u u' (Mof X Y u u' s) (Miof X Y u u' s)) =
    s.lin.symm (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) := by
  rw [secondNormal_eq_mulVec, linsymm_toV]

theorem ker_of_det (hG : Gflag (X.Fu u) s.frame.fl ≠ 0) (hdet : (ZE X u u' (Mof X Y u u' s)).det = 0) :
    ∃ d ∈ s.frame.fl.Xplus, d ∈ orth (VS D) (X.Fu u).Xplus ∧ d ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨Formalism.L2.SG.Pf.Level.toV X (∑ b, c b • (Mof X Y u u' s *ᵥ famE X u' b)), ?_, ?_, ?_⟩
  · rw [toV_comb]; exact sum_mem_xplus _ _
  · rw [orth_fvec]
    intro a
    rw [← toV_famE, ← Formalism.L2.SG.Pf.Level.iota_hE, hE_comb, hc, Pi.zero_apply, map_zero]
  · intro h
    rw [toV_comb] at h
    have h2 := indep' (X.Fu u) s.frame.fl hG _ h
    apply hc0
    funext b
    have h3 := congrFun h2 b
    simpa using h3

theorem det_of_ker {d : (VS D).V} (hd : d ∈ s.frame.fl.Xplus) (hdO : d ∈ orth (VS D) (X.Fu u).Xplus) (hd0 : d ≠ 0) :
    (ZE X u u' (Mof X Y u u' s)).det = 0 := by
  obtain ⟨C, hC⟩ := xplus_sum _ hd
  set c : Fin (D.R.rS + 1) → X.B.I.E := fun b => X.ιE.symm (C b) with hc
  have hd' : Formalism.L2.SG.Pf.Level.toV X (∑ b, c b • (Mof X Y u u' s *ᵥ famE X u' b)) = d := by
    rw [toV_comb, ← hC]
    simp [c]
  have hZ : ZE X u u' (Mof X Y u u' s) *ᵥ c = 0 := by
    funext a
    apply X.ιE.injective
    rw [← hE_comb, Formalism.L2.SG.Pf.Level.iota_hE, toV_famE, hd', Pi.zero_apply, map_zero]
    exact (orth_fvec _).1 hdO a
  have hc0 : c ≠ 0 := by
    intro h
    apply hd0
    rw [← hd', h]
    simp [Formalism.L2.SG.Pf.Level.toV]
  exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, hZ⟩

theorem det_of_lker {d : (VS D).V} (hd : d ∈ (X.Fu u).Xplus) (hdO : ∀ b, (VS D).hT d (s.frame.fl.fvec b) = 0)
    (hd0 : d ≠ 0) : (ZE X u u' (Mof X Y u u' s)).det = 0 := by
  obtain ⟨C, hC⟩ := xplus_sum _ hd
  set k : Fin (D.R.rS + 1) → X.B.I.E := fun a => star (X.ιE.symm (C a)) with hk
  have hd' : Formalism.L2.SG.Pf.Level.toV X (∑ a, star (k a) • famE X u a) = d := by
    rw [toV_combL, ← hC]
    simp [k]
  have hZ : k ᵥ* ZE X u u' (Mof X Y u u' s) = 0 := by
    funext b
    apply X.ιE.injective
    have e1 : (k ᵥ* ZE X u u' (Mof X Y u u' s)) b =
        Formalism.L2.SG.Pf.Level.hE X (∑ a, star (k a) • famE X u a) (Mof X Y u u' s *ᵥ famE X u' b) := by
      rw [hE_sum_left]
      simp only [Matrix.vecMul, dotProduct, ZE]
    rw [e1, Formalism.L2.SG.Pf.Level.iota_hE, hd', toV_Mfam, Pi.zero_apply, map_zero]
    exact hdO b
  have hk0 : k ≠ 0 := by
    intro h
    apply hd0
    rw [← hd', h]
    simp [Formalism.L2.SG.Pf.Level.toV]
  exact Matrix.exists_vecMul_eq_zero_iff.1 ⟨k, hk0, hZ⟩

theorem uue_le {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    UUE Λ F F' ≤ F.fl.Xplus ⊔ F'.fl.Xplus := by
  unfold UUE spanE
  rw [Submodule.span_le]
  have h : UU Λ F F' ≤ (F.fl.Xplus ⊔ F'.fl.Xplus).restrictScalars (𝓞 D.host.E) := by
    unfold UU
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans (fun v hv => Submodule.mem_sup_left (Submodule.mem_sup_left hv))
    · rw [Submodule.span_le, Set.singleton_subset_iff, hz]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact inf_le_right.trans (fun v hv => Submodule.mem_sup_right (Submodule.mem_sup_left hv))
    · rw [Submodule.span_le, Set.singleton_subset_iff, hz']
      exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  exact fun v hv => h hv

theorem orthogonal_toV {Λ : Submodule (𝓞 D.host.E) (VS D).V} {y : Fin X.B.I.n → X.B.I.E}
    (hy : orthogonalComplementRational X u u' (Mof X Y u u' s) y) :
    Formalism.L2.SG.Pf.Level.toV X y ∈ Hp Λ (lf D (X.Fu u)) s.frame := by
  have h1 : ∀ a, (VS D).hT ((X.Fu u).fvec a) (Formalism.L2.SG.Pf.Level.toV X y) = 0 := fun a => by
    rw [← toV_famE, ← Formalism.L2.SG.Pf.Level.iota_hE, hy.1 a, map_zero]
  have h2 : ∀ b, (VS D).hT (s.frame.fl.fvec b) (Formalism.L2.SG.Pf.Level.toV X y) = 0 := fun b => by
    rw [← toV_Mfam, ← Formalism.L2.SG.Pf.Level.iota_hE, hy.2 b, map_zero]
  have o1 := (orth_fvec (X.Fu u)).2 h1
  have o2 := (orth_fvec s.frame.fl).2 h2
  apply PI.UnitaryGroupMassFormula.ScalEquivGen.orthAntiQ (uue_le (Λ := Λ) (lf D (X.Fu u)) s.frame rfl (frame_zt X Y u u' s))
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ]
  intro x hx
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, LinearMap.add_apply, PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp o1 x1 hx1,
    PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp o2 x2 hx2, add_zero]

theorem orthogonal_ofV {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (hL : IsLift Λ (lf D (X.Fu u))) (hL' : IsLift Λ s.frame) {y : (VS D).V}
    (hy : y ∈ Hp Λ (lf D (X.Fu u)) s.frame) : orthogonalComplementRational X u u' (Mof X Y u u' s) (X.crd y) := by
  have hm := PI.PairCorankPos.W.frame_mem_UUE Λ hΛ (lf D (X.Fu u)) s.frame hL hL'
  have hy' : ∀ x ∈ UUE Λ (lf D (X.Fu u)) s.frame, (VS D).hT x y = 0 := PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp hy
  refine ⟨fun a => ?_, fun b => ?_⟩
  · apply X.ιE.injective
    rw [Formalism.L2.SG.Pf.Level.iota_hE, toV_famE, Formalism.L2.SG.Pf.Level.toV_crd, map_zero]
    exact hy' _ (hm (Sum.inl a))
  · apply X.ιE.injective
    rw [Formalism.L2.SG.Pf.Level.iota_hE, toV_Mfam, Formalism.L2.SG.Pf.Level.toV_crd, map_zero]
    exact hy' _ (hm (Sum.inr b))

theorem wperp_of (w : D.what₂.Word) {x : Fin X.B.I.n → X.B.I.E}
    (h : Formalism.L2.SG.Pf.Level.toV X x ∈ Submodule.span D.host.E (Set.range X.eX)) : x ∈ WperpE X w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have e : x = ∑ i, X.ιE.symm (c i) • X.eR i := by
    rw [← Formalism.L2.SG.Pf.Level.crd_toV X x, ← Formalism.L2.SG.Pf.Level.crd_toV X (∑ i, X.ιE.symm (c i) • X.eR i)]
    congr 1
    rw [Formalism.L2.SG.Pf.Level.toV_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.SG.Pf.Level.toV_smul, HidaSetting.eR, Formalism.L2.SG.Pf.Level.toV_crd, RingEquiv.apply_symm_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))

theorem fixedX (v : (VS D).V) (hv : v ∈ (X.Fu u).X) : v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  simpa [FlagG.X, X.Fu_e] using hv

theorem symm_frameX {v : (VS D).V} (hv : v ∈ s.frame.fl.X) : s.lin.symm v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  obtain ⟨c, hc⟩ := x_sum _ hv
  rw [← hc, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, frame_e, LinearEquiv.symm_apply_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GT

end Formalism.L2.SG.Pf.RowForm.ClassFrameFirstNormalAdjugate
