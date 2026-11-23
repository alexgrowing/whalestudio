import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SmatUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClmEqZeroOfSpan

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf.UkEmb

namespace PI.SchurPlaces.Geo

open PI.SchurPlaces Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {n k : ℕ} (ε : Fin n → Bool)

theorem hJ_eq (x y : Fin n → ℂ) : hJ ε x y = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := rfl

theorem hJ_symm (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  simp only [hJ, dotProduct, Formalism.REAL.Jm, mulVec_diagonal, Pi.star_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem hJ_add_right (x y z : Fin n → ℂ) : hJ ε x (y + z) = hJ ε x y + hJ ε x z := by
  simp only [hJ, mulVec_add, dotProduct_add]

theorem hJ_sub_right (x y z : Fin n → ℂ) : hJ ε x (y - z) = hJ ε x y - hJ ε x z := by
  simp only [hJ, mulVec_sub, dotProduct_sub]

theorem hJ_smul_right (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp only [hJ, mulVec_zero, dotProduct_zero]

theorem hJ_sum_right {ι : Type} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  refine Finset.induction_on s (by simp only [Finset.sum_empty, hJ_zero_right]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_right, ih]

theorem hJ_add_left (x y z : Fin n → ℂ) : hJ ε (x + y) z = hJ ε x z + hJ ε y z := by
  simp only [hJ, star_add, add_dotProduct]

theorem hJ_sub_left (x y z : Fin n → ℂ) : hJ ε (x - y) z = hJ ε x z - hJ ε y z := by
  simp only [hJ, star_sub, sub_dotProduct]

theorem hJ_smul_left (x y : Fin n → ℂ) (c : ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, x i) y = ∑ i ∈ s, hJ ε (x i) y := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, hJ, star_zero, zero_dotProduct]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_left, ih]

theorem hJ_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  simp only [hJ]
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hg,
    ← dotProduct_mulVec]

theorem smat_apply (wf : Fin k → Fin n → ℂ) (G : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    smat (Formalism.REAL.Jm ε) wf G *ᵥ y = y + ∑ c, ((G - 1) *ᵥ fun d => hJ ε (wf d) y) c • wf c := by
  have hw : (Wm wf)ᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = fun d => hJ ε (wf d) y := by
    funext d
    simp only [hJ, mulVec, dotProduct, Wm, conjTranspose_apply, of_apply, Pi.star_apply]
  funext i
  simp only [smat]
  rw [add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hw]
  simp only [Pi.add_apply, mulVec, dotProduct, Wm, of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]

end Lin

section Rat

variable {D : D7} (X : HidaSetting D)

abbrev rvc (v : InfinitePlace X.B.I.F) (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem crd_add (p p' : (VS D).V) : X.crd (p + p') = X.crd p + X.crd p' := by
  funext i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, map_add, Finsupp.add_apply, Pi.add_apply]

theorem crd_smul (c : D.host.E) (p : (VS D).V) : X.crd (c • p) = X.ιE.symm c • X.crd p := by
  funext i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, map_smul, Finsupp.smul_apply,
    smul_eq_mul, map_mul, Pi.smul_apply]

theorem rvc_add (v : InfinitePlace X.B.I.F) (p p' : (VS D).V) : rvc X v (p + p') = rvc X v p + rvc X v p' := by
  simp only [rvc, crd_add, Formalism.L2.SG.HidaSetting.rv]
  rw [← mulVec_add]
  congr 1
  funext i
  simp only [Pi.add_apply, map_add]

theorem rvc_smul (v : InfinitePlace X.B.I.F) (c : D.host.E) (p : (VS D).V) :
    rvc X v (c • p) = X.B.I.φ v (X.ιE.symm c) • rvc X v p := by
  simp only [rvc, crd_smul, Formalism.L2.SG.HidaSetting.rv]
  rw [← mulVec_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem rvc_zero (v : InfinitePlace X.B.I.F) : rvc X v 0 = 0 := by
  simpa using rvc_smul X v (0 : D.host.E) 0

theorem orth_span (v : InfinitePlace X.B.I.F) (w : Fin X.B.I.n → ℂ) {S : Set (VS D).V}
    (h : ∀ s ∈ S, hJ (X.B.I.ε v) (rvc X v s) w = 0) :
    ∀ p ∈ Submodule.span D.host.E S, hJ (X.B.I.ε v) (rvc X v p) w = 0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp only [rvc_zero, hJ, star_zero, zero_dotProduct]
  | add x y _ _ hx hy => rw [rvc_add, hJ_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [rvc_smul, hJ_smul_left, hx, mul_zero]

theorem spanAt_orth (v : InfinitePlace X.B.I.F) (U : Submodule D.host.E (VS D).V) (w : Fin X.B.I.n → ℂ)
    (h : ∀ p ∈ U, hJ (X.B.I.ε v) (rvc X v p) w = 0) : ∀ y ∈ spanAt X v U, hJ (X.B.I.ε v) y w = 0 := by
  intro y hy
  unfold spanAt at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact h p hp
  | zero => simp only [hJ, star_zero, zero_dotProduct]
  | add x y _ _ hx hy => rw [hJ_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [hJ_smul_left, hx, mul_zero]

theorem spanAt_orth' (v : InfinitePlace X.B.I.F) (U : Submodule D.host.E (VS D).V) (w : Fin X.B.I.n → ℂ)
    (h : ∀ p ∈ U, hJ (X.B.I.ε v) (rvc X v p) w = 0) : ∀ y ∈ spanAt X v U, hJ (X.B.I.ε v) w y = 0 := by
  intro y hy
  rw [hJ_symm, spanAt_orth X v U w h y hy, star_zero]

theorem spanAt_mono (v : InfinitePlace X.B.I.F) {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') :
    spanAt X v U ≤ spanAt X v U' := by
  unfold spanAt
  exact Submodule.span_mono fun _ ⟨q, hq, e⟩ => ⟨q, h hq, e⟩

theorem rvc_mem (v : InfinitePlace X.B.I.F) {U : Submodule D.host.E (VS D).V} {p : (VS D).V} (hp : p ∈ U) :
    rvc X v p ∈ spanAt X v U := by
  unfold spanAt
  exact Submodule.subset_span ⟨p, hp, rfl⟩

theorem hJ_rvc (v : InfinitePlace X.B.I.F) (p p' : (VS D).V) :
    hJ (X.B.I.ε v) (rvc X v p) (rvc X v p') = X.B.I.φ v (X.ιE.symm ((VS D).hT p p')) := by
  rw [X.φ_eq, RingEquiv.apply_symm_apply]
  first
  | exact Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p p'
  | exact Formalism.L2.SG.PoincareInHH.Cut.hJ_crd v p p'
  | exact Formalism.L2.SG.PoincareInHH.Cut.hJ_crd (X := X) v p p'

theorem hJ_rvc_zero (v : InfinitePlace X.B.I.F) {p p' : (VS D).V} (h : (VS D).hT p p' = 0) :
    hJ (X.B.I.ε v) (rvc X v p) (rvc X v p') = 0 := by
  rw [hJ_rvc, h, map_zero, map_zero]

theorem hJ_rvc_one (v : InfinitePlace X.B.I.F) {p p' : (VS D).V} (h : (VS D).hT p p' = 1) :
    hJ (X.B.I.ε v) (rvc X v p) (rvc X v p') = 1 := by
  rw [hJ_rvc, h, map_one, map_one]

theorem Xplus_span {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) :
    F.Xplus = Submodule.span D.host.E (Set.range F.e ∪ {F.z}) := by
  rw [Submodule.span_union]
  rfl

end Rat

section Main

def sUg {n k : ℕ} (ε : Fin n → Bool) (wf : Fin k → Fin n → ℂ)
    (hon : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    Formalism.REAL.UJ ε :=
  ⟨⟨smat (Formalism.REAL.Jm ε) wf G, Formalism.REAL.Jm ε * (smat (Formalism.REAL.Jm ε) wf G)ᴴ * Formalism.REAL.Jm ε,
    mul_eq_one_comm.1 (smat_inv _ _ (Formalism.REAL.Jm_mul_self _) (Formalism.REAL.Jm_conjTranspose _) G hG hon),
    smat_inv _ _ (Formalism.REAL.Jm_mul_self _) (Formalism.REAL.Jm_conjTranspose _) G hG hon⟩,
    smat_unitary _ _ hon (Formalism.REAL.Jm_conjTranspose _) G hG⟩

theorem uMat_sUg {n k : ℕ} (ε : Fin n → Bool) (wf : Fin k → Fin n → ℂ)
    (hon : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    uMat (sUg ε wf hon G hG) = smat (Formalism.REAL.Jm ε) wf G := rfl

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  rfl

theorem uMat_inv_mul'' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  exact Units.inv_mul (a : (Matrix (Fin n) (Fin n) ℂ)ˣ)

theorem uMat_mul_inv'' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  exact Units.mul_inv (a : (Matrix (Fin n) (Fin n) ℂ)ˣ)

theorem uMat_unit {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) :
    (uMat a)ᴴ * Formalism.REAL.Jm ε * uMat a = Formalism.REAL.Jm ε := by
  exact a.2

theorem sub_one_mulVec_fix {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ} (h : g *ᵥ y = y) :
    (g - 1) *ᵥ y = 0 := by
  rw [sub_mulVec, one_mulVec, h, sub_self]

theorem geomB_of (hL : LeviTens) (hW : WfrSpan) (hN : CplxNF) : GeomB := by
  intro D X u u' Λ Λ' q hrel hG

  have hFXp : (lf D (X.Fu u)).fl.Xplus ≤ fixedSubspaceOfRepresentative X q := le_sup_left
  have hF'Xp : (frq X q).fl.Xplus ≤ fixedSubspaceOfRepresentative X q := le_sup_right
  have hFX : (lf D (X.Fu u)).fl.X ≤ fixedSubspaceOfRepresentative X q := le_trans (by unfold FlagG.Xplus; exact le_sup_left) hFXp
  have hF'X : (frq X q).fl.X ≤ fixedSubspaceOfRepresentative X q := le_trans (by unfold FlagG.Xplus; exact le_sup_left) hF'Xp
  have he : ∀ a, X.eX a ∈ (lf D (X.Fu u)).fl.X := by
    intro a
    show X.eX a ∈ (X.Fu u).X
    rw [← X.Fu_e u]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hz : X.zu u ∈ (lf D (X.Fu u)).fl.Xplus := by
    show X.zu u ∈ (X.Fu u).Xplus
    rw [← X.flagZVector u]
    unfold FlagG.Xplus
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hiso := q.2.2.1
  have hfrq : (frq X q).fl = mapFlag q.1.2 hiso (lf D (X.Fu u')).fl := by
    unfold frq mapLF
    rw [dif_pos hiso]
    rfl
  have he' : ∀ a, q.1.2 (X.eX a) ∈ (frq X q).fl.X := by
    intro a
    rw [hfrq]
    have : q.1.2 (X.eX a) = (mapFlag q.1.2 hiso (lf D (X.Fu u')).fl).e a := by
      simp only [mapFlag, lf]; rw [X.Fu_e u']
    rw [this]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hz' : q.1.2 (X.zu u') ∈ (frq X q).fl.Xplus := by
    rw [hfrq]
    have : q.1.2 (X.zu u') = (mapFlag q.1.2 hiso (lf D (X.Fu u')).fl).z := by
      simp only [mapFlag, lf]; exact congrArg _ (X.flagZVector u').symm
    rw [this]
    unfold FlagG.Xplus
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

  obtain ⟨Mq, -, hMv, -, hcrd⟩ := q.2.1
  have hγ : ∀ v p, uMat (q.1.1.1 v) *ᵥ rvc X v p = rvc X v (q.1.2 p) := by
    intro v p
    rw [hMv v]
    show _ *ᵥ rv X.B.I v (X.crd p) = rv X.B.I v (X.crd (q.1.2 p))
    rw [Formalism.L2.SG.Pf.rv_mulVec, ← hcrd]

  have hwp : ∀ v b, ∀ p ∈ (lf D (X.Fu u)).fl.Xplus, hJ (X.B.I.ε v) (rvc X v p) (X.wfr u v b) = 0 := by
    intro v b p hp
    rw [Xplus_span] at hp
    refine orth_span X v _ ?_ p hp
    rintro s (⟨a, rfl⟩ | hs)
    · show hJ _ (rv X.B.I v (X.crd ((X.Fu u).e a))) _ = 0
      rw [X.Fu_e u]
      exact ((X.wfr_perp u v b).1 a).1
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      show hJ _ (rv X.B.I v (X.crd (X.Fu u).z)) _ = 0
      rw [X.flagZVector u]
      exact (X.wfr_perp u v b).2
  have hwp' : ∀ v b, ∀ p ∈ (frq X q).fl.Xplus,
      hJ (X.B.I.ε v) (rvc X v p) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v b) = 0 := by
    intro v b p hp
    rw [Xplus_span, hfrq] at hp
    refine orth_span X v _ ?_ p hp
    rintro s (⟨a, rfl⟩ | hs)
    · show hJ _ (rvc X v (q.1.2 ((lf D (X.Fu u')).fl.e a))) _ = 0
      rw [← hγ, hJ_unitary _ (uMat_unit _)]
      show hJ _ (rv X.B.I v (X.crd ((X.Fu u').e a))) _ = 0
      rw [X.Fu_e u']
      exact ((X.wfr_perp u' v b).1 a).1
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      show hJ _ (rvc X v (q.1.2 ((lf D (X.Fu u')).fl.z))) _ = 0
      rw [← hγ, hJ_unitary _ (uMat_unit _)]
      show hJ _ (rv X.B.I v (X.crd (X.Fu u').z)) _ = 0
      rw [X.flagZVector u']
      exact (X.wfr_perp u' v b).2

  have ex1 : ∀ v b, ∃ x ∈ spanAt X v (lf D (X.Fu u)).fl.X,
      ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) (X.wfr u v b - x) = 0 :=
    fun v b => (hN D X u u' Λ Λ' q hrel hG v).1 _ (hwp v b)
  have ex2 : ∀ v b, ∃ x ∈ spanAt X v (frq X q).fl.X,
      ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v b - x) = 0 :=
    fun v b => (hN D X u u' Λ Λ' q hrel hG v).2.1 _ (hwp' v b)
  choose x hx hxo using ex1
  choose x' hx' hx'o using ex2
  have hXXp : ∀ {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T), F.X ≤ F.Xplus := fun F => by
    unfold FlagG.Xplus; exact le_sup_left
  obtain ⟨wt, hwt⟩ : ∃ wt : ∀ v : InfinitePlace X.B.I.F, Fin D.R.k → Fin X.B.I.n → ℂ,
      ∀ v b, wt v b = X.wfr u v b - x v b := ⟨_, fun _ _ => rfl⟩
  obtain ⟨wt', hwt'⟩ : ∃ wt' : ∀ v : InfinitePlace X.B.I.F, Fin D.R.k → Fin X.B.I.n → ℂ,
      ∀ v b, wt' v b = uMat (q.1.1.1 v) *ᵥ X.wfr u' v b - x' v b := ⟨_, fun _ _ => rfl⟩
  have hwo : ∀ v b, ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) (wt v b) = 0 := by
    intro v b p hp; rw [hwt]; exact hxo v b p hp
  have hwo' : ∀ v b, ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) (wt' v b) = 0 := by
    intro v b p hp; rw [hwt']; exact hx'o v b p hp
  have hxV : ∀ v b, x v b ∈ spanAt X v (fixedSubspaceOfRepresentative X q) := fun v b => spanAt_mono X v hFX (hx v b)
  have hx'V : ∀ v b, x' v b ∈ spanAt X v (fixedSubspaceOfRepresentative X q) := fun v b => spanAt_mono X v hF'X (hx' v b)
  have hwtx : ∀ v c, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) (wt v c) y = 0 :=
    fun v c => spanAt_orth' X v _ (wt v c) (hwo v c)
  have hxwt : ∀ v c, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) y (wt v c) = 0 :=
    fun v c => spanAt_orth X v _ (wt v c) (hwo v c)
  have hxwt' : ∀ v c, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) y (wt' v c) = 0 :=
    fun v c => spanAt_orth X v _ (wt' v c) (hwo' v c)
  have hwfrX : ∀ v a, ∀ y ∈ spanAt X v (lf D (X.Fu u)).fl.X, hJ (X.B.I.ε v) (X.wfr u v a) y = 0 :=
    fun v a => spanAt_orth' X v _ _ (fun p hp => hwp v a p (hXXp _ hp))
  have hwhX : ∀ v a, ∀ y ∈ spanAt X v (frq X q).fl.X,
      hJ (X.B.I.ε v) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v a) y = 0 :=
    fun v a => spanAt_orth' X v _ _ (fun p hp => hwp' v a p (hXXp _ hp))
  have hw : ∀ v b, X.wfr u v b = wt v b + x v b := fun v b => by rw [hwt]; abel
  have hw' : ∀ v b, uMat (q.1.1.1 v) *ᵥ X.wfr u' v b = wt' v b + x' v b := fun v b => by rw [hwt']; abel

  have hon : ∀ v a b, hJ (X.B.I.ε v) (wt v a) (wt v b) = if a = b then 1 else 0 := by
    intro v a b
    have e1 : hJ (X.B.I.ε v) (wt v a) (wt v b) = hJ (X.B.I.ε v) (X.wfr u v a) (wt v b) := by
      rw [hwt v a, hJ_sub_left, hxwt v b (x v a) (hxV v a), sub_zero]
    rw [e1, hwt v b, hJ_sub_right, hwfrX v a (x v b) (hx v b), sub_zero]
    exact X.wfr_on u v a b
  have hon' : ∀ v a b, hJ (X.B.I.ε v) (wt' v a) (wt' v b) = if a = b then 1 else 0 := by
    intro v a b
    have e1 : hJ (X.B.I.ε v) (wt' v a) (wt' v b) =
        hJ (X.B.I.ε v) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v a) (wt' v b) := by
      rw [hwt' v a, hJ_sub_left, hxwt' v b (x' v a) (hx'V v a), sub_zero]
    rw [e1, hwt' v b, hJ_sub_right, hwhX v a (x' v b) (hx' v b), sub_zero, hJ_unitary _ (uMat_unit _)]
    exact X.wfr_on u' v a b

  obtain ⟨K, hK⟩ : ∃ K : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ,
      ∀ v c a, K v c a = hJ (X.B.I.ε v) (wt v c) (wt' v a) := ⟨fun v => Matrix.of fun c a => _, fun _ _ _ => rfl⟩
  have KK : ∀ v, (K v)ᴴ * K v = 1 := by
    intro v
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply]
    have yperp := hwo' v a
    obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin X.B.I.n → ℂ,
        ξ = ∑ c, hJ (X.B.I.ε v) (rvc X v (X.fY c)) (wt' v a) • rvc X v (X.eX c) := ⟨_, rfl⟩
    have hee : ∀ a c, hJ (X.B.I.ε v) (rvc X v (X.eX a)) (rvc X v (X.eX c)) = 0 :=
      fun a c => hJ_rvc_zero X v (X.ee a c)
    have hfe : ∀ a c, hJ (X.B.I.ε v) (rvc X v (X.fY a)) (rvc X v (X.eX c)) = if c = a then 1 else 0 := by
      intro a c
      rw [hJ_symm, hJ_rvc, X.ef c a]
      split_ifs <;> simp
    have hze : ∀ c, hJ (X.B.I.ε v) (rvc X v (X.zu u)) (rvc X v (X.eX c)) = 0 := by
      intro c
      rw [hJ_symm, hJ_rvc_zero X v (X.zu_orth u c).1, star_zero]
    have hwe : ∀ b c, hJ (X.B.I.ε v) (X.wfr u v b) (rvc X v (X.eX c)) = 0 := by
      intro b c
      rw [hJ_symm, hwp v b _ (hXXp _ (he c)), star_zero]
    have hexp : ∀ w, hJ (X.B.I.ε v) w (wt' v a - ξ) =
        hJ (X.B.I.ε v) w (wt' v a) - ∑ c, hJ (X.B.I.ε v) (rvc X v (X.fY c)) (wt' v a) *
          hJ (X.B.I.ε v) w (rvc X v (X.eX c)) := by
      intro w
      rw [hξ, hJ_sub_right, hJ_sum_right]
      simp_rw [hJ_smul_right]
    have h1 := hW D X u v (wt' v a - ξ) (fun a' => ⟨?_, ?_⟩) ?_
    rotate_left
    · show hJ _ (rvc X v (X.eX a')) _ = 0
      rw [hexp, yperp _ (hFX (he a'))]
      simp [hee]
    · show hJ _ (rvc X v (X.fY a')) _ = 0
      rw [hexp]
      simp_rw [hfe]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    · show hJ _ (rvc X v (X.zu u)) _ = 0
      rw [hexp, yperp _ (hFXp hz)]
      simp [hze]
    have hcoef : ∀ b, hJ (X.B.I.ε v) (X.wfr u v b) (wt' v a - ξ) = K v b a := by
      intro b
      rw [hexp]
      simp only [hwe, mul_zero, Finset.sum_const_zero, sub_zero]
      rw [hw v b, hJ_add_left, spanAt_orth X v _ _ yperp _ (hxV v b), add_zero, hK]
    simp_rw [hcoef] at h1
    obtain ⟨η, hη⟩ : ∃ η : Fin X.B.I.n → ℂ, η = wt' v a - ∑ c, K v c a • wt v c := ⟨_, rfl⟩
    have hη1 : η = ξ + ∑ c, K v c a • x v c := by
      have e : wt' v a = ξ + ∑ c, K v c a • (wt v c + x v c) := by
        rw [← sub_add_cancel (wt' v a) ξ, h1, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by rw [hw v c]
      rw [hη, e]
      simp only [smul_add, Finset.sum_add_distrib]
      abel
    have hηX : η ∈ spanAt X v (lf D (X.Fu u)).fl.X := by
      rw [hη1, hξ]
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (rvc_mem X v (he c)))
        (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hx v c))
    have hηp : ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) η = 0 := by
      intro p hp
      rw [hη, hJ_sub_right, hJ_sum_right, yperp p hp]
      simp [hJ_smul_right, hwo v _ p hp]
    have hηI := (hN D X u u' Λ Λ' q hrel hG v).2.2 η hηX hηp
    have hηw : hJ (X.B.I.ε v) η (wt' v b) = 0 :=
      spanAt_orth X v _ (wt' v b) (fun p hp => hwo' v b p (hF'X (Submodule.mem_inf.1 hp).2)) η hηI
    calc ∑ c, star (K v c a) * K v c b = hJ (X.B.I.ε v) (∑ c, K v c a • wt v c) (wt' v b) := by
          rw [hJ_sum_left]
          simp_rw [hJ_smul_left, hK]
      _ = hJ (X.B.I.ε v) (wt' v a) (wt' v b) := by
          have e : wt' v a = η + ∑ c, K v c a • wt v c := by rw [hη, sub_add_cancel]
          rw [e, hJ_add_left, hηw, zero_add]
      _ = _ := hon' v a b
  have hC : ∀ v, (K v)ᴴ ∈ UJset (allPos D.R.k) := by
    intro v
    rw [memU_iff, Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 (KK v)
  refine ⟨fun v => (K v)ᴴ, hC, fun M hM => ?_⟩
  have hMu : ∀ v, (M v)ᴴ * M v = 1 := fun v => (memU_iff _).1 (hM v)
  let h : X.B.I.Ginf := fun v => sUg (X.B.I.ε v) (wt v) (hon v) (M v) (hMu v)
  have hh : ∀ v, uMat (h v) = smat (Formalism.REAL.Jm (X.B.I.ε v)) (wt v) (M v) := fun v => rfl
  have hfix : ∀ v y, (∀ c, hJ (X.B.I.ε v) (wt v c) y = 0) → uMat (h v) *ᵥ y = y :=
    fun v y hy => by rw [hh]; exact smat_fix _ _ (hon v) _ _ hy
  have hfixV : ∀ v, ∀ p ∈ fixedSubspaceOfRepresentative X q, uMat (h v) *ᵥ rvc X v p = rvc X v p :=
    fun v p hp => hfix v _ (fun c => by rw [hJ_symm, hwo v c p hp, star_zero])
  have hfixS : ∀ v, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), uMat (h v) *ᵥ y = y :=
    fun v y hy => hfix v y (fun c => hwtx v c y hy)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro v y hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact hfixV v p hp
  · have hS : h ∈ X.SinfU u := by
      show ∀ v, InS _ _ _
      intro v
      refine ⟨fun a => ?_, ?_⟩
      · show (uMat (h v) - 1) *ᵥ rvc X v (X.eX a) ∈ _
        rw [sub_one_mulVec_fix (hfixV v _ (hFX (he a)))]
        exact Submodule.zero_mem _
      · show (uMat (h v) - 1) *ᵥ rvc X v (X.zu u) ∈ _
        rw [sub_one_mulVec_fix (hfixV v _ (hFXp hz))]
        exact Submodule.zero_mem _
    have hmat : ∀ v, matW X.B.I (X.wfr u v) v h = M v := by
      intro v
      funext a b
      show hJ (X.B.I.ε v) (X.wfr u v a) (uMat (h v) *ᵥ X.wfr u v b) = M v a b
      rw [hw v b, Matrix.mulVec_add, hfixS v _ (hxV v b), hJ_add_right, hwfrX v a _ (hx v b), add_zero,
        hw v a, hJ_add_left]
      have e1 : hJ (X.B.I.ε v) (x v a) (uMat (h v) *ᵥ wt v b) = 0 := by
        have hu := hJ_unitary (X.B.I.ε v) (uMat_unit (h v)) (x v a) (wt v b)
        rw [hfixS v _ (hxV v a)] at hu
        rw [hu]
        exact hxwt v b _ (hxV v a)
      rw [e1, add_zero, hh]
      exact smat_mat _ _ (hon v) (M v) a b
    intro y
    rw [hL D X u h hS y]
    simp only [hmat]
  · let h' : X.B.I.Ginf := q.1.1.1⁻¹ * h * q.1.1.1
    have hh' : ∀ v, uMat (h' v) = uMat (q.1.1.1 v)⁻¹ * uMat (h v) * uMat (q.1.1.1 v) := by
      intro v
      show uMat ((q.1.1.1 v)⁻¹ * h v * q.1.1.1 v) = _
      rw [uMat_mul', uMat_mul']
    have hfix' : ∀ v p, q.1.2 p ∈ fixedSubspaceOfRepresentative X q → uMat (h' v) *ᵥ rvc X v p = rvc X v p := by
      intro v p hp
      rw [hh', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ, hfixV v _ hp, ← hγ, Matrix.mulVec_mulVec,
        uMat_inv_mul'', Matrix.one_mulVec]
    have hS' : h' ∈ X.SinfU u' := by
      show ∀ v, InS _ _ _
      intro v
      refine ⟨fun a => ?_, ?_⟩
      · show (uMat (h' v) - 1) *ᵥ rvc X v (X.eX a) ∈ _
        rw [sub_one_mulVec_fix (hfix' v _ (hF'X (he' a)))]
        exact Submodule.zero_mem _
      · show (uMat (h' v) - 1) *ᵥ rvc X v (X.zu u') ∈ _
        rw [sub_one_mulVec_fix (hfix' v _ (hF'Xp hz'))]
        exact Submodule.zero_mem _
    have hmat' : ∀ v, matW X.B.I (X.wfr u' v) v h' = (K v)ᴴ * M v * ((K v)ᴴ)ᴴ := by
      intro v
      funext a b
      show hJ (X.B.I.ε v) (X.wfr u' v a) (uMat (h' v) *ᵥ X.wfr u' v b) = _
      rw [Matrix.conjTranspose_conjTranspose]
      have e0 : hJ (X.B.I.ε v) (X.wfr u' v a) (uMat (h' v) *ᵥ X.wfr u' v b) =
          hJ (X.B.I.ε v) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v a) (uMat (h v) *ᵥ (uMat (q.1.1.1 v) *ᵥ X.wfr u' v b)) := by
        rw [← hJ_unitary _ (uMat_unit (q.1.1.1 v)) (X.wfr u' v a), hh']
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (uMat (q.1.1.1 v)) (uMat (q.1.1.1 v)⁻¹), uMat_mul_inv'', Matrix.one_mul]
      have hsa : uMat (h v) *ᵥ wt' v b =
          wt' v b + ∑ c, ((M v - 1) *ᵥ fun d : Fin D.R.k => K v d b) c • wt v c := by
        rw [hh, smat_apply]
        simp only [← hK]
      have hwa : ∀ c, hJ (X.B.I.ε v) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v a) (wt v c) = star (K v c a) := by
        intro c
        rw [hw' v a, hJ_add_left, hxwt v c _ (hx'V v a), add_zero, hK, hJ_symm]
      have lhs : hJ (X.B.I.ε v) (uMat (q.1.1.1 v) *ᵥ X.wfr u' v a)
          (uMat (h v) *ᵥ (uMat (q.1.1.1 v) *ᵥ X.wfr u' v b)) =
          (if a = b then 1 else 0) + ∑ c, star (K v c a) * ((M v - 1) *ᵥ fun d : Fin D.R.k => K v d b) c := by
        have e2 : uMat (h v) *ᵥ (uMat (q.1.1.1 v) *ᵥ X.wfr u' v b) =
            (wt' v b + x' v b) + ∑ c, ((M v - 1) *ᵥ fun d : Fin D.R.k => K v d b) c • wt v c := by
          rw [hw' v b, Matrix.mulVec_add, hfixS v _ (hx'V v b), hsa]
          abel
        rw [e2, hJ_add_right, ← hw' v b, hJ_unitary _ (uMat_unit _), X.wfr_on u' v a b, hJ_sum_right]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hJ_smul_right, hwa, mul_comm]
      have rhs : ((K v)ᴴ * M v * K v) a b =
          (if a = b then 1 else 0) + ∑ c, star (K v c a) * ((M v - 1) *ᵥ fun d : Fin D.R.k => K v d b) c := by
        have hid : (K v)ᴴ * M v * K v = 1 + (K v)ᴴ * ((M v - 1) * K v) := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, KK v, ← Matrix.mul_assoc]
          abel
        rw [hid, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply]
        congr 1
      rw [e0, lhs, rhs]
    intro y
    rw [hL D X u' h' hS' y]
    simp only [hmat']

end Main

end PI.SchurPlaces.Geo
