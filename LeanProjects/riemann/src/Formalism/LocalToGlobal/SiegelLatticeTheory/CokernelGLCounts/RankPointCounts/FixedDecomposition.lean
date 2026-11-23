import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurNFCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HaarRelevantTerms
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShiftCore

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf.UkEmb

namespace Formalism.L2.SG.FixedDecomposition

open PI.SchurPlaces PI.SchurPlaces.Geo Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.TermOp.Vanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FixedDecompositionZero : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), t.relevant → t.G = 0 →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ k n : X.B.I.Ginf, h = k * n ∧ n ∈ Rset t ∧ (∀ r, r ∈ Rset t ↔ k⁻¹ * r * k ∈ Rset t) ∧
      ∃ C : Set X.B.I.Ginf, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C

section Smat

variable {n k : ℕ} (ε : Fin n → Bool) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)

include hon in
theorem coef_smat (G : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    (fun d => hJ ε (wf d) (smat (Formalism.REAL.Jm ε) wf G *ᵥ y)) = G *ᵥ fun d => hJ ε (wf d) y := by
  funext d
  rw [smat_apply, hJ_add_right, hJ_sum_right]
  simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_mulVec, one_mulVec]
  simp only [Pi.sub_apply]
  ring

include hon in
theorem smat_mul (G G' : Matrix (Fin k) (Fin k) ℂ) :
    smat (Formalism.REAL.Jm ε) wf G * smat (Formalism.REAL.Jm ε) wf G' = smat (Formalism.REAL.Jm ε) wf (G * G') := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
  rw [smat_apply ε wf G (smat (Formalism.REAL.Jm ε) wf G' *ᵥ y), coef_smat ε wf hon G', smat_apply ε wf G' y,
    smat_apply ε wf (G * G') y]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← add_smul]
  congr 1
  simp only [sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Pi.sub_apply]
  ring

theorem smat_one : smat (Formalism.REAL.Jm ε) wf 1 = 1 := by
  simp [smat]

def sU (M : {G : Matrix (Fin k) (Fin k) ℂ // Gᴴ * G = 1}) : Formalism.REAL.UJ ε := sUg ε wf hon M.1 M.2

theorem sU_mul (M M' : {G : Matrix (Fin k) (Fin k) ℂ // Gᴴ * G = 1}) (hMM : (M.1 * M'.1)ᴴ * (M.1 * M'.1) = 1) :
    sU ε wf hon M * sU ε wf hon M' = sU ε wf hon ⟨M.1 * M'.1, hMM⟩ := by
  apply Subtype.ext
  apply Units.ext
  show smat (Formalism.REAL.Jm ε) wf M.1 * smat (Formalism.REAL.Jm ε) wf M'.1 = smat (Formalism.REAL.Jm ε) wf (M.1 * M'.1)
  exact smat_mul ε wf hon M.1 M'.1

theorem unit_mul {G G' : Matrix (Fin k) (Fin k) ℂ} (h : Gᴴ * G = 1) (h' : G'ᴴ * G' = 1) :
    (G * G')ᴴ * (G * G') = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Gᴴ, h, Matrix.one_mul, h']

theorem unit_inv {G : Matrix (Fin k) (Fin k) ℂ} (h : Gᴴ * G = 1) : Gᴴᴴ * Gᴴ = 1 := by
  rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.1 h

theorem sU_inv (M : {G : Matrix (Fin k) (Fin k) ℂ // Gᴴ * G = 1}) :
    (sU ε wf hon M)⁻¹ = sU ε wf hon ⟨M.1ᴴ, unit_inv M.2⟩ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  apply Subtype.ext
  apply Units.ext
  show smat (Formalism.REAL.Jm ε) wf M.1ᴴ * smat (Formalism.REAL.Jm ε) wf M.1 = 1
  rw [smat_mul ε wf hon, M.2, smat_one]

theorem isCompact_U : IsCompact {G : Matrix (Fin k) (Fin k) ℂ | Gᴴ * G = 1} := by
  have hcl : IsClosed {G : Matrix (Fin k) (Fin k) ℂ | Gᴴ * G = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  refine (isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
    hcl ?_
  intro (G : Matrix (Fin k) (Fin k) ℂ) hG
  have hG' : Gᴴ * G = 1 := hG
  refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
  show dist (G i j) 0 ≤ 1
  rw [dist_zero_right]
  have h1 := congrFun (congrFun hG' j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp only [Matrix.conjTranspose_apply] at h1
  have h2 : ∀ l, star (G l j) * G l j = ((Complex.normSq (G l j) : ℝ) : ℂ) := fun l => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [h2] at h1
  have h3 : ∑ l, Complex.normSq (G l j) = 1 := by exact_mod_cast h1
  have h4 : Complex.normSq (G i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun l => Complex.normSq (G l j)) (fun l _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at h4
  nlinarith [norm_nonneg (G i j)]

end Smat

section Cpt

variable {n k : ℕ} {ι : Type} [Fintype ι] (ε : ι → Fin n → Bool) (wt : ι → Fin k → Fin n → ℂ)
  (hon : ∀ v a b, hJ (ε v) (wt v a) (wt v b) = if a = b then 1 else 0)

abbrev UPi (ι : Type) (k : ℕ) : Type := {M : ι → Matrix (Fin k) (Fin k) ℂ // ∀ v, (M v)ᴴ * M v = 1}

def Phi (M : UPi ι k) : ∀ v, Formalism.REAL.UJ (ε v) := fun v => sU (ε v) (wt v) (hon v) ⟨M.1 v, M.2 v⟩

theorem compactSpace_UPi : CompactSpace (UPi ι k) := by
  have h : IsCompact {M : ι → Matrix (Fin k) (Fin k) ℂ | ∀ v, (M v)ᴴ * M v = 1} := by
    have e : {M : ι → Matrix (Fin k) (Fin k) ℂ | ∀ v, (M v)ᴴ * M v = 1} =
        Set.univ.pi fun _ => {G : Matrix (Fin k) (Fin k) ℂ | Gᴴ * G = 1} := by
      ext M; simp
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_U
  exact isCompact_iff_compactSpace.1 h

theorem continuous_smat_of {α : Type} [TopologicalSpace α] (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
    {f : α → Matrix (Fin k) (Fin k) ℂ} (hf : Continuous f) : Continuous fun a => smat J wf (f a) := by
  unfold smat
  exact continuous_const.add
    ((((continuous_const.matrix_mul (hf.sub continuous_const)).matrix_mul continuous_const)).matrix_mul
      continuous_const)

theorem continuous_Phi : Continuous (Phi ε wt hon) := by
  refine continuous_pi fun v => ?_
  have hG : Continuous fun M : UPi ι k => M.1 v := (continuous_apply v).comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_smat_of _ _ hG
  · exact (continuous_const.matrix_mul (continuous_smat_of _ _ hG).matrix_conjTranspose).matrix_mul continuous_const

theorem Phi_mul (M M' : UPi ι k) :
    Phi ε wt hon M * Phi ε wt hon M' =
      Phi ε wt hon ⟨fun v => M.1 v * M'.1 v, fun v => unit_mul (M.2 v) (M'.2 v)⟩ := by
  funext v
  exact sU_mul (ε v) (wt v) (hon v) ⟨M.1 v, M.2 v⟩ ⟨M'.1 v, M'.2 v⟩ _

theorem Phi_inv (M : UPi ι k) :
    (Phi ε wt hon M)⁻¹ = Phi ε wt hon ⟨fun v => (M.1 v)ᴴ, fun v => unit_inv (M.2 v)⟩ := by
  funext v
  exact sU_inv (ε v) (wt v) (hon v) ⟨M.1 v, M.2 v⟩

theorem Phi_one : Phi ε wt hon ⟨fun _ => 1, fun _ => by simp⟩ = 1 := by
  funext v
  apply Subtype.ext
  apply Units.ext
  show smat (Formalism.REAL.Jm (ε v)) (wt v) 1 = 1
  exact smat_one _ _

theorem Phi_zpow_mem (M : UPi ι k) (m : ℤ) : (Phi ε wt hon M) ^ m ∈ Set.range (Phi ε wt hon) := by
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, ← Phi_one ε wt hon]; exact ⟨_, rfl⟩
  | succ m ih =>
    obtain ⟨N, hN⟩ := ih
    rw [_root_.zpow_add_one, ← hN, Phi_mul]; exact ⟨_, rfl⟩
  | pred m ih =>
    obtain ⟨N, hN⟩ := ih
    rw [_root_.zpow_sub_one, ← hN, Phi_inv, Phi_mul]; exact ⟨_, rfl⟩

theorem isCompact_range_Phi : IsCompact (Set.range (Phi ε wt hon)) := by
  have := compactSpace_UPi (ι := ι) (k := k)
  exact isCompact_range (continuous_Phi ε wt hon)

end Cpt

section Main

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
  (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (v : InfinitePlace X.B.I.F)

theorem X_span : (lf D (X.Fu u)).fl.X = Submodule.span D.host.E (Set.range X.eX) := by
  show (X.Fu u).X = _
  rw [FlagG.X, X.Fu_e u]

theorem hT_e_X (a : Fin D.R.rS) : ∀ p ∈ (lf D (X.Fu u)).fl.X, (VS D).hT (X.eX a) p = 0 := by
  intro p hp
  rw [X_span] at hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact X.ee a b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem hJ_E_Xs (a : Fin D.R.rS) : ∀ s ∈ spanAt X v (lf D (X.Fu u)).fl.X,
    hJ (X.B.I.ε v) (rvc X v (X.eX a)) s = 0 := by
  refine spanAt_orth' X v _ _ fun p hp => hJ_rvc_zero X v ?_
  rw [← (VS D).herm.eq, hT_e_X X a p hp, map_zero]

theorem hJ_Xs_w {w : Fin X.B.I.n → ℂ} (hw : ∀ a, hJ (X.B.I.ε v) (rvc X v (X.eX a)) w = 0) :
    ∀ s ∈ spanAt X v (lf D (X.Fu u)).fl.X, hJ (X.B.I.ε v) s w = 0 := by
  refine spanAt_orth X v _ w fun p hp => ?_
  rw [X_span] at hp
  refine orth_span X v w ?_ p hp
  rintro _ ⟨a, rfl⟩
  exact hw a

theorem Xs_iso : ∀ s ∈ spanAt X v (lf D (X.Fu u)).fl.X, ∀ s' ∈ spanAt X v (lf D (X.Fu u)).fl.X,
    hJ (X.B.I.ε v) s s' = 0 := fun s hs s' hs' =>
  hJ_Xs_w X v (fun a => hJ_E_Xs X v a s' hs') s hs

theorem E_mem_Xs (a : Fin D.R.rS) : rvc X v (X.eX a) ∈ spanAt X v (lf D (X.Fu u)).fl.X := by
  refine rvc_mem X v ?_
  rw [X_span]; exact Submodule.subset_span ⟨a, rfl⟩

theorem Xs_le_E : spanAt X v (lf D (X.Fu u)).fl.X ≤
    Submodule.span ℂ (Set.range fun a => rv X.B.I v (X.eR a)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨p, hp, rfl⟩
  rw [X_span] at hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact Submodule.subset_span ⟨b, rfl⟩
  | zero =>
    show rvc X v 0 ∈ Submodule.span ℂ (Set.range fun a => rv X.B.I v (X.eR a))
    rw [rvc_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    show rvc X v (x + y) ∈ Submodule.span ℂ (Set.range fun a => rv X.B.I v (X.eR a))
    rw [rvc_add]; exact add_mem hx hy
  | smul c x _ hx =>
    show rvc X v (c • x) ∈ Submodule.span ℂ (Set.range fun a => rv X.B.I v (X.eR a))
    rw [rvc_smul]; exact Submodule.smul_mem _ _ hx

theorem hJ_F_E (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rvc X v (X.fY a)) (rvc X v (X.eX b)) = if b = a then 1 else 0 := by
  split_ifs with h
  · exact hJ_rvc_one X v (by rw [Formalism.L2.SG.Pf.hT_f_e, if_pos h])
  · exact hJ_rvc_zero X v (by rw [Formalism.L2.SG.Pf.hT_f_e, if_neg h])

theorem hJ_F_Z (a : Fin D.R.rS) : hJ (X.B.I.ε v) (rvc X v (X.fY a)) (rvc X v (X.zu u)) = 0 :=
  hJ_rvc_zero X v (X.zu_orth u a).2

theorem hJ_E_Z (a : Fin D.R.rS) : hJ (X.B.I.ε v) (rvc X v (X.eX a)) (rvc X v (X.zu u)) = 0 :=
  hJ_rvc_zero X v (X.zu_orth u a).1

theorem hJ_Z_Z : hJ (X.B.I.ε v) (rvc X v (X.zu u)) (rvc X v (X.zu u)) ≠ 0 := by
  rw [hJ_rvc, X.zu_norm]
  intro h0
  rw [map_eq_zero_iff _ (X.B.I.φ v).injective, map_eq_zero_iff _ X.ιE.symm.injective, neg_eq_zero,
    Nat.cast_eq_zero] at h0
  exact (D.mem u).A.T_prime.ne_zero h0

theorem hJ_Z_Xs : ∀ s ∈ spanAt X v (lf D (X.Fu u)).fl.X, hJ (X.B.I.ε v) (rvc X v (X.zu u)) s = 0 := by
  intro s hs
  rw [hJ_symm, hJ_Xs_w X v (fun a => hJ_E_Z X v a) s hs, star_zero]

end Main

section Place

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
  (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (v : InfinitePlace X.B.I.F)

theorem wfr_perp_Xplus (b : Fin D.R.k) : ∀ p ∈ (lf D (X.Fu u)).fl.Xplus,
    hJ (X.B.I.ε v) (rvc X v p) (X.wfr u v b) = 0 := by
  intro p hp
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

theorem isotropicSpan_le_jointSpan_left : (lf D (X.Fu u)).fl.X ≤ fixedSubspaceOfRepresentative X q :=
  le_trans (by unfold FlagG.Xplus; exact le_sup_left) le_sup_left

theorem span_le_span_fixedSubspace : spanAt X v (lf D (X.Fu u)).fl.X ≤ spanAt X v (fixedSubspaceOfRepresentative X q) := Geo.spanAt_mono X v (isotropicSpan_le_jointSpan_left X q)

theorem exists_wt (hN1 : ∀ y : Fin X.B.I.n → ℂ,
      (∀ p ∈ (lf D (X.Fu u)).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (lf D (X.Fu u)).fl.X, ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) :
    ∃ wt : Fin D.R.k → Fin X.B.I.n → ℂ, (∀ b, X.wfr u v b - wt b ∈ spanAt X v (lf D (X.Fu u)).fl.X) ∧
      (∀ b, ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) (wt b) = 0) ∧
      (∀ a b, hJ (X.B.I.ε v) (wt a) (wt b) = if a = b then 1 else 0) := by
  choose x hx hxo using fun b => hN1 (X.wfr u v b) (wfr_perp_Xplus X v b)
  refine ⟨fun b => X.wfr u v b - x b, fun b => by simpa using hx b, fun b p hp => hxo b p hp, fun a b => ?_⟩
  have hwV : ∀ c, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) y (X.wfr u v c - x c) = 0 :=
    fun c => spanAt_orth X v _ _ (fun p hp => hxo c p hp)
  have hwX : ∀ c, ∀ y ∈ spanAt X v (lf D (X.Fu u)).fl.X, hJ (X.B.I.ε v) (X.wfr u v c) y = 0 :=
    fun c => spanAt_orth' X v _ _ (fun p hp => wfr_perp_Xplus X v c p (by unfold FlagG.Xplus; exact Submodule.mem_sup_left hp))
  rw [hJ_sub_left, hwV b (x a) (span_le_span_fixedSubspace X q v (hx a)), sub_zero, hJ_sub_right, hwX a (x b) (hx b), sub_zero]
  exact X.wfr_on u v a b

variable {X q v}

theorem dec {wt : Fin D.R.k → Fin X.B.I.n → ℂ} (hwt : ∀ b, X.wfr u v b - wt b ∈ spanAt X v (lf D (X.Fu u)).fl.X)
    (w : Fin X.B.I.n → ℂ) (hw : ∀ a, hJ (X.B.I.ε v) (rvc X v (X.eX a)) w = 0) :
    ∃ s ∈ spanAt X v (lf D (X.Fu u)).fl.X, ∃ (c : ℂ) (d : Fin D.R.k → ℂ),
      w = s + c • rvc X v (X.zu u) + ∑ b, d b • wt b := by
  set α : Fin D.R.rS → ℂ := fun a => hJ (X.B.I.ε v) (rvc X v (X.fY a)) w with hα
  set w1 := w - ∑ a, α a • rvc X v (X.eX a) with hw1
  set c := hJ (X.B.I.ε v) (rvc X v (X.zu u)) w1 * (hJ (X.B.I.ε v) (rvc X v (X.zu u)) (rvc X v (X.zu u)))⁻¹ with hc
  set w2 := w1 - c • rvc X v (X.zu u) with hw2
  have hE2 : ∀ a, hJ (X.B.I.ε v) (rvc X v (X.eX a)) w2 = 0 := fun a => by
    rw [hw2, hw1, hJ_sub_right, hJ_sub_right, hJ_sum_right, hw a, hJ_smul_right, hJ_E_Z]
    simp only [hJ_smul_right, hJ_rvc_zero X v (X.ee _ _), mul_zero, Finset.sum_const_zero]
    ring
  have hF2 : ∀ a, hJ (X.B.I.ε v) (rvc X v (X.fY a)) w2 = 0 := fun a => by
    rw [hw2, hw1, hJ_sub_right, hJ_sub_right, hJ_sum_right, hJ_smul_right, hJ_F_Z]
    simp only [hJ_smul_right, hJ_F_E, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hα]
    ring
  have hZ2 : hJ (X.B.I.ε v) (rvc X v (X.zu u)) w2 = 0 := by
    rw [hw2, hJ_sub_right, hJ_smul_right, hc, mul_assoc, inv_mul_cancel₀ (hJ_Z_Z X v), mul_one, sub_self]
  have hspan := wfrSpan D X u v w2 (fun a => ⟨hE2 a, hF2 a⟩) hZ2
  set d : Fin D.R.k → ℂ := fun b => hJ (X.B.I.ε v) (X.wfr u v b) w2
  refine ⟨∑ a, α a • rvc X v (X.eX a) + ∑ b, d b • (X.wfr u v b - wt b), ?_, c, d, ?_⟩
  · exact add_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (E_mem_Xs X v a))
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hwt b))
  · have e1 : w = w2 + c • rvc X v (X.zu u) + ∑ a, α a • rvc X v (X.eX a) := by
      rw [hw2, hw1]; abel
    have e2 : ∑ b, d b • X.wfr u v b = ∑ b, d b • (X.wfr u v b - wt b) + ∑ b, d b • wt b := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← smul_add, sub_add_cancel]
    rw [e1]
    conv_lhs => rw [hspan]
    rw [e2]
    abel

theorem rad {wt : Fin D.R.k → Fin X.B.I.n → ℂ} (hwt : ∀ b, X.wfr u v b - wt b ∈ spanAt X v (lf D (X.Fu u)).fl.X)
    (hwo : ∀ b, ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) (wt b) = 0)
    (hon : ∀ a b, hJ (X.B.I.ε v) (wt a) (wt b) = if a = b then 1 else 0)
    (hN3 : ∀ y ∈ spanAt X v (lf D (X.Fu u)).fl.X, (∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        y ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl))
    (w : Fin X.B.I.n → ℂ) (hw : ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) w = 0) :
    w - ∑ b, hJ (X.B.I.ε v) (wt b) w • wt b ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl) := by
  obtain ⟨s, hs, c, d, hdec⟩ := dec hwt w (fun a => hw _ (Formalism.L2.SG.CovariantRepresentation.basis_mem_fixedSubspace q a))
  have hwtV : ∀ b, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) (wt b) y = 0 :=
    fun b => spanAt_orth' X v _ _ (hwo b)
  have hZV : rvc X v (X.zu u) ∈ spanAt X v (fixedSubspaceOfRepresentative X q) := rvc_mem X v (Formalism.L2.SG.CovariantRepresentation.zu_mem_fixedSubspaceOfRepresentative q)
  have hsV : s ∈ spanAt X v (fixedSubspaceOfRepresentative X q) := span_le_span_fixedSubspace X q v hs
  have hd : ∀ b, hJ (X.B.I.ε v) (wt b) w = d b := fun b => by
    rw [hdec, hJ_add_right, hJ_add_right, hwtV b s hsV, hJ_smul_right, hwtV b _ hZV, hJ_sum_right]
    simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hc : c = 0 := by
    have h0 := hw _ (Formalism.L2.SG.CovariantRepresentation.zu_mem_fixedSubspaceOfRepresentative q)
    rw [hdec, hJ_add_right, hJ_add_right, hJ_Z_Xs X v s hs, hJ_smul_right, hJ_sum_right] at h0
    have hz : ∀ b, hJ (X.B.I.ε v) (rvc X v (X.zu u)) (d b • wt b) = 0 := fun b => by
      rw [hJ_smul_right, hJ_symm, hwtV b _ hZV, star_zero, mul_zero]
    simp only [hz, Finset.sum_const_zero, add_zero, zero_add] at h0
    exact (mul_eq_zero.1 h0).resolve_right (hJ_Z_Z X v)
  have e : w - ∑ b, hJ (X.B.I.ε v) (wt b) w • wt b = s := by
    simp only [hd]
    rw [hdec, hc, zero_smul, add_zero]; abel
  rw [e]
  refine hN3 s hs fun p hp => ?_
  have h1 := hw p hp
  rw [hdec, hc, zero_smul, add_zero, hJ_add_right, hJ_sum_right] at h1
  have hz : ∀ b, hJ (X.B.I.ε v) (rvc X v p) (d b • wt b) = 0 := fun b => by
    rw [hJ_smul_right, hwo b p hp, mul_zero]
  simpa [hz] using h1

end Place

section Final

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
  (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ')

theorem Xp_span : (frq X q).fl.X = Submodule.span D.host.E (Set.range fun a => q.1.2 (X.eX a)) := by
  rw [Formalism.L2.SG.CovariantRepresentation.frq_fl]
  show Submodule.span _ (Set.range fun a => q.1.2 ((X.Fu u').e a)) = _
  rw [X.Fu_e u']

theorem hJ_sum_sum {n k : ℕ} (ε : Fin n → Bool) (wf : Fin k → Fin n → ℂ)
    (hon : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (α β : Fin k → ℂ) :
    hJ ε (∑ c, α c • wf c) (∑ d, β d • wf d) = ∑ c, star (α c) * β c := by
  rw [hJ_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hJ_smul_left, hJ_sum_right]
  simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem smat_wt {n k : ℕ} (ε : Fin n → Bool) (wf : Fin k → Fin n → ℂ)
    (hon : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0) (G : Matrix (Fin k) (Fin k) ℂ) (b : Fin k) :
    smat (Formalism.REAL.Jm ε) wf G *ᵥ wf b = ∑ c, G c b • wf c := by
  have hcoef : (fun d => hJ ε (wf d) (wf b)) = Pi.single b 1 := by
    funext d; rw [hon]; by_cases h : d = b
    · subst h; simp
    · simp [h]
  rw [smat_apply, hcoef, mulVec_single_one]
  show wf b + ∑ c, (G - 1) c b • wf c = ∑ c, G c b • wf c
  have e : ∑ c, (G - 1) c b • wf c = ∑ c, G c b • wf c - wf b := by
    simp only [Matrix.transpose_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [e]; abel

theorem fixedDecompositionZero_holds : FixedDecompositionZero := by
  intro D X Y u u' t hr hG h hh
  obtain ⟨hrel, hG0⟩ := relRepC D X Y u u' t hr hG
  have hN := fun v => cplxNF D X u u' t.lam t.lam' t.rep hrel hG0 v
  choose wt hwt hwo hon using fun v => exists_wt X t.rep v (hN v).1
  set q := t.rep with hq
  have hIX : ∀ v, spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl) ≤ spanAt X v (lf D (X.Fu u)).fl.X :=
    fun v => Geo.spanAt_mono X v inf_le_left
  have hIX' : ∀ v, spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl) ≤ spanAt X v (frq X q).fl.X :=
    fun v => Geo.spanAt_mono X v inf_le_right
  have hIV : ∀ v, spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl) ≤ spanAt X v (fixedSubspaceOfRepresentative X q) :=
    fun v => (hIX v).trans (span_le_span_fixedSubspace X q v)
  have hIiso : ∀ v, ∀ i ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl),
      ∀ i' ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl), hJ (X.B.I.ε v) i i' = 0 :=
    fun v i hi i' hi' => Xs_iso X v i (hIX v hi) i' (hIX v hi')
  have hwtV : ∀ v b, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) (wt v b) y = 0 :=
    fun v b => spanAt_orth' X v _ _ (hwo v b)
  have hVwt : ∀ v b, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), hJ (X.B.I.ε v) y (wt v b) = 0 :=
    fun v b => spanAt_orth X v _ _ (hwo v b)

  have hHp : ∀ v, ∀ p ∈ fixedSubspaceOfRepresentative X q, uMat (h v) *ᵥ rvc X v p = rvc X v p :=
    fun v p hp => Formalism.L2.SG.CovariantRepresentation.fix_rv hh hp v
  have hHu : ∀ v x y, hJ (X.B.I.ε v) (uMat (h v) *ᵥ x) (uMat (h v) *ᵥ y) = hJ (X.B.I.ε v) x y :=
    fun v => hJ_unitary _ (uMat_unit _)

  set G : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ :=
    fun v => Matrix.of fun a b => hJ (X.B.I.ε v) (wt v a) (uMat (h v) *ᵥ wt v b) with hGdef
  set r : ∀ v, Fin D.R.k → Fin X.B.I.n → ℂ :=
    fun v b => uMat (h v) *ᵥ wt v b - ∑ a, G v a b • wt v a with hrdef
  have hHwt : ∀ v b, uMat (h v) *ᵥ wt v b = ∑ a, G v a b • wt v a + r v b := fun v b => by
    have e : r v b = uMat (h v) *ᵥ wt v b - ∑ a, G v a b • wt v a := rfl
    rw [e, add_sub_cancel]
  have hrI : ∀ v b, r v b ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl) := fun v b =>
    rad (hwt v) (hwo v) (hon v) (hN v).2.2 _ (fun p hp => by rw [← hHp v p hp, hHu]; exact hwo v b p hp)
  have Gu : ∀ v, (G v)ᴴ * G v = 1 := by
    intro v
    ext a b
    have h1 := hHu v (wt v a) (wt v b)
    rw [hon, hHwt, hHwt, hJ_add_left, hJ_add_right, hJ_add_right, hJ_sum_sum _ _ (hon v),
      hIiso v _ (hrI v a) _ (hrI v b), hJ_sum_left, hJ_sum_right] at h1
    have hz1 : ∀ c, hJ (X.B.I.ε v) (G v c a • wt v c) (r v b) = 0 := fun c => by
      rw [hJ_smul_left, hwtV v c _ (hIV v (hrI v b)), mul_zero]
    have hz2 : ∀ d, hJ (X.B.I.ε v) (r v a) (G v d b • wt v d) = 0 := fun d => by
      rw [hJ_smul_right, hVwt v d _ (hIV v (hrI v a)), mul_zero]
    simp only [hz1, hz2, Finset.sum_const_zero, add_zero] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply]
    rw [← h1]

  set k : X.B.I.Ginf := Phi (fun v => X.B.I.ε v) wt hon ⟨G, Gu⟩ with hkdef
  have hkm : ∀ v, uMat (k v) = smat (Formalism.REAL.Jm (X.B.I.ε v)) (wt v) (G v) := fun v => rfl
  have hkfix : ∀ v y, (∀ c, hJ (X.B.I.ε v) (wt v c) y = 0) → uMat (k v) *ᵥ y = y := fun v y hy => by
    rw [hkm]; exact smat_fix _ _ (hon v) _ _ hy
  have hkwt : ∀ v b, uMat (k v) *ᵥ wt v b = ∑ c, G v c b • wt v c := fun v b => by
    rw [hkm]; exact smat_wt _ _ (hon v) _ b
  have hkFix : k ∈ pointwiseStabilizerInfinite X q := by
    rintro v _ ⟨p, hp, rfl⟩
    exact hkfix v _ (fun c => by rw [hJ_symm, hwo v c p hp, star_zero])

  set n : X.B.I.Ginf := k⁻¹ * h with hndef
  have hnm : ∀ v, uMat (n v) = uMat ((k v)⁻¹) * uMat (h v) := fun v => rfl
  have hkinv : ∀ v y z, uMat (k v) *ᵥ y = z → uMat ((k v)⁻¹) *ᵥ z = y := fun v y z e => by
    rw [← e, mulVec_mulVec, uMat_inv_mul'', one_mulVec]
  have hnp : ∀ v, ∀ p ∈ fixedSubspaceOfRepresentative X q, uMat (n v) *ᵥ rvc X v p = rvc X v p := fun v p hp => by
    rw [hnm, ← mulVec_mulVec, hHp v p hp]
    exact hkinv v _ _ (hkfix v _ (fun c => by rw [hJ_symm, hwo v c p hp, star_zero]))
  have hnV : ∀ v, ∀ y ∈ spanAt X v (fixedSubspaceOfRepresentative X q), uMat (n v) *ᵥ y = y := fun v y hy => by
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨p, hp, rfl⟩ := hx; exact hnp v p hp
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
    | smul c x _ hx => rw [mulVec_smul, hx]
  have hnwt : ∀ v b, uMat (n v) *ᵥ wt v b = wt v b + r v b := fun v b => by
    rw [hnm, ← mulVec_mulVec]
    refine hkinv v _ _ ?_
    rw [mulVec_add, hkwt, hkfix v _ (fun c => hwtV v c _ (hIV v (hrI v b))), hHwt]
  have hnu : ∀ v x y, hJ (X.B.I.ε v) (uMat (n v) *ᵥ x) (uMat (n v) *ᵥ y) = hJ (X.B.I.ε v) x y :=
    fun v => hJ_unitary _ (uMat_unit _)

  have hmain : ∀ v y, (∀ i ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl), hJ (X.B.I.ε v) i y = 0) →
      (uMat (n v) - 1) *ᵥ y ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl) := by
    intro v y hy
    have hperp : ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rvc X v p) ((uMat (n v) - 1) *ᵥ y) = 0 := fun p hp => by
      rw [sub_mulVec, one_mulVec, hJ_sub_right, ← hnu v (rvc X v p) y, hnp v p hp, sub_self]
    have hc : ∀ b, hJ (X.B.I.ε v) (wt v b) ((uMat (n v) - 1) *ᵥ y) = 0 := fun b => by
      have e : uMat (n v) *ᵥ (wt v b - r v b) = wt v b := by
        rw [mulVec_sub, hnwt, hnV v _ (hIV v (hrI v b)), add_sub_cancel_right]
      calc hJ (X.B.I.ε v) (wt v b) ((uMat (n v) - 1) *ᵥ y)
          = hJ (X.B.I.ε v) (wt v b) (uMat (n v) *ᵥ y) - hJ (X.B.I.ε v) (wt v b) y := by
            rw [sub_mulVec, one_mulVec, hJ_sub_right]
        _ = hJ (X.B.I.ε v) (uMat (n v) *ᵥ (wt v b - r v b)) (uMat (n v) *ᵥ y) - hJ (X.B.I.ε v) (wt v b) y := by
            rw [e]
        _ = 0 := by rw [hnu, hJ_sub_left, hy _ (hrI v b), sub_zero, sub_self]
    have := rad (hwt v) (hwo v) (hon v) (hN v).2.2 _ hperp
    simpa [hc] using this

  have hnU : n ∈ X.NinfU u := by
    intro v
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · show (uMat (n v) - 1) *ᵥ rvc X v (X.eX a) ∈ _
      rw [sub_mulVec, one_mulVec, hnp v _ (Formalism.L2.SG.CovariantRepresentation.basis_mem_fixedSubspace q a), sub_self]; exact zero_mem _
    · show (uMat (n v) - 1) *ᵥ rvc X v (X.zu u) ∈ _
      rw [sub_mulVec, one_mulVec, hnp v _ (Formalism.L2.SG.CovariantRepresentation.zu_mem_fixedSubspaceOfRepresentative q), sub_self]; exact zero_mem _
    · have h1 := hmain v y (fun i hi => hJ_Xs_w X v hy i (hIX v hi))
      show _ ∈ spanLt _ _
      unfold spanLt
      rw [Formalism.L2.SG.Pf.Level.image_lt_r]
      exact Xs_le_E X v (hIX v h1)
  have hnU' : q.1.1.1⁻¹ * n * q.1.1.1 ∈ X.NinfU u' := by
    intro v
    have hγ : ∀ p, uMat (q.1.1.1 v) *ᵥ rvc X v p = rvc X v (q.1.2 p) :=
      fun p => Formalism.L2.SG.CovariantRepresentation.rv_ratLink q.2.1 v p
    have hγi : uMat ((q.1.1.1 v)⁻¹) * uMat (q.1.1.1 v) = 1 := uMat_inv_mul'' _
    have hγu : ∀ x y, hJ (X.B.I.ε v) (uMat (q.1.1.1 v) *ᵥ x) (uMat (q.1.1.1 v) *ᵥ y) = hJ (X.B.I.ε v) x y :=
      hJ_unitary _ (uMat_unit _)
    have hm : uMat ((q.1.1.1⁻¹ * n * q.1.1.1) v) = uMat ((q.1.1.1 v)⁻¹) * uMat (n v) * uMat (q.1.1.1 v) := rfl
    have hconj : ∀ y, (uMat ((q.1.1.1⁻¹ * n * q.1.1.1) v) - 1) *ᵥ y =
        uMat ((q.1.1.1 v)⁻¹) *ᵥ ((uMat (n v) - 1) *ᵥ (uMat (q.1.1.1 v) *ᵥ y)) := fun y => by
      have hmat : uMat ((q.1.1.1 v)⁻¹) * uMat (n v) * uMat (q.1.1.1 v) - 1 =
          uMat ((q.1.1.1 v)⁻¹) * ((uMat (n v) - 1) * uMat (q.1.1.1 v)) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hγi, Matrix.mul_assoc]
      rw [hm, hmat, ← mulVec_mulVec, ← mulVec_mulVec]
    have hback : ∀ p, uMat ((q.1.1.1 v)⁻¹) *ᵥ rvc X v (q.1.2 p) = rvc X v p := fun p => by
      rw [← hγ, mulVec_mulVec, hγi, one_mulVec]
    have hXp : ∀ s ∈ spanAt X v (frq X q).fl.X,
        uMat ((q.1.1.1 v)⁻¹) *ᵥ s ∈ Submodule.span ℂ (Set.range fun a => rv X.B.I v (X.eR a)) := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, hp, rfl⟩ := hx
        rw [Xp_span] at hp
        induction hp using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          show uMat ((q.1.1.1 v)⁻¹) *ᵥ rvc X v (q.1.2 (X.eX a)) ∈ _
          rw [hback]; exact Submodule.subset_span ⟨a, rfl⟩
        | zero =>
          show uMat ((q.1.1.1 v)⁻¹) *ᵥ rvc X v 0 ∈ _
          rw [rvc_zero, mulVec_zero]; exact zero_mem _
        | add x y _ _ hx hy =>
          show uMat ((q.1.1.1 v)⁻¹) *ᵥ rvc X v (x + y) ∈ _
          rw [rvc_add, mulVec_add]; exact add_mem hx hy
        | smul c x _ hx =>
          show uMat ((q.1.1.1 v)⁻¹) *ᵥ rvc X v (c • x) ∈ _
          rw [rvc_smul, mulVec_smul]; exact Submodule.smul_mem _ _ hx
      | zero => rw [mulVec_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
      | smul c x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · show (uMat ((q.1.1.1⁻¹ * n * q.1.1.1) v) - 1) *ᵥ rvc X v (X.eX a) ∈ _
      rw [hconj, hγ, sub_mulVec, one_mulVec, hnp v _ (Formalism.L2.SG.CovariantRepresentation.ge_mem_fixedSubspace q a), sub_self, mulVec_zero]
      exact zero_mem _
    · show (uMat ((q.1.1.1⁻¹ * n * q.1.1.1) v) - 1) *ᵥ rvc X v (X.zu u') ∈ _
      rw [hconj, hγ, sub_mulVec, one_mulVec, hnp v _ (Formalism.L2.SG.CovariantRepresentation.gz_mem_fixedSubspace q), sub_self, mulVec_zero]
      exact zero_mem _
    · have hy2 : ∀ i ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl),
          hJ (X.B.I.ε v) i (uMat (q.1.1.1 v) *ᵥ y) = 0 := by
        intro i hi
        refine spanAt_orth X v _ _ (fun p hp => ?_) i (hIX' v hi)
        rw [Xp_span] at hp
        refine orth_span X v _ ?_ p hp
        rintro _ ⟨a, rfl⟩
        rw [← hγ, hγu]
        exact hy a
      have h1 := hmain v _ hy2
      show _ ∈ spanLt _ _
      unfold spanLt
      rw [Formalism.L2.SG.Pf.Level.image_lt_r, hconj]
      exact hXp _ (hIX' v h1)
  refine ⟨k, n, by rw [hndef, mul_inv_cancel_left], ⟨hnU, hnU'⟩,
    Formalism.L2.SG.CovariantRepresentation.fixNormC D X Y u u' t k hkFix, Set.range (Phi (fun v => X.B.I.ε v) wt hon),
    isCompact_range_Phi _ _ _, fun m => Phi_zpow_mem _ _ _ ⟨G, Gu⟩ m⟩

end Final

section Cov

open scoped ComplexConjugate
open Formalism.L2.SG.CovariantRepresentation Formalism.L2.SG.HaarPushforward Formalism.L2.SG.HaarRelevantTerms

def RHaarRel0 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), t.relevant → t.G = 0 →
    (∀ r ∈ Rset t, X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) = 1) →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ ν : Measure X.B.I.Ginf, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (Rset t)ᶜ = 0 ∧
      (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) ∧ (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) ∧
      ν.map (fun x => x⁻¹) = ν ∧ ν.map (fun x => h⁻¹ * x * h) = ν

theorem rHaarRel0_holds (hN : NLamNinf) (hG : PsiInfChar) (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) :
    RHaarRel0 := by
  intro D X Y u u' t hr hGt _ h hh
  have hΓR : ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ Rsub hG t := by
    intro s hs
    have hs0 : s ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin := hs
    obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
    have hl : RatLink X (t.pt⁻¹ * z * t.pt) (t.lin⁻¹ * n * t.lin) :=
      ratLink_mul X (ratLink_mul X (ratLink_inv X t.rep.2.1) hz) t.rep.2.1
    have hs2 := hN D X u' t.lam' _ _ hl hn'
    rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
    exact ⟨hzs ▸ hN D X u t.lam z n hz hn, hs2⟩
  haveI := ROsub_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin
  haveI := h2 D X Y u u' t
  obtain ⟨K, hK, hKc⟩ := h3 D X Y u u' t
  obtain ⟨ν, hs, h0, hc, hKf, hl, hi⟩ :=
    pushHaar_inv (Rsub hG t) (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (h1 D X Y u u' t) hΓR
      ⟨K, hK, fun r hr => hKc r hr⟩
  obtain ⟨k, n, rfl, hn, hk, hC⟩ := fixedDecompositionZero_holds D X Y u u' t hr hGt h hh
  exact ⟨ν, hs, h0, hc, hKf, hl, hi,
    conj_of_decomp (Rsub hG t) (h1 D X Y u u' t) ν hs h0 hc hKf hl hi k n hk hn hC⟩

def CovariantRepresentationZero : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), t.relevant → t.G = 0 → ∀ (Ω : Set X.B.I.Ginf),
    IsSFund X.B.I (ROinf t) Ω →
    OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') t.pt.1 →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       (X.piU u h).comp (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') t.pt.1) =
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') t.pt.1).comp
          (X.piU u' (t.pt.1⁻¹ * h * t.pt.1)))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covariantRepZero_of_lemmaV (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) :
    CovariantRepresentationZero := by
  have hRH := rHaarRel0_holds hN hG h1 h2 h3
  have hS : ShiftCore := shiftCore
  have hFN : FixNormC := fixNormC
  intro D X Y u u' t hr hGt Ω hΩ hI h hh
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have := FiniteDimensional.complete ℂ (X.Vpi u')
  have := hU X.B.I
  have hfe : ∀ v a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix_rv hh (basis_mem_fixedSubspace t.rep a) v
  have hfz : ∀ v, uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
    fun v => fix_rv hh (zu_mem_fixedSubspaceOfRepresentative t.rep) v
  have hfe' : ∀ v a, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix'_rv hh (ge_mem_fixedSubspace t.rep a) v
  have hfz' : ∀ v, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u') :=
    fun v => fix'_rv hh (gz_mem_fixedSubspace t.rep) v
  have hS1 : h ∈ X.SinfU u := fun v => inS_of_fix _ _ _ (hfe v) (hfz v)
  have hS2 : t.pt.1⁻¹ * h * t.pt.1 ∈ X.SinfU u' := fun v => inS_of_fix _ _ _ (hfe' v) (hfz' v)
  have hp1 : X.psiInfU u h = 1 := (psiInfU_fix X u h hfe hfz).trans (psiInfU_one X u)
  have hp2 : X.psiInfU u' (t.pt.1⁻¹ * h * t.pt.1) = 1 :=
    (psiInfU_fix X u' _ hfe' hfz').trans (psiInfU_one X u')
  have hWh : ∀ x, X.Wu u (h * x) = X.piU u h (X.Wu u x) := fun x => by
    have e : X.Wu u (h * x) = X.psiInfU u h • X.piU u h (X.Wu u x) := (X.Wu_spec u).1 h hS1 x
    rw [e, hp1, one_smul]
  have hWh' : ∀ y, X.Wu u' ((t.pt.1⁻¹ * h * t.pt.1) * y) = X.piU u' (t.pt.1⁻¹ * h * t.pt.1) (X.Wu u' y) :=
    fun y => by
      have e : X.Wu u' ((t.pt.1⁻¹ * h * t.pt.1) * y) =
          X.psiInfU u' (t.pt.1⁻¹ * h * t.pt.1) • X.piU u' (t.pt.1⁻¹ * h * t.pt.1) (X.Wu u' y) :=
        (X.Wu_spec u').1 _ hS2 y
      rw [e, hp2, one_smul]
  have hΓR : ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ Rsub hG t := by
    intro s hs
    have hs0 : s ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin := hs
    obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
    have hl : RatLink X (t.pt⁻¹ * z * t.pt) (t.lin⁻¹ * n * t.lin) :=
      ratLink_mul X (ratLink_mul X (ratLink_inv X t.rep.2.1) hz) t.rep.2.1
    have hs2 := hN D X u' t.lam' _ _ hl hn'
    rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
    exact ⟨hzs ▸ hN D X u t.lam z n hz hn, hs2⟩
  by_cases hχ : ∃ r ∈ Rset t, X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) ≠ 1
  ·
    have hOO : OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') t.pt.1 = 0 := by
      have hψ1 : ∀ s, ‖X.psiInfU u' s‖ = 1 := psiInfU_norm X u'
      have hcc : ∀ b : ℂ, ‖b‖ = 1 → b * starRingEnd ℂ b = 1 := fun b hb => by
        rw [Complex.mul_conj', hb]; simp
      unfold OO
      refine hA X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) (Rsub hG t)
        (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) _
        (fun r => X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1))) _ Ω
        (h1 D X Y u u' t) hΓR (h2 D X Y u u' t) (h3 D X Y u u' t) ?_ ?_ ?_ hχ ?_ hΩ
      · exact ((psiInfU_cont X u).mul (continuous_star.comp ((psiInfU_cont X u').comp
          ((continuous_const.mul continuous_id).mul continuous_const)))).continuousOn
      · intro r hr r' hr'
        have e : t.pt.1⁻¹ * (r * r') * t.pt.1 = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * r' * t.pt.1) := by group
        rw [e, ((hG D X u).2.1 r hr.1 r' hr'.1).2, ((hG D X u').2.1 _ hr.2 _ hr'.2).2, map_mul]
        ring
      · intro s hs
        rw [hC D X Y u u' t.lam t.lam' t.mem t.mem' t.rep s hs]
        exact hcc _ (hψ1 _)
      · intro r hr x
        have e2 : t.pt.1⁻¹ * (r * x) = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * x) := by
          simp only [mul_assoc, mul_inv_cancel_left]
        rw [wu_N X u hr.1, e2, wu_N X u' hr.2, rankOneInnerOperator_smul_smul]
    rw [hOO, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  ·
    push Not at hχ
    let F : X.B.I.Ginf → (X.Vpi u' →L[ℂ] X.Vpi u) := fun x => rk1 (X.Wu u (h * x)) (X.Wu u' (t.pt.1⁻¹ * x))
    have hFinv : ∀ r ∈ Rsub hG t, ∀ x, F (r * x) = F x := by
      intro r hr x
      have e2 : t.pt.1⁻¹ * (r * x) = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * x) := by
        simp only [mul_assoc, mul_inv_cancel_left]
      show rk1 (X.Wu u (h * (r * x))) (X.Wu u' (t.pt.1⁻¹ * (r * x))) = rk1 (X.Wu u (h * x)) (X.Wu u' (t.pt.1⁻¹ * x))
      rw [hWh, wu_N X u hr.1, map_smul, ← hWh, e2, wu_N X u' hr.2, rankOneInnerOperator_smul_smul, hχ r hr, one_smul]
    have hFint : IntegrableOn F Ω (Formalism.L2.SG.ProjRows.muInf X.B.I) := by
      have := (ContinuousLinearMap.compL ℂ (X.Vpi u') (X.Vpi u) (X.Vpi u) (X.piU u h)).integrable_comp hI
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      show (X.piU u h).comp (rk1 _ _) = rk1 _ _
      rw [comp_rk1, hWh]
    obtain ⟨ν, hσ, hne, hcon, hfin, hleft, hinv, hconj⟩ := hRH D X Y u u' t hr hGt hχ h hh
    have := ROsub_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin
    have key := hS X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) (Rsub hG t)
      (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (X.Vpi u' →L[ℂ] X.Vpi u) F Ω h ν
      (h1 D X Y u u' t) hΓR (h3 D X Y u u' t) (hFN D X Y u u' t h hh) hσ hne hcon hfin hleft hinv hconj
      hFinv hΩ hFint
    rw [setIntegral_image_mul _ h⁻¹ Ω F] at key

    let A := piIsoT X u h hS1
    let B := piIsoT X u' _ hS2
    let L : (X.Vpi u' →L[ℂ] X.Vpi u) ≃L[ℂ] (X.Vpi u' →L[ℂ] X.Vpi u) :=
      ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℂ (X.Vpi u')) A.toContinuousLinearEquiv
    let L' : (X.Vpi u' →L[ℂ] X.Vpi u) ≃L[ℂ] (X.Vpi u' →L[ℂ] X.Vpi u) :=
      ContinuousLinearEquiv.arrowCongr B.symm.toContinuousLinearEquiv (ContinuousLinearEquiv.refl ℂ (X.Vpi u))
    have hL : ∀ T, L T = (X.piU u h).comp T := fun T => by ext ξ; rfl
    have hL' : ∀ T, L' T = T.comp (B.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u') := fun T => by ext ξ; rfl
    have hB : (B.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u') = X.piU u' (t.pt.1⁻¹ * h * t.pt.1) := by
      ext ξ; rfl
    unfold OO
    rw [← hL, ← hB, ← hL', ← L.integral_comp_comm, ← L'.integral_comp_comm]
    simp only [hL, hL', comp_rk1, rankOne_map_left_eq_comp, ← hWh]
    refine key.trans ?_
    congr 1
    funext x
    show rk1 (X.Wu u (h * (h⁻¹ * x))) (X.Wu u' (t.pt.1⁻¹ * (h⁻¹ * x))) = rk1 (X.Wu u x) (B.symm (X.Wu u' (t.pt.1⁻¹ * x)))
    rw [mul_inv_cancel_left]
    congr 1
    rw [LinearIsometryEquiv.eq_symm_apply]
    show X.piU u' (t.pt.1⁻¹ * h * t.pt.1) (X.Wu u' (t.pt.1⁻¹ * (h⁻¹ * x))) = X.Wu u' (t.pt.1⁻¹ * x)
    rw [← hWh']
    congr 1
    group

end Cov

section Asm

variable {D : D7} {X : HidaSetting D}

theorem OOt_eq_zero0 (hCov : CovariantRepresentationZero) (hSch : SchurNFC) (Y : Full X) {u u' : D.what₂.Word}
    (hw : ∀ τ, uS D u τ ≠ uS D u' τ)
    (hF : FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hr : t.relevant) (hG : t.G = 0) :
    OOt t = 0 := by
  obtain ⟨hrel, hG0⟩ := relRepC D X Y u u' t hr hG
  have hΩ := fundOf_spec hF t
  have hcov := hCov D X Y u u' t hr hG (FundOf t) hΩ (hI t)
  exact hSch D X u u' t.lam t.lam' t.rep hw hrel hG0 _ hcov

theorem kppOffC_of_steps0 (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC) (hV : LemmaVC)
    (hCov : CovariantRepresentationZero) (hSch : SchurNFC) : Formalism.L2.SG.RowsConc.KppOffC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hH hT huu => ?_⟩
  obtain ⟨hL, -, -, -, hWd, -⟩ := hT
  have hF := hFE D X Y u u'
  have hI := hOI D X Y u u' (hFold D X Y u hL hWd) (hFold D X Y u' hL hWd) hF
  have hw := words_differ hH huu
  intro t ht
  obtain ⟨hG, -⟩ := ht
  have hG' : t.G = 0 := by
    by_contra hne
    have h1 : (Y.tO u u').G t = 1 := by
      show Gt t = 1
      unfold Gt; rw [if_neg hne]
    rw [h1] at hG; exact one_ne_zero hG
  show op (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold op
  by_cases hr : t.relevant
  · rw [aTerm_eq_zero_of_OOt _ _ _ _ t (OOt_eq_zero0 hCov hSch Y hw hF hI t hr hG'), map_zero]
  · rw [hV D X Y u u' hF hI t hr, map_zero]

end Asm

end Formalism.L2.SG.FixedDecomposition
