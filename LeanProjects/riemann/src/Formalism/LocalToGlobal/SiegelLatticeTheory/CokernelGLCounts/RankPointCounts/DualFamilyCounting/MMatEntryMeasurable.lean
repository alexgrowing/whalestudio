import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolNOfSteps

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped ENNReal
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem uMat_continuous (v : InfinitePlace X.B.I.F) :
    Continuous fun s : X.B.I.Ginf => uMat (s v) := by
  first
    | exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    | fun_prop
    | continuity

theorem hJ_continuous (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → ℂ) :
    Continuous fun s : X.B.I.Ginf => hJ (X.B.I.ε v) x (uMat (s v) *ᵥ y) := by
  simp only [hJ]
  first
    | exact continuous_const.matrix_dotProduct
        (continuous_const.matrix_mulVec ((uMat_continuous X v).matrix_mulVec continuous_const))
    | (have hu := uMat_continuous X v; fun_prop)

theorem xMat_entry_continuous (v : InfinitePlace X.B.I.F) (b a : Fin D.R.rS) :
    Continuous fun s => xMat X v s b a :=
  hJ_continuous X v (fV X v b) (eV X v a)

theorem aMat_entry_continuous (v : InfinitePlace X.B.I.F) (b a : Fin D.R.rS) :
    Continuous fun s => aMat X v s b a :=
  hJ_continuous X v (fV X v b) (fV X v a)

theorem xMat_continuous (v : InfinitePlace X.B.I.F) : Continuous fun s => xMat X v s := by
  first
    | exact continuous_pi fun b => continuous_pi fun a => xMat_entry_continuous X v b a
    | exact continuous_matrix fun b a => xMat_entry_continuous X v b a

theorem mMat_entry_measurable (v : InfinitePlace X.B.I.F) (b a : Fin D.R.rS) :
    Measurable fun s => mMat X v s b a := by
  have hx : Continuous fun s => xMat X v s := xMat_continuous X v
  have ha : Continuous fun s => aMat X v s := by
    first
      | exact continuous_pi fun b => continuous_pi fun a => aMat_entry_continuous X v b a
      | exact continuous_matrix fun b a => aMat_entry_continuous X v b a
  have hd : Measurable fun s => ((xMat X v s).det)⁻¹ := hx.matrix_det.measurable.inv
  simp only [mMat, Matrix.mul_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact (hd.mul (hx.matrix_adjugate.matrix_elem b c).measurable).mul (ha.matrix_elem c a).measurable

theorem reim_measurable {α : Type} [MeasurableSpace α] {f : α → ℂ} (hf : Measurable f) (t : Bool) :
    Measurable fun x => reim (f x) t := by
  cases t
  · first
      | exact Complex.measurable_re.comp hf
      | (simp only [reim, Bool.false_eq_true, if_false]; exact Complex.measurable_re.comp hf)
  · first
      | exact Complex.measurable_im.comp hf
      | (simp only [reim, if_true]; exact Complex.measurable_im.comp hf)

theorem kap_measurable : Measurable (kap X u) := by
  refine measurable_pi_lambda _ fun i => ?_
  obtain ⟨v, c⟩ := i
  rcases c with ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))
  · exact reim_measurable (xMat_entry_continuous X v p.1.1 p.1.2).measurable t
  · exact reim_measurable (hJ_continuous X v (fV X v b) (zV X u v)).measurable t
  · exact reim_measurable (hJ_continuous X v (fV X v b) (X.wfr u v j)).measurable t
  · exact reim_measurable (((mMat_entry_measurable X v p.1.1 p.1.2).sub
      (continuous_star.measurable.comp (mMat_entry_measurable X v p.1.2 p.1.1))).div_const 2) t
  · exact Complex.measurable_im.comp (mMat_entry_measurable X v a a)

private lemma isClosed_setOf_sub_one_mulVec_mem {n : ℕ} (w : Fin n → ℂ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ w ∈ S} := by
  have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g - 1) *ᵥ w := by
    first
      | exact (continuous_id.sub continuous_const).matrix_mulVec continuous_const
      | fun_prop
  exact S.closed_of_finiteDimensional.preimage hc

private lemma isClosed_setOf_InN {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have h : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a : Fin r, {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩
        {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
      ⋂ y : Fin n → ℂ, ⋂ (_ : ∀ a, hJ ε (e a) y = 0),
        {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [InN, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  exact ((isClosed_iInter fun a => isClosed_setOf_sub_one_mulVec_mem _ _).inter (isClosed_setOf_sub_one_mulVec_mem _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_setOf_sub_one_mulVec_mem _ _)

theorem ninfU_closed : IsClosed (X.NinfU u) := by
  have h : ∀ v : InfinitePlace X.B.I.F, IsClosed {s : X.B.I.Ginf | InN (X.B.I.ε v)
      (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (s v))} := fun v =>
    (isClosed_setOf_InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))).preimage
      (uMat_continuous X v)
  have h2 := isClosed_iInter h
  simp only [← Set.setOf_forall] at h2
  exact h2

theorem boxN_eq : boxN X u = X.NinfU u ∩ kap X u ⁻¹' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
  ext s
  simp only [boxN, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ico]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro h ⟨v, i⟩
    obtain ⟨hx, hy, hp, hm, hd⟩ := h v
    rcases i with ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))
    · cases t
      · exact (hx p.1.1 p.1.2 p.2).1
      · exact (hx p.1.1 p.1.2 p.2).2
    · cases t
      · exact (hy b).1
      · exact (hy b).2
    · cases t
      · exact (hp b j).1
      · exact (hp b j).2
    · cases t
      · exact (hm p.1.1 p.1.2 p.2).1
      · exact (hm p.1.1 p.1.2 p.2).2
    · exact hd a
  · intro h v
    exact ⟨fun b a hba => ⟨h (v, Sum.inl (Sum.inl (⟨(b, a), hba⟩, false))),
        h (v, Sum.inl (Sum.inl (⟨(b, a), hba⟩, true)))⟩,
      fun b => ⟨h (v, Sum.inl (Sum.inr (b, false))), h (v, Sum.inl (Sum.inr (b, true)))⟩,
      fun b j => ⟨h (v, Sum.inr (Sum.inl (b, j, false))), h (v, Sum.inr (Sum.inl (b, j, true)))⟩,
      fun b a hba => ⟨h (v, Sum.inr (Sum.inr (Sum.inl (⟨(b, a), hba⟩, false)))),
        h (v, Sum.inr (Sum.inr (Sum.inl (⟨(b, a), hba⟩, true))))⟩,
      fun a => h (v, Sum.inr (Sum.inr (Sum.inr a)))⟩

def KapInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), Set.InjOn (kap X u) (X.NinfU u)

theorem coordMeas_of (h : KapInj) : CoordMeas := by
  intro D X u
  exact ⟨kap_measurable X u, (ninfU_closed X u).measurableSet, h D X u⟩

def HaarUnique : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (μ ν : Measure X.B.I.Ginf),
    IsHaarOnSet X.B.I (X.NinfU u) μ → IsHaarOnSet X.B.I (X.NinfU u) ν → ∃ c : ℝ≥0∞, μ = c • ν

def LebHaar : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    ∃ lam : Measure X.B.I.Ginf, IsHaarOnSet X.B.I (X.NinfU u) lam ∧ lam.map (kap X u) = volume

private lemma measure_inter_eq_of_compl_null {α : Type*} [MeasurableSpace α] (μ : Measure α) {N : Set α}
    (hN : μ Nᶜ = 0) (P : Set α) : μ (P ∩ N) = μ P := by
  refine le_antisymm (measure_mono Set.inter_subset_left) ?_
  calc μ P ≤ μ ((P ∩ N) ∪ Nᶜ) := by
        refine measure_mono fun s hs => ?_
        by_cases h : s ∈ N
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr h
    _ ≤ μ (P ∩ N) + μ Nᶜ := measure_union_le _ _
    _ = μ (P ∩ N) := by rw [hN, add_zero]

theorem coordHaar_of (hU : HaarUnique) (hL : LebHaar) : CoordHaar := by
  intro D X u μ hμ
  obtain ⟨lam, hlam, hmap⟩ := hL D X u
  obtain ⟨c, rfl⟩ := hU D X u μ lam hμ hlam
  have hkm : Measurable (kap X u) := kap_measurable X u
  have hbm : MeasurableSet (Set.pi Set.univ
      (fun _ : InfinitePlace X.B.I.F × CIdx D.R.rS D.R.k => Set.Ico (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hvol : volume (Set.pi Set.univ
      (fun _ : InfinitePlace X.B.I.F × CIdx D.R.rS D.R.k => Set.Ico (0 : ℝ) 1)) = 1 := by
    first
      | (rw [volume_pi, Measure.pi_pi]; simp [Real.volume_Ico])
      | simp [Real.volume_pi_Ico]
  have hbox : lam (boxN X u) = 1 := by
    rw [boxN_eq, Set.inter_comm, measure_inter_eq_of_compl_null lam hlam.2.2.1,
      ← Measure.map_apply hkm hbm, hmap, hvol]
  rw [Measure.map_smul, hmap, Measure.smul_apply, hbox, smul_eq_mul, mul_one]

theorem covolN_of_four (hInj : KapInj) (hU : HaarUnique) (hL : LebHaar) (hC : CoordCovol) : CovolN := by
  intro D X u μ FdN hμ hF
  obtain ⟨hkm, -, hinj⟩ := coordMeas_of hInj D X u
  have hH := coordHaar_of hU hL D X u μ hμ
  obtain ⟨hAm, hAv⟩ := hC D X u FdN hF
  have hpre : kap X u ⁻¹' (kap X u '' (FdN ∩ X.NinfU u)) ∩ X.NinfU u = FdN ∩ X.NinfU u := by
    ext s
    constructor
    · rintro ⟨⟨t, ht, hts⟩, hs⟩
      rw [← hinj ht.2 hs hts]
      exact ht
    · intro hs
      exact Set.mem_inter (Set.mem_image_of_mem _ hs) hs.2
  have h2 := measure_inter_eq_of_compl_null μ hμ.2.2.1 (kap X u ⁻¹' (kap X u '' (FdN ∩ X.NinfU u)))
  rw [hpre] at h2
  have h3 : μ.map (kap X u) (kap X u '' (FdN ∩ X.NinfU u)) = μ (FdN ∩ X.NinfU u) := by
    rw [Measure.map_apply hkm hAm]
    exact h2.symm
  rw [hH, Measure.smul_apply, hAv, smul_eq_mul] at h3
  rw [← measure_inter_eq_of_compl_null μ hμ.2.2.1 FdN, ← h3]
  exact mul_comm _ _

end Formalism.L2.SG.Pf.LsNc5
