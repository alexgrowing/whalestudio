import CompanionTheory.AutomorphicTheory.NumberFieldModels.StepCpt
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.ModelLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomEmpty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CellSmoothness

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.MainStatements.NFTie

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

noncomputable section

def LocLift : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (J J₀ : B.Mat k r → (Wq →L[ℂ] Wp)) (g₀ : B.Mat k r),
    J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs) → J₀ ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs) →
    g₀ ∈ JF.Om k r Bs.z Bs.z' → J₀ g₀ ≠ 0 →
    (∀ H : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs H → B.JF Bs H ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) →
    ∃ F₁ : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs F₁ ∧ ∃ U : Set (B.Mat k r), IsOpen U ∧ g₀ ∈ U ∧
      ∀ g ∈ U, g ∈ B.GV k r → B.JF Bs F₁ g = J g

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem evQ_trJB_FF (p : KB.Pl P Wp Wq) {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P p.T.base e)
    {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFKB p) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    MA.evQ P (trJB P p.T.base e J ρ) q = rawJ P p.T.base e J ρ q := by
  obtain ⟨h1, h2, -⟩ := gauge_transition_chain_holds Wp Wq P p.T.base p.hP p.hl.2.2 J hJ
  have h3 := raw_gauge_smoothness_holds Wp Wq P p.T.base p.hP p.hl.2.2 e he _ _ h1 ρ
  rw [← h2] at h3
  unfold trJB
  rw [toSm_of_mem P h3]
  rfl

theorem qdom (p : KB.Pl P Wp Wq) {x : MA.E P.r} :
    x ∈ MA.Qset P.r P.TT ↔ x ∈ JF.QDom P.k P.r p.T.base.z p.T.base.z' := by
  obtain ⟨_, _, _, h1, h2, _, _⟩ := p.hP
  simp only [MA.Qset, JF.QDom, Set.mem_setOf_eq, M.Par.TT, h1, h2]

theorem thrW_exists (k r m : ℕ) : ∃ A : ℝ, WeakThresholdClauses.WeakDominationThreshold k r A m := by
  refine ⟨6 * r * m + |(r : ℝ) * (4 * r + 2 * k - 1) * (6 * r + 1)| + 1, ?_⟩
  unfold WeakThresholdClauses.WeakDominationThreshold
  have h1 := le_abs_self ((r : ℝ) * (4 * r + 2 * k - 1) * (6 * r + 1))
  have h2 := abs_nonneg ((r : ℝ) * (4 * r + 2 * k - 1) * (6 * r + 1))
  constructor <;> linarith

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem tie_FF (hLL : LocLift) (p : KB.Pl P Wp Wq) {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P p.T.base e)
    (hG : GaugeQQ P p.T.base e) {Lm : R.LevelData (MA.A P (MA.DQ P)) P.r} (hM : MA.IsModelLevel P (MA.DQ P) Lm)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (a : Wd.Ix (Fin w.length))
    (hloc : Loc (gM P p.l0 Lm (D.positionted w) a)) {Dop : B.DiffOp P.k P.r Wp Wq}
    (hS : B.SmoothCoef (B.GPos p.T.base) Dop) (hC : B.Commutes p.T.base (B.GPos p.T.base) Dop)
    (hΘ : ∀ F, ∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w a F g = B.opApply Dop F g)
    {J H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFKB p)
    (hH : ∀ g ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', B.opApply Dop J g = B.JF p.T.base H g)
    (q : MA.Qp P.r P.TT) (h0 : B.JF p.T.base H (B.gq p.T.base q.1) ≠ 0) (ρ : M.Ty P) :
    rawJ P p.T.base e (B.JF p.T.base H) ρ q =
      MA.evQ P (MA.actA P (gM P p.l0 Lm (D.positionted w) a) (trJB P p.T.base e J) ρ) q := by
  have hom : ∀ q' : MA.Qp P.r P.TT, B.gq p.T.base q'.1 ∈ JF.Om P.k P.r p.T.base.z p.T.base.z' := fun q' =>
    BigCellHermitian.gqDom p.T.base ((qdom p).1 q'.2)
  have hJ0 := jdc_ffl p.T.base Dop hS hJ H hH
  obtain ⟨F₁, hF₁, U, hU, hgU, hag⟩ := hLL P.k P.r Wp Wq p.T.base J _ _ hJ hJ0 (hom q) h0
    fun H hH => jf_cpt_FF p.T.base hH
  obtain ⟨⟨Φ, hΦ⟩, ht⟩ := tie_cpt p he hG hM hw a hF₁
  obtain ⟨A, hA⟩ := thrW_exists P.k P.r (B.opOrder Dop)
  obtain ⟨ε, -, hn⟩ := TLB.nice_of_cpt hF₁
  have e1 : B.JF p.T.base (p.Θ.Θ w a F₁) (B.gq p.T.base q.1) = B.JF p.T.base H (B.gq p.T.base q.1) := by
    have hd : B.gq p.T.base q.1 ∈ C6.domL p.T.base ∅ := by
      rw [nfLeib_domL_eq]; exact jdc_om_sub_gpos _ (hom q)
    rw [PBN.jf_congr_pos p.T.base (hΘ F₁) hd, ← orbital_commutes_on_open_set _ _ _ _ p.T.base A (B.opOrder Dop) F₁ Dop _ subset_rfl
      le_rfl hA (hn.2.1 A _) (fun p' hp' f' hf' g hg => hC p' hp' f' hf' g (jdc_om_sub_gpos _ hg)) _ (hom q),
      JA.LocOp.opApply_congr_GV Dop hU (fun g hg hgU => hag g hgU hg) _ (hom q).1 hgU, hH _ (hom q)]
  have hcont : ContinuousOn (fun x => B.gq p.T.base x) (MA.Qset P.r P.TT) :=
    (CellSmoothness.contDiffOn_gq p.T.base).continuousOn.mono fun x hx => (qdom p).1 hx
  have hV := hcont.isOpen_inter_preimage (MA.Qset_open _ _) hU
  rw [← hloc.congr hV (f := trJB P p.T.base e (B.JF p.T.base F₁)) (fun ρ' q' hq' => ?_) ρ q ⟨q.2, hgU⟩, ← ht,
    evQ_trJB p.hP p.hl.2.2 he hΦ]
  · simp only [rawJ, e1]
  · rw [evQ_trJB_FF p he (jf_cpt_FF p.T.base hF₁), evQ_trJB_FF p he hJ]
    simp only [rawJ, hag _ hq'.2 (hom q').1]

theorem jf_Gpow (p : KB.Pl P Wp Wq) (s : ℕ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.JF p.T.base F ∈ FFKB p) :
    B.JF p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ s : ℝ) : ℂ) • F g) ∈ FFKB p := by
  obtain ⟨C₁, h⟩ := empty_operator_list_holds
  obtain ⟨Th₀, Th, -, hTh, hh⟩ := h Wp Wq P p s
  refine jdc_ffl p.T.base Th hTh.1 hF _ fun g _ => ?_
  have h := JCTx2.JF_cutF p.T.base (fun x => x ^ s) F 1 g
  unfold D.cutF at h
  simp only [div_one] at h
  rw [(hh (B.JF p.T.base F) g).2, h]

def PD {E : Type} [AddCommGroup E] [Module ℂ E] (o : ℕ) (f : ℕ → E) : Prop :=
  ∃ a : ℕ → E, ∀ s : ℕ, f s = ∑ n ∈ Finset.range (o + 1), (s : ℂ) ^ n • a n

theorem pd_list {E ι : Type} [AddCommGroup E] [Module ℂ E] {o : ℕ} (l : List ι) (f : ι → ℕ → E)
    (h : ∀ i ∈ l, PD o (f i)) : PD o fun s => (l.map fun i => f i s).sum := by
  induction l with
  | nil => exact ⟨fun _ => 0, fun s => by simp⟩
  | cons i l ih =>
    obtain ⟨a₁, h₁⟩ := h i (by simp)
    obtain ⟨a₂, h₂⟩ := ih (fun j hj => h j (by simp [hj]))
    refine ⟨fun n => a₁ n + a₂ n, fun s => ?_⟩
    simp only [List.map_cons, List.sum_cons, h₁ s, h₂ s, smul_add, Finset.sum_add_distrib]

theorem pd_mono {E : Type} [AddCommGroup E] [Module ℂ E] {o n : ℕ} (hn : n ≤ o) (x : E) :
    PD o fun s => (s : ℂ) ^ n • x := by
  refine ⟨fun m => if m = n then x else 0, fun s => ?_⟩
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' (Finset.range (o + 1)) n, if_pos (Finset.mem_range.2 (by omega))]

theorem scoef_zero (p : KB.Pl P Wp Wq) {w : List C.Letter} {a : Wd.Ix (Fin w.length)} {Q o : ℕ}
    {L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq} (hS : IsSCoef p w a Q L) {Dop : B.DiffOp P.k P.r Wp Wq}
    (ho : ∀ T ∈ Dop, T.word.length ≤ o)
    (hΘ : ∀ F, ∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w a F g = B.opApply Dop F g)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {g : B.Mat P.k P.r}
    (hg : g ∈ C6.domL p.T.base ∅) (qq : Fin (Q + 1)) (hq : o < qq) : B.opApply (L qq) F g = 0 := by
  have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g := hg.2.1
  have hpd : PD o fun s : ℕ => ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g := by
    have h1 : PD o fun s : ℕ => (Dop.map fun T => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-(s : ℝ)) : ℝ) : ℂ) •
        T.coef g (B.Rw T.word (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ (s : ℝ) : ℝ) : ℂ) • F g') g)).sum := by
      refine pd_list _ _ fun T hT => ?_
      obtain ⟨terms, ht, hexp⟩ := leibniz_expansion_holds P.k P.r Wp Wq p.T.base T.word T.word_lie
      have h2 := pd_list (o := o) terms (fun t (s : ℕ) => (s : ℂ) ^ t.1 • T.coef g ((t.2.1 g *
        ((Gf P.k P.r p.T.base.z p.T.base.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F g))
        fun t h => pd_mono (le_trans (ht t h).1 (ho T hT)) _
      convert h2 using 2 with s
      have h3 := hexp _ (nfLeib_thChain_rpow (s : ℝ)) F hF g hg
      simp only [pow_zero, one_mul] at h3
      rw [h3, map_list_sum, List.smul_sum, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp, map_smul, smul_smul]
      congr 1
      have h4 : ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-(s : ℝ)) : ℝ) : ℂ) *
          ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (s : ℝ) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add hG, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one]
      push_cast at h4 ⊢
      linear_combination ((s : ℂ) ^ t.1 * (t.2.1 g * ((Gf P.k P.r p.T.base.z p.T.base.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1)) * h4
    convert h1 using 2 with s
    have h5 := hS (s : ℝ) F hF g hg
    rw [hΘ _ g hg, B.opApply, List.smul_sum, List.map_map] at h5
    push_cast at h5 ⊢
    exact h5.symm
  obtain ⟨c, hc⟩ := hpd
  beta_reduce at hc
  have key := nf_coef_unique (Q + 1 + (o + 1))
    (fun i => (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) - (if i < o + 1 then c i else 0))
    (Set.range fun n : ℕ => (n : ℂ)) (Set.infinite_range_of_injective Nat.cast_injective) (by
      rintro _ ⟨s, rfl⟩
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [nf_sum_pad (by omega) _ fun q => B.opApply (L q) F g, hc s, sub_eq_zero,
        ← Finset.sum_subset (Finset.range_subset_range.2 (show o + 1 ≤ Q + 1 + (o + 1) by omega))]
      · exact Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)]
      · intro i _ hi
        rw [if_neg (by simpa using hi), smul_zero]) qq (by omega)
  simpa only [dif_pos qq.2, if_neg (show ¬ (qq : ℕ) < o + 1 by omega), sub_zero] using key

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
