import Formalism.LocalToGlobal.ProjectiveLattices.NormalizedValuationMul
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def wRat (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.N) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w 1 (emb (xplus X E hM) la G.N (X.inc wL (G.w k))),
    Algebra.subset_adjoin (frac_mem_Hfr (xplus X E hM) la G.w (by
      rw [add_zero_weight_one_eq]; exact emb_mem_Vw (xplus X E hM) la G.N wL (G.w k)))⟩

def GenericSectionMinimumIntegral (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) →
    IsReduced (OsK (xplus X E hM) la G.w) → ∀ ζ : PtsG G la, (∀ k, 0 ≤ ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) ∧
    ∃ k, ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = 0

lemma nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ 0 ≤ nval T.V 1 z := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz, EReal.coe_nonneg, EReal.coe_nonneg]
    have : (0 : ℝ) < e := by exact_mod_cast he
    constructor
    · intro h; simpa using (div_nonneg_iff.1 h).elim (fun h' => h'.1) (fun h' => absurd h'.2 (not_le.2 this))
    · intro h; exact div_nonneg (by simpa using h) this.le

lemma nval_eq_zero_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : nval T.V e z = 0 ↔ nval T.V 1 z = 0 := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp [div_eq_zero_iff, this]

theorem depthAtSec_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (S : Scal B)
    (hspan : SpanW (xplus X E hM) G.w S) (h0 : GenericSectionMinimumIntegral G la)
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w)) (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ))
    (ζ : PtsG G la) :
    (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) := by
  set h := hs ζ with hh
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos

  have hwk : ∀ k, E.vAt' la (y ζ) (X.inc wL (G.w k)) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) +
        nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) := by
    intro k
    rw [h.hv, ← nval_mul]
    congr 1
    show _ = _ * h.lift (frac (xplus X E hM) la G.w 1 _)
    rw [h.lift_frac, pow_one, mul_comm, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hord : ∀ k, nval h.T.V 1 (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) =
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) :=
    fun k => (h.ord (wRat G la k)).symm
  obtain ⟨hint, k0, hk0⟩ := h0 hfd hred ζ
  have hnn : ∀ k, 0 ≤ nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw _ la G.w)) := by
    intro k
    rw [nval_nonneg_iff he, hord]
    have := hint k
    generalize ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = o at this ⊢
    cases o with
    | top => simp [toE]
    | coe n => simp only [toE]; exact_mod_cast (WithTop.coe_nonneg.1 this)
  have hz0 : nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k0 : Lw _ la G.w)) = 0 := by
    rw [nval_eq_zero_iff he, hord, hk0]
    show toE ((0 : ℤ) : WithTop ℤ) = 0
    simp [toE]
  apply le_antisymm
  · refine (iInf₂_le (G.w k0) (by rw [← hspan]; exact Submodule.subset_span ⟨k0, rfl⟩)).trans_eq ?_
    show E.vAt' la (y ζ) (X.inc wL (G.w k0)) = _
    rw [hwk, hz0, add_zero]
  · refine le_iInf₂ fun F hF => ?_
    rw [← hspan] at hF
    show _ ≤ E.vAt' la (y ζ) (X.inc wL F)
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hwk]
      exact le_add_of_nonneg_right (hnn k)
    | zero => rw [map_zero, E.vAt'_zero]; exact le_top
    | add x z _ _ hx hz =>
      rw [map_add]
      exact (le_min hx hz).trans (E.vAt'_add la _ _ _)
    | smul a x _ hx =>
      by_cases ha : ((a : 𝓞 B.KO) : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        rw [this, zero_smul, map_zero, E.vAt'_zero]; exact le_top
      · rw [← algebraMap_smul B.KO a x, map_smul, E.vAt'_smul la _ _ _ ha]
        exact le_add_of_nonneg_of_le (by exact_mod_cast vAdd_int_nonneg la ha) hx

end Formalism.L2.Pj
