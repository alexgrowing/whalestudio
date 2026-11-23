import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Ord

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

theorem ord_prod_eq_zero (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i ∈ s, ord ϖ ζ (f i) = 0) : ord ϖ ζ (∏ i ∈ s, f i) = 0 := by
  refine Finset.prod_induction f (fun x => ord ϖ ζ x = 0) (fun a b ha hb => ?_) (ord_one ζ h) hf
  rw [ord_mul ζ h, ha, hb, add_zero]

theorem eq_zero_of_ord_top [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A} (hx : ∀ ζ : Pts O A, ord ϖ ζ x = ⊤) : x = 0 := by
  obtain ⟨n, hn⟩ := h.denom x
  have h0 : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) = 0 := by
    refine eq_zero_of_localization _ fun J hJ => ?_
    have h1 := hx ⟨J, hJ⟩
    rw [ord_eq _ h hn, ordAt, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · rw [ENat.map_eq_top_iff] at h1
      exact (vL_eq_top_iff (ζ := (⟨J, hJ⟩ : Pts O A)) _).1 h1
    · exact absurd h1 (WithTop.coe_ne_top)
  have h2 : ϖ ^ n • x = 0 := congrArg Subtype.val h0
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

end Ord

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem ord_uC_eq_zero {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (hC : Q.InCurve)
    (ζ : PtsG G la) (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ)
    (h0 : ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) = 0) :
    ord (unifO X la G.N) ζ (uC G la jj α) = 0 := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  unfold uC
  refine ord_prod_eq_zero ζ hU _ _ fun i _ => ?_
  rw [ord_pow ζ hU, h0, smul_zero]

theorem uBall_of_column (hCol : Column) : UBall := by
  unfold UBall
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  unfold LocalPointData.A0 at hb ⊢
  rw [mem_ballO_iff Q.c hU hC.2.2]
  intro ζ
  obtain ⟨jj, hjj⟩ := (hCol G la Q S CRm T c hOk hw ζ).2
  have h1 := (mem_ballO_iff Q.c hU hC.2.2 _).1 (hb jj) ζ
  rw [ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add] at h1
  exact h1

end PoleLengthBounds
