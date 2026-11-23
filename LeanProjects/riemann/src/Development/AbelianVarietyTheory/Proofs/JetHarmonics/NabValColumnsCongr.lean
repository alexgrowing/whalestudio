import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonGaugeDmonOfHLIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGroupedOfSublist
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ColumnValue

theorem dmonOf_zero_index {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (g : PS k 1 d) : DmonOf F u 0 g = g := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, ih]; rfl

theorem dmonOf_smul {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (c : k) (g : PS k 1 d) :
    DmonOf F u mo (c • g) = C c * DmonOf F u mo g := by
  rw [smul_eq_C_mul]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, DerivEndo.iterate_dof_C_mul]

theorem column_value {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h)
    (w0 a : O) (N m : ℕ) (w : PS R 1 d)
    (hw : FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0))
    (I : Ideal R) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (α : ι → R) (hI : ∀ l, α l ∈ I)
    (hα : ∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) =
      algebraMap R k (α l) • (fun i => algebraMap R k (u l i)))
    (hβ : ∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
      ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range)
    (f : PS R 1 d) (y : ι → R) (hf : ∀ l mo, coeff mo (Dof B.G.F (u l) f - C (y l) * f) ∈ I)
    (mo : ι →₀ ℕ) :
    ∃ s : R, s - (∏ l, y l ^ mo l) * constantCoeff f ∈ I ∧
      B.nabVal k h w0 (N * m) (FB.toK k (f * w ^ m)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : FB.toK k (f * w ^ m) * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      FB.toK k f * FB.expS k ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0)) := by
    have e : FB.toK k (f * w ^ m) = FB.toK k f * FB.toK k w ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hw, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0))) = algebraMap R k r := by
    intro mo
    rcases eq_or_ne mo 0 with rfl | hmo
    · exact ⟨0, I.zero_mem, by rw [dmonOf_zero_index, nt_const_smul, cA, mul_zero, map_zero]⟩
    · obtain ⟨l, hl⟩ := Finsupp.ne_iff.1 hmo
      obtain ⟨t, ht⟩ := canonGauge_dmonOf_hL_integral R d O k B h hh w0 ι u hβ mo
      refine ⟨(m : R) * ((∏ l, α l ^ mo l) * t), I.mul_mem_left _ (I.mul_mem_right _
        (Ideal.prod_mem I (Finset.mem_univ l) (I.pow_mem_of_mem (hI l) _ (Nat.pos_of_ne_zero hl)))), ?_⟩
      rw [dmonOf_smul, map_mul, constantCoeff_C,
        (invariantDeriv_along_endo R d O k B a).2 ι _ (fun l => algebraMap R k (α l)) hα mo, ← ht]
      simp only [map_mul, map_prod, map_pow, map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cA, mul_zero]) hφ f mo
  refine ⟨constantCoeff (DmonOf B.G.F u mo f) + r, ?_, ?_⟩
  · rw [add_sub_right_comm]
    exact I.add_mem (constantCoeff_dmonOf_sub_mem R d B.G.F I ι u y f hf mo) hr
  · unfold FB.nabVal
    rw [hG, PullbackColumn.dpolyOf_monomial_one]
    exact e

end GlobalTheory.ColumnValue

namespace GlobalTheory

open ColumnValue

theorem nabVal_columns_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l ∈ I) → (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) → (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) → ∀ (n : ℕ) (f : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ l b mo, coeff mo (Dof B.G.F (u l) (f b) - C (y (l, b)) * f b) ∈ I) → ∀ P : MvPolynomial (ι × Fin n) R, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) * ∏ b, B.nabVal k h w0 (N * m) (FB.toK k (f b * w ^ m)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k (MvPolynomial.eval y P * ∏ b, constantCoeff (f b) + r) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw I ι _ u α hI hα hβ n f y hf P
  choose s hs he using fun (mo : ι × Fin n →₀ ℕ) (b : Fin n) =>
    column_value B h hh w0 a N m w hw I u α hI hα hβ (f b) (fun l => y (l, b)) (fun l => hf l b) (colM mo b)
  refine ⟨∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b -
    MvPolynomial.eval y P * ∏ b, constantCoeff (f b), ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo _ => ?_
    rw [mul_assoc, ← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b)
  · rw [add_sub_cancel]
    simp only [he]
    simp only [map_sum, map_mul, map_prod]

end GlobalTheory
