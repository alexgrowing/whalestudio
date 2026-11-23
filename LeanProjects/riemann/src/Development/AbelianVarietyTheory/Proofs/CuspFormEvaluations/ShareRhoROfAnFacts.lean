import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPairStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningFormsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IndepSpanRankTransferLargeFieldComplexStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem finite_sum_le (D a : ℕ) : {α : Fin D → ℕ | ∑ i, α i ≤ a}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin D => Set.finite_Iic a)).subset ?_
  intro α hα i
  exact (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hα

theorem graded_prod_pow_mul {A ι : Type} [CommRing A] (Q : ℕ → A → Prop) (s : ι → A)
    (h : ∀ n i x, Q n x → Q (n + 1) (s i * x)) (α : ι → ℕ) (F : Finset ι) (n : ℕ) (x : A) (hx : Q n x) :
    Q (n + ∑ i ∈ F, α i) ((∏ i ∈ F, s i ^ α i) * x) := by
  classical
  have hp : ∀ i m n x, Q n x → Q (n + m) (s i ^ m * x) := by
    intro i m
    induction m with
    | zero => intro n x hx; simpa using hx
    | succ m ih => intro n x hx; rw [pow_succ', mul_assoc, ← add_assoc]; exact h _ _ _ (ih n x hx)
  induction F using Finset.induction_on with
  | empty => simpa using hx
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mul_assoc, add_comm (α i), ← add_assoc]
    exact hp _ _ _ _ ih

theorem addL_zero' {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  unfold addL wadd wsmul
  simp

theorem shareRhoR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ∀ S : Scal B, ShareRhoR G S T (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hA hka hD hT hLat S la
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hDT : WeightFamilies.dimY D j < T := by nlinarith
  obtain ⟨b1, b2⟩ := GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair (WeightFamilies.dimY D j) T
  obtain ⟨θ, -, hθ⟩ := GlobalTheory.T.exists_valueBasis_in_spanning_forms D B P j X ka wL wF G.N G.w R t T Mg δ xs hA Set.univ Submodule.span_univ

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank ℂ (R.sp ka Set.univ) := by
    have h1 := (d8 ka ⊤).2
    rw [Submodule.top_coe] at h1
    rw [h1]
    unfold PJ.rk
    have : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ := Submodule.IsLattice.span_eq_top (self := hLat)
    rw [this]
  haveI hfin : FiniteDimensional ℂ (R.sp ka Set.univ) := by
    have h1 := (d8 ka ⊤).1
    rwa [Submodule.top_coe] at h1

  set a := a0 D j T with ha
  have haD : WeightFamilies.dimY D j + a = T := by rw [ha]; unfold a0; omega
  let p1 : Fin (WeightFamilies.dimY D j + 1) → MvPolynomial (Idx D j G.N) X.Forms := fun i =>
    ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (G.w k))
  let pm : (Fin (WeightFamilies.dimY D j) → ℕ) → MvPolynomial (Idx D j G.N) X.Forms := fun α => ∏ i, p1 i.succ ^ α i
  have pmK : ∀ α, toRp X la G.N (pm α) = secPow X la G.w α := by
    intro α
    simp only [pm, map_prod, map_pow, secPow]
    exact Finset.prod_congr rfl fun i _ => by rw [(d1 i.succ).1]
  have pmC : ∀ α, R.toFn t (pm α) = R.mon G.w t α := by
    intro α
    simp only [pm, map_prod, map_pow, Rdg.mon]
    exact Finset.prod_congr rfl fun i _ => by rw [(d1 i.succ).2.1]
  have hstep : ∀ n i x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + 1)) (p1 i * x) := by
    intro n i x hx
    rw [← wadd_addL]
    exact d4 _ _ _ _ (d1 i).2.2 hx
  have hpm : ∀ α n x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + ∑ i, α i)) (pm α * x) := fun α n x hx =>
    graded_prod_pow_mul (fun n x => OfWt X (addL wF wL n) x) (fun i : Fin (WeightFamilies.dimY D j) => p1 i.succ)
      (fun n i x hx => hstep n i.succ x hx) α Finset.univ n x hx
  have hp0 : ∀ m n x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + m)) (p1 0 ^ m * x) := fun m n x hx => by
    simpa using graded_prod_pow_mul (fun n x => OfWt X (addL wF wL n) x) (fun _ : Unit => p1 0)
      (fun n _ x hx => hstep n 0 x hx) (fun _ => m) Finset.univ n x hx
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j (X.wF0 wL wF))
  haveI : Finite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a} :=
    ((finite_sum_le (WeightFamilies.dimY D j) a).subset (t := {α | ∑ i, α i = a}) fun α (h : ∑ i, α i = a) => h.le).to_subtype
  haveI : Finite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} :=
    ((finite_sum_le (WeightFamilies.dimY D j) a).subset (t := {α | ∑ i, α i < a}) fun α (h : ∑ i, α i < a) => h.le).to_subtype
  letI := Fintype.ofFinite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a}
  letI := Fintype.ofFinite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a}
  let q : {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a} × Fin n → MvPolynomial (Idx D j G.N) X.Forms := fun p =>
    pm p.1.1 * MvPolynomial.C (X.inc (X.wF0 wL wF) (b p.2))
  have hq : ∀ p, OfWt X ka (q p) := by
    intro p
    have := hpm p.1.1 (WeightFamilies.dimY D j) _ (d3 (X.wF0 wL wF) (b p.2))
    rwa [p.1.2, haD, hka] at this
  have htr := (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la G.N t hgen ka _ q hq).2.2

  have hK : Submodule.span (Kp X la G.N) (zAll G la S T) ≤
      Submodule.span (Kp X la G.N) (Set.range fun p => toRp X la G.N (q p)) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, F, hα, -, rfl⟩
    have hF := emb_mem_Vw X la G.N _ F
    rw [Vw_eq_span_image X la G.N _ hb] at hF
    have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (Kp X la G.N) (secPow X la G.w α)) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(⟨α, hα⟩, k), ?_⟩
    simp only [q, map_mul, pmK, (d2 _).1, LinearMap.mulLeft_apply]

  have hC : Submodule.span ℂ (Set.range fun p => R.toFn t (q p)) ≤ R.deep G.w t (X.wF0 wL wF) a := by
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    refine ⟨p.1.1, R.ev (X.inc _ (b p.2)), p.1.2, Submodule.subset_span ⟨b p.2, trivial, rfl⟩, ?_⟩
    simp only [q, map_mul, pmC, (d2 _).2]
  have hCk : Submodule.span ℂ (Set.range fun p => R.toFn t (q p)) ≤ R.sp ka Set.univ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (d5 ka _ (hq p)).2
  obtain ⟨hli, hdis⟩ := hA.indep δ (fun i => R.ev (X.inc wF (θ i)))
    (fun i => Submodule.subset_span ⟨θ i, trivial, rfl⟩) hθ
  rw [← ha] at hli hdis
  have hLk : Submodule.span ℂ (Set.range (R.lead G.w t T a fun i => R.ev (X.inc wF (θ i)))) ≤ R.sp ka Set.univ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (θ p.2)) : MvPolynomial (Idx D j G.N) X.Forms) := by
      rw [addL_zero']; exact d3 _ _
    have h1 := hpm p.1.1 _ _ (hp0 (T - ∑ i, p.1.1 i) _ _ h0)
    have h2 := p.1.2
    rw [show 0 + (T - ∑ i, p.1.1 i) + ∑ i, p.1.1 i = T by omega, hka] at h1
    have h3 := (d5 ka _ h1).2
    rw [map_mul, map_mul, map_pow, pmC, (d1 0).2.1, (d2 _).2, ← mul_assoc] at h3
    exact h3
  have hrk := finrank_span_eq_card hli
  rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card] at hrk
  have hcard : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} = (T - 1).choose (WeightFamilies.dimY D j) :=
    b1 (by omega) hDT
  rw [hcard] at hrk
  haveI := Submodule.finiteDimensional_of_le hLk
  haveI := Submodule.finiteDimensional_of_le hCk
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℂ (Set.range (R.lead G.w t T a fun i => R.ev (X.inc wF (θ i)))))
    (Submodule.span ℂ (Set.range fun p => R.toFn t (q p)))
  rw [(hdis.mono_right hC).eq_bot, finrank_bot, add_zero, hrk] at hsum
  have hle := Submodule.finrank_mono (sup_le hLk hCk)
  haveI : FiniteDimensional (Kp X la G.N)
      (Submodule.span (Kp X la G.N) (Set.range fun p => toRp X la G.N (q p))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hKle := Submodule.finrank_mono hK
  rw [hd]
  refine (b2 δ _ _ hD hT hA.upper).1 ?_
  rw [mul_comm δ]
  omega

end GlobalTheory.Shares
