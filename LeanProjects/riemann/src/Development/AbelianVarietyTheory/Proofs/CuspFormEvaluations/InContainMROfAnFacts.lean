import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpanStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IndepSpanRankTransferLargeFieldComplexStatement

noncomputable section

namespace GlobalTheory.Shares.Contain

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem addL_zero (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  unfold addL wadd wsmul
  cases u
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; simp
  · funext τ i; simp
  · simp

def secP (X : PJ D B P j) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (i : Fin (WeightFamilies.dimY D j + 1)) :
    MvPolynomial (Idx D j N) X.Forms :=
  ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))

section Weights

variable {X : PJ D B P j} {N : ℕ} {wL : WeightFamilies.Wt D j} {w : Fin N → B.Cusp j wL}

theorem ofWt_pow_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) : OfWt X (addL u wL (n + m)) (secP X w i ^ m * p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact hm _ _ _ _ (hs i) ih

theorem ofWt_prod_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (u : WeightFamilies.Wt D j) (n : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) (s : Finset (Fin (WeightFamilies.dimY D j))) :
    OfWt X (addL u wL (n + ∑ i ∈ s, α i)) ((∏ i ∈ s, secP X w i.succ ^ α i) * p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, add_comm (α a), ← add_assoc]
    exact ofWt_pow_mul hs hm _ u _ _ ih

end Weights

theorem inContainMR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → addL wF wL T = ka → WeightFamilies.dimY D j ≤ T → ∀ S : Scal B, Submodule.span B.KO ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ → ∀ la, InBasis G la → InContainMR G la S CR T c := by
  intro D B P j X ka wL wF G R t T CR c δ xs hgen hA hka hDT S hTh la hB
  obtain ⟨hsec, hC, hCw, hmul, -, -, hsp, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  obtain ⟨hli, hdel⟩ := (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T _ δ xs hgen hA hka la).1 hB
  have hs1 : ∀ i, toRp X la G.N (secP X G.w i) = sec X la G.w i := fun i => (hsec i).1
  have hs2 : ∀ i, R.toFn t (secP X G.w i) = R.s G.w t i := fun i => (hsec i).2.1
  have hs3 : ∀ i, OfWt X wL (secP X G.w i) := fun i => (hsec i).2.2
  have hspan : Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hdel])
  have hcon := hA.contain G.del (fun i => R.ev (X.inc wF (G.th' i)))
    (fun i => Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩) hspan

  set Gen : Set (Rp X la G.N) := ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       zAll G la S T) with hGen
  let Sp : Set (MvPolynomial (Idx D j G.N) X.Forms) := {p | OfWt X ka p ∧ toRp X la G.N p ∈ Gen}
  have hle : Submodule.span ℂ (Set.range (R.lead G.w t T (a0 D j T) fun i => R.ev (X.inc wF (G.th' i)))) ⊔
      R.deep G.w t (X.wF0 wL wF) (a0 D j T) ≤ Submodule.span ℂ (R.toFn t '' Sp) := by
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨⟨⟨al, hal⟩, i⟩, rfl⟩
      refine ⟨(∏ k, secP X G.w k.succ ^ al k) * (secP X G.w 0 ^ (T - ∑ k, al k) *
        MvPolynomial.C (X.inc wF (G.th' i))), ⟨?_, Or.inl ⟨al, i, hal, ?_⟩⟩, ?_⟩
      · have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (G.th' i)) : MvPolynomial (Idx D j G.N) X.Forms) := by
          rw [addL_zero]; exact hCw _ _
        have h1 := ofWt_prod_mul hs3 hmul al wF _ (ofWt_pow_mul hs3 hmul 0 wF 0 (T - ∑ k, al k) h0) Finset.univ
        have he : 0 + (T - ∑ k, al k) + ∑ k, al k = T := by
          unfold a0 at hal; omega
        rwa [he, hka] at h1
      · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, secPow, mul_assoc]
      · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.lead, Rdg.mon, mul_assoc]
    · rintro _ ⟨al, f, hal, hf, rfl⟩
      have hf' : f ∈ R.sp (X.wF0 wL wF)
          ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) := by
        rw [← hsp, hTh]; exact hf
      clear hf
      unfold Rdg.sp at hf'
      induction hf' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨θ, hθ, rfl⟩ := hx
        refine Submodule.subset_span ⟨(∏ k, secP X G.w k.succ ^ al k) * MvPolynomial.C (X.inc _ θ),
          ⟨?_, Or.inr ⟨al, θ, hal, hθ, ?_⟩⟩, ?_⟩
        · have h0 : OfWt X (addL wF wL (WeightFamilies.dimY D j))
              (MvPolynomial.C (X.inc _ θ) : MvPolynomial (Idx D j G.N) X.Forms) := hCw _ θ
          have h1 := ofWt_prod_mul hs3 hmul al wF _ h0 Finset.univ
          have he : WeightFamilies.dimY D j + ∑ k, al k = T := by
            unfold a0 at hal; omega
          rwa [he, hka] at h1
        · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, secPow]
        · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.mon]
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have hmem : R.ev (X.inc ka F) ∈ Submodule.span ℂ (R.toFn t '' Sp) :=
    hle (hcon (Submodule.subset_span ⟨F, hF, rfl⟩))
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.1 hmem
  choose p hp hpg using fun i => (g i).2
  have htr := (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la G.N t hgen ka (Fin n) p (fun i => (hp i).1)).2.1
    (MvPolynomial.C (X.inc ka F)) (hCw _ _)
  rw [(hC _).1, (hC _).2] at htr
  have h2 : R.ev (X.inc ka F) ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)) := by
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hpg i⟩)
  refine Submodule.span_mono ?_ (htr.2 h2)
  rintro _ ⟨i, rfl⟩
  exact (hp i).2

end GlobalTheory.Shares.Contain
