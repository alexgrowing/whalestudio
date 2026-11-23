import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFamilyRelabelledSignsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormRelabellingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionLambdaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionFibreDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionVandermondeClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDR

theorem count_pairs {N j : ℕ} (hj : j ≤ N) (a : Fin N) :
    (∑ b : Fin N, if a < b ∧ (b : ℕ) < j then 1 else 0) + (∑ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then 1 else 0) =
      if (a : ℕ) < j then j - 1 - (a : ℕ) else N - 1 - (a : ℕ) := by
  simp only [Fin.lt_iff_val_lt_val]
  rw [Fin.sum_univ_eq_sum_range (fun b => if (a : ℕ) < b ∧ b < j then 1 else 0) N,
    Fin.sum_univ_eq_sum_range (fun b => if (a : ℕ) < b ∧ j ≤ (a : ℕ) then 1 else 0) N]
  rw [Finset.sum_boole, Finset.sum_boole]
  split_ifs with ha
  · have e1 : (Finset.range N).filter (fun b => (a : ℕ) < b ∧ b < j) = Finset.Ioo (a : ℕ) j := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; omega
    have e2 : (Finset.range N).filter (fun b => (a : ℕ) < b ∧ j ≤ (a : ℕ)) = ∅ := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]; omega
    rw [e1, e2, Nat.card_Ioo, Finset.card_empty]
    simp only [Nat.cast_id]
    omega
  · have e1 : (Finset.range N).filter (fun b => (a : ℕ) < b ∧ b < j) = ∅ := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]; omega
    have e2 : (Finset.range N).filter (fun b => (a : ℕ) < b ∧ j ≤ (a : ℕ)) = Finset.Ioo (a : ℕ) N := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; omega
    rw [e1, e2, Nat.card_Ioo, Finset.card_empty]
    simp only [Nat.cast_id]
    omega

theorem vdmCl_isHomogeneous (ι : Type) [Fintype ι] {N j : ℕ} (hj : j ≤ N) :
    (GlobalTheory.CovTestDR.vdmCl ι N j).IsHomogeneous
      (Fintype.card ι * ∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) := by
  unfold GlobalTheory.CovTestDR.vdmCl
  have hτ : ∀ τ : ι, ((C ((Nat.factorial j : ℝ)⁻¹) *
      ∏ a : Fin N, ∏ b : Fin N, if a < b ∧ (b : ℕ) < j then X (τ, b) - X (τ, a) else 1) *
    (C ((Nat.factorial (N - j) : ℝ)⁻¹) *
      ∏ a : Fin N, ∏ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then X (τ, b) - X (τ, a) else 1) : Pol ι N).IsHomogeneous
        (∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) := by
    intro τ
    have h1 : (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ (b : ℕ) < j then X (τ, b) - X (τ, a) else 1 : Pol ι N).IsHomogeneous
        (∑ a : Fin N, ∑ b : Fin N, if a < b ∧ (b : ℕ) < j then 1 else 0) :=
      IsHomogeneous.prod _ _ _ fun a _ => IsHomogeneous.prod _ _ _ fun b _ => by
        split_ifs
        · exact (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)
        · exact isHomogeneous_one _ _
    have h2 : (∏ a : Fin N, ∏ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then X (τ, b) - X (τ, a) else 1 : Pol ι N).IsHomogeneous
        (∑ a : Fin N, ∑ b : Fin N, if a < b ∧ j ≤ (a : ℕ) then 1 else 0) :=
      IsHomogeneous.prod _ _ _ fun a _ => IsHomogeneous.prod _ _ _ fun b _ => by
        split_ifs
        · exact (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)
        · exact isHomogeneous_one _ _
    have h := ((isHomogeneous_C (ι × Fin N) ((Nat.factorial j : ℝ)⁻¹)).mul h1).mul
      ((isHomogeneous_C (ι × Fin N) ((Nat.factorial (N - j) : ℝ)⁻¹)).mul h2)
    convert h using 1
    rw [zero_add, zero_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (count_pairs hj a).symm
  have := IsHomogeneous.prod (Finset.univ : Finset ι) _ _ fun τ _ => hτ τ
  convert this using 1
  simp

open Classical in

theorem antisymm_sub {ι : Type} [Fintype ι] {m : ι → ℕ} (P Q : MvPolynomial (GlobalTheory.GoodMetric.Root m) ℝ) :
    GlobalTheory.GoodMetric.antisymm (P - Q) = GlobalTheory.GoodMetric.antisymm P - GlobalTheory.GoodMetric.antisymm Q := by
  unfold GlobalTheory.GoodMetric.antisymm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_sub, smul_sub]

open Classical in

theorem antisymm_smul {ι : Type} [Fintype ι] {m : ι → ℕ} (r : ℝ) (P : MvPolynomial (GlobalTheory.GoodMetric.Root m) ℝ) :
    GlobalTheory.GoodMetric.antisymm (r • P) = r • GlobalTheory.GoodMetric.antisymm P := by
  unfold GlobalTheory.GoodMetric.antisymm
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, smul_comm]

theorem relabel_diffPolDR : ∀ (D : D7) (O : Setup D), ∃ (ix : GlobalTheory.EigWhole.Var O → Letter O.S.Dw ⊕ Letter O.S.Dw) (sg : GlobalTheory.EigWhole.Var O → ℤ) (n e : ℕ) (Q : MvPolynomial (Letter O.S.Dw) ℝ), n + 1 = dimGr D.what₂.Tau O.N O.j ∧ n + 1 + e = dimFl D.what₂.Tau O.N ∧ (∀ i, sg i = 1 ∨ sg i = -1) ∧ (∀ (R : ℝ) i, (∃ z, ix i = .inl z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inl (z.1, (z.2 : ℕ))) (sg i)) ∨ ∃ z k, ix i = .inr z ∧ (letters O.S.Dw)[k]? = some z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inr k) (sg i)) ∧ Q.IsHomogeneous e ∧ GlobalTheory.GoodMetric.antisymm Q = 0 ∧ (GlobalTheory.EigWholeDR.diffPolDR O).IsHomogeneous (n + 1 + e + 1) ∧ aeval (fun i => (C (sg i : ℝ) * X (ix i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) (GlobalTheory.EigWholeDR.diffPolDR O) = (∑ z, X (Sum.inr z) ^ 2 - ∑ z, X (Sum.inl z) ^ 2) * rename Sum.inl ((∑ z, X z) ^ n * Q) := by
  intro D O
  obtain ⟨hsg, hfam⟩ := GlobalTheory.T.eigen_family_relabelled_signs D O
  have hι : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hj : 1 ≤ O.j := O.indef.1
  have hjN : O.j < O.N := O.indef.2
  have hpos : 1 ≤ dimGr D.what₂.Tau O.N O.j := by
    unfold dimGr
    exact Nat.mul_pos hι (Nat.mul_pos hj (by omega))
  have hF := GlobalTheory.Mean4.WholeShift.fibPt_isHomogeneous (ι := D.what₂.Tau) (N := O.N) O.j
  have hV := vdmCl_isHomogeneous D.what₂.Tau hjN.le
  have hdim : dimGr D.what₂.Tau O.N O.j + Fintype.card D.what₂.Tau *
      ∑ i : Fin O.N, (if (i : ℕ) < O.j then O.j - 1 - (i : ℕ) else O.N - 1 - (i : ℕ)) = dimFl D.what₂.Tau O.N := by
    have h := congrArg (Fintype.card D.what₂.Tau * ·) (GlobalTheory.Mean4.WholeShift.sum_exp (N := O.N) O.j hjN.le)
    simp only [mul_add] at h
    unfold dimFl dimGr
    rw [← h]
    ring
  have hsub : ∀ x, (rootSub O x).IsHomogeneous 1 := fun x => isHomogeneous_C_mul_X _ _
  generalize Fintype.card D.what₂.Tau *
      ∑ i : Fin O.N, (if (i : ℕ) < O.j then O.j - 1 - (i : ℕ) else O.N - 1 - (i : ℕ)) = e at hF hV hdim
  refine ⟨ix O, sg O, dimGr D.what₂.Tau O.N O.j - 1, e,
    ((-1 : ℝ) ^ (dimGr D.what₂.Tau O.N O.j - 1)) • (aeval (rootSub O) (fibPt D.what₂.Tau O.N O.j) -
      aeval (rootSub O) (GlobalTheory.CovTestDR.vdmCl D.what₂.Tau O.N O.j)), by omega, by omega, hsg, hfam, ?_, ?_, ?_, ?_⟩
  · have h1 := (hF.aeval (rootSub O) hsub).sub (hV.aeval (rootSub O) hsub)
    rw [one_mul] at h1
    rw [smul_eq_C_mul]
    have h2 := (isHomogeneous_C (Letter O.S.Dw) ((-1 : ℝ) ^ (dimGr D.what₂.Tau O.N O.j - 1))).mul h1
    rwa [zero_add] at h2
  · rw [antisymm_smul, antisymm_sub, GlobalTheory.T.root_substitution_fibre_discriminant, GlobalTheory.T.root_substitution_vandermonde_class, sub_self, smul_zero]
  · unfold GlobalTheory.EigWholeDR.diffPolDR GlobalTheory.EigWholeDR.testG
    have hA : (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2 :
        MvPolynomial (GlobalTheory.EigWhole.Var O) ℝ).IsHomogeneous 2 := by
      refine IsHomogeneous.sub ?_ ?_
      · have h3 := (isHomogeneous_C (GlobalTheory.EigWhole.Var O) (1 / 2 : ℝ)).mul
          (IsHomogeneous.sum (Finset.univ : Finset (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))
            (fun l => (X (Sum.inr l : GlobalTheory.EigWhole.Var O) : MvPolynomial (GlobalTheory.EigWhole.Var O) ℝ) ^ 2) 2
            fun l _ => isHomogeneous_X_pow _ 2)
        rwa [zero_add] at h3
      · exact IsHomogeneous.sum (Finset.univ : Finset (DV.Rt D.what₂.Tau O.N))
          (fun x => (X (Sum.inl x : GlobalTheory.EigWhole.Var O) : MvPolynomial (GlobalTheory.EigWhole.Var O) ℝ) ^ 2) 2
          fun x _ => isHomogeneous_X_pow _ 2
    have hG := (((GlobalTheory.Mean4.WholeShift.lamA_isHomogeneous (ι := D.what₂.Tau) (N := O.N) O.j).pow
      (dimGr D.what₂.Tau O.N O.j - 1)).mul (hF.sub hV)).rename_isHomogeneous (f := (Sum.inl : DV.Rt D.what₂.Tau O.N → GlobalTheory.EigWhole.Var O))
    convert hA.mul hG using 1
    omega
  · unfold GlobalTheory.EigWholeDR.diffPolDR GlobalTheory.EigWholeDR.testG
    rw [map_mul, GlobalTheory.T.quadratic_form_relabelling D O, aeval_rename]
    have hc : ((fun i => (C (sg O i : ℝ) * X (ix O i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) ∘
        (Sum.inl : DV.Rt D.what₂.Tau O.N → GlobalTheory.EigWhole.Var O)) = fun x => rename Sum.inl (rootSub O x) := by
      funext x
      simp [sg, ix, rootSub]
    have hc2 : ∀ P : MvPolynomial (DV.Rt D.what₂.Tau O.N) ℝ,
        aeval (fun x => rename Sum.inl (rootSub O x)) P = rename Sum.inl (aeval (rootSub O) P) := fun P =>
      (congrArg (fun φ => φ P) (comp_aeval (rootSub O) (rename (Sum.inl : Letter O.S.Dw → Letter O.S.Dw ⊕ Letter O.S.Dw)))).symm
    rw [hc, hc2]
    congr 2
    rw [map_mul, map_pow, GlobalTheory.T.root_substitution_lambda, map_sub, smul_eq_C_mul, map_pow, map_neg, map_one, neg_pow]
    ring
end GlobalTheory.RelabDR

end
