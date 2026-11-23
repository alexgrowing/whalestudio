import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousSides
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamModelDR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedModelDeRhamOfHeightAlterationStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.CovTestDR GlobalTheory.EigWhole

namespace GlobalTheory.EigWholeDR

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
    (vdmCl ι N j).IsHomogeneous
      (Fintype.card ι * ∑ i : Fin N, (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ))) := by
  unfold vdmCl
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

end GlobalTheory.EigWholeDR

namespace GlobalTheory.EigWholeDR

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

variable {D : D7} (O : Setup D)

theorem testG_isHomogeneous : ∃ m, m + 2 = dimFl D.what₂.Tau O.N + 1 ∧ (testG O).IsHomogeneous m := by
  classical
  have hι : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hj : 1 ≤ O.j := O.indef.1
  have hjN : O.j < O.N := O.indef.2
  have hpos : 1 ≤ dimGr D.what₂.Tau O.N O.j := by
    unfold dimGr
    exact Nat.mul_pos hι (Nat.mul_pos hj (by omega))
  refine ⟨_, ?_, ((WholeShift.lamA_isHomogeneous (ι := D.what₂.Tau) (N := O.N) O.j).pow
    (dimGr D.what₂.Tau O.N O.j - 1)).mul ((WholeShift.fibPt_isHomogeneous O.j).sub (vdmCl_isHomogeneous D.what₂.Tau hjN.le))⟩
  have h := congrArg (Fintype.card D.what₂.Tau * ·) (WholeShift.sum_exp (N := O.N) O.j hjN.le)
  simp only [mul_add] at h
  unfold dimFl
  unfold dimGr at hpos ⊢
  omega

theorem mixEv_empty (R : ℝ) (c : O.s.Comp) (P : Pol D.what₂.Tau O.N) :
    (arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N P) =
      rename (fam O ∅ R) (C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) * rename Sum.inl P) := by
  have hT : (1 : ℕ) ∉ (∅ : Finset ℕ) := Finset.notMem_empty 1
  have e1 : ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c).comp (DV.tagDR D.what₂.Tau O.N) =
      rename fun x => (arIn O.s O.Φ O.met.hm).root (ArIn.ind ∅) R x c := by
    ext x : 1
    simp [ArIn.mixEv, DV.tagDR, update_ind_one ∅ hT]
  have e2 := congrArg (fun f => f P) e1
  simp only [AlgHom.comp_apply] at e2
  rw [map_mul, e2, map_mul, map_mul, rename_rename]
  congr 1
  simp only [ArIn.mixEv, aeval_X, update_ind_one ∅ hT, map_sum, map_pow, rename_X, map_mul, algHom_C]
  norm_num
  rfl

theorem rename_root_sq (R : ℝ) (c : O.s.Comp) (P : Pol D.what₂.Tau O.N) :
    rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind ∅) R y c) ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.N)) * P) =
      rename (fam O ∅ R) ((∑ x, X (Sum.inl x) ^ 2) * rename Sum.inl P) := by
  have hp : (∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.N)) = ∑ x : DV.Rt D.what₂.Tau O.N, X x ^ 2 := by
    simp only [pSum]
    rw [Fintype.sum_prod_type]
  rw [hp]
  simp only [map_mul, map_sum, map_pow, rename_X, rename_rename, Function.comp_def]
  rfl

theorem comp_eqDR (hM : RamModelDR) (hC : ArCalc) (hD : ArDegree) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R)
    (c : O.s.Comp) (hA : AwayAgree O ∅ R c) :
    numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (testG O))) =
      numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind ∅) R y c)
          ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.N)) * testG O)) := by
  obtain ⟨x, P, hW⟩ := hO
  have hm := hW.hm_eq
  obtain ⟨-, h2⟩ := GlobalTheory.ArTopTrue.arTop_true hC hD GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s x O.Φ c R hR
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := h2 (Var O) (fam O ∅ R) (fam_support O _ R)
  have hdim := O.dim_eq c
  have hnum' : ∀ μ : Multiset (Var O), Multiset.card μ = dimFl D.what₂.Tau O.N + 1 →
      (arIn O.s O.Φ O.met.hm).num c (μ.map (fam O ∅ R)) =
        Ψ ((μ.map X).prod) / ((((m : ℕ) : ℝ)) ^ ((O.Φ.C c).Y.dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) := by
    intro μ hμ
    rw [hm]
    exact hnum μ (by rw [hdim]; exact hμ)
  have key := GlobalTheory.NumLRename.numL_rename_of_agree _ _ _ Ψ _ hnum'
  have hz := hM D O ⟨x, P, hW⟩ R hR c hA M L m Ψ (by rw [hm]; exact hI) hΨ
  obtain ⟨k, hk, hG⟩ := testG_isHomogeneous O
  have hG' := hG.rename_isHomogeneous (f := (Sum.inl : DV.Rt D.what₂.Tau O.N → Var O))
  have hsq : ∀ v : Var O, (X v ^ 2 : MvPolynomial (Var O) ℝ).IsHomogeneous 2 := fun v => by
    simpa using (isHomogeneous_X ℝ v).pow 2
  have hPL : ((∑ x, X (Sum.inl x) ^ 2) * rename (Sum.inl : DV.Rt D.what₂.Tau O.N → Var O) (testG O)).IsHomogeneous
      (dimFl D.what₂.Tau O.N + 1) := by
    have := (IsHomogeneous.sum Finset.univ (fun x : DV.Rt D.what₂.Tau O.N => (X (Sum.inl x) ^ 2 : MvPolynomial (Var O) ℝ))
      2 fun x _ => hsq (Sum.inl x)).mul hG'
    rwa [add_comm, hk] at this
  have hPR : (C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) *
      rename (Sum.inl : DV.Rt D.what₂.Tau O.N → Var O) (testG O)).IsHomogeneous (dimFl D.what₂.Tau O.N + 1) := by
    have := ((isHomogeneous_C (Var O) (1 / 2 : ℝ)).mul (IsHomogeneous.sum Finset.univ
      (fun l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N) => (X (Sum.inr l) ^ 2 : MvPolynomial (Var O) ℝ)) 2
      fun l _ => hsq (Sum.inr l))).mul hG'
    rwa [zero_add, add_comm, hk] at this
  rw [rename_root_sq, mixEv_empty]
  refine (key _ hPR).trans (Eq.trans ?_ (key _ hPL).symm)
  congr 1
  have e : diffPolDR O = C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) * rename Sum.inl (testG O) -
      (∑ x, X (Sum.inl x) ^ 2) * rename Sum.inl (testG O) := by
    rw [diffPolDR]; ring
  rw [e, map_sub, sub_eq_zero] at hz
  exact hz

theorem whole_eq_eig_of_ramModelDR : RamModelDR → Hypotheses2 → HypothesesH → RegularAlteration →
    OnObj fun D O _ _ _ _ => ∀ R : ℝ, 2 ≤ R →
      O.Y.arMix ∅ R 1 (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.Y.N
        (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) *
          (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) =
      O.Y.arDeg ∅ R ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.Y.N)) *
        (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) *
          (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) := by
  intro hM h2 hH _ D O hO _ A T H hRd R hR
  have eL : (arIn O.s O.Φ O.met.hm).arMix ∅ R 1 (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (testG O)) =
      ∑ c, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (testG O))) := by
    rw [ArIn.arMix, LinearMap.sum_apply]; rfl
  have eR : (arIn O.s O.Φ O.met.hm).arDeg ∅ R ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.N)) * testG O) =
      ∑ c, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind ∅) R y c)
          ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.N)) * testG O)) := by
    rw [ArIn.arDeg, LinearMap.sum_apply]; rfl
  exact eL.trans ((Finset.sum_congr rfl fun c _ =>
    comp_eqDR O hM h2.p4 hH.deg hO R hR c (GlobalTheory.T.eigen_away_agree D O hO ∅ R c)).trans eR.symm)

end GlobalTheory.EigWholeDR

namespace GlobalTheory.EigWholeDR

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

theorem whole_eq_eig_DR : Hypotheses2 → HypothesesH → RegularAlteration →
    OnObj fun D O _ _ _ _ => ∀ R : ℝ, 2 ≤ R →
      O.Y.arMix ∅ R 1 (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.Y.N
        (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) *
          (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) =
      O.Y.arDeg ∅ R ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.Y.N)) *
        (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) *
          (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) :=
  fun h2 hH hR => whole_eq_eig_of_ramModelDR (GlobalTheory.T.ramified_model_de_rham_of_height_alteration h2 hH hR) h2 hH hR

end GlobalTheory.EigWholeDR

end
