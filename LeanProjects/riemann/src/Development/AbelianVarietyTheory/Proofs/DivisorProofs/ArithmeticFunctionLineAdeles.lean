import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousSides
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverInducesDualLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFamilySignsDimensionCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFamilyRelabelledSigns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormRelabelling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionVandermondeClass
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DRRead

theorem rootDiscr_eq_vdm {ι : Type} [Fintype ι] (m : ι → ℕ) : GlobalTheory.GoodMetric.rootDiscr m = MixDens.vdm m := by
  unfold GlobalTheory.GoodMetric.rootDiscr MixDens.vdm
  refine Finset.prod_congr rfl fun τ _ => ?_
  refine Finset.prod_comm' fun j i => ?_
  simp

variable {D : D7} (O : Setup D)

def pol : MvPolynomial (EigWhole.Var O) ℝ :=
  C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) * rename Sum.inl (CovTestDR.vdmCl D.what₂.Tau O.N O.j) *
    (∑ i : Fin (D.R.f * O.N), X (Sum.inr (Sum.inr i))) ^ (dimGr D.what₂.Tau O.N O.j - 1)

theorem termW_eq (R : ℝ) (c : O.s.Comp) : termW O c R =
    numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1) (rename (EigWhole.fam O ∅ R) (pol O)) := by
  have hT : 1 ∉ (∅ : Finset ℕ) := by simp
  have e0 : ArIn.ind ∅ = fun _ => false := by funext q; simp [ArIn.ind]
  have e1 : ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c).comp (DV.tagDR D.what₂.Tau O.N) =
      rename fun x => (arIn O.s O.Φ O.met.hm).root (ArIn.ind ∅) R x c := by
    ext x : 1
    simp [ArIn.mixEv, DV.tagDR, EigWhole.update_ind_one ∅ hT]
  have e2 := congrArg (fun f => f (CovTestDR.vdmCl D.what₂.Tau O.N O.j)) e1
  simp only [AlgHom.comp_apply] at e2
  unfold termW cNum pol
  congr 1
  rw [map_mul, map_mul (rename _)]
  congr 1
  · refine (congrArg _ e2).trans ?_
    rw [map_mul, map_mul, rename_rename]
    congr 1
    simp only [ArIn.mixEv, aeval_X, EigWhole.update_ind_one ∅ hT, map_sum, map_pow, rename_X, map_mul, algHom_C]
    norm_num
    rfl
  · rw [map_pow, map_sum, ← e0]
    simp only [rename_X]
    rfl

theorem pol_isHomogeneous : (pol O).IsHomogeneous (dimFl D.what₂.Tau O.N + 1) := by
  have hι : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hj : 1 ≤ O.j := O.indef.1
  have hjN : O.j < O.N := O.indef.2
  have hpos : 1 ≤ dimGr D.what₂.Tau O.N O.j := by
    unfold dimGr
    exact Nat.mul_pos hι (Nat.mul_pos hj (by omega))
  have hV := RelabDR.vdmCl_isHomogeneous D.what₂.Tau hjN.le
  have hdim : dimGr D.what₂.Tau O.N O.j + Fintype.card D.what₂.Tau *
      ∑ i : Fin O.N, (if (i : ℕ) < O.j then O.j - 1 - (i : ℕ) else O.N - 1 - (i : ℕ)) = dimFl D.what₂.Tau O.N := by
    have h := congrArg (Fintype.card D.what₂.Tau * ·) (GlobalTheory.Mean4.WholeShift.sum_exp (N := O.N) O.j hjN.le)
    simp only [mul_add] at h
    unfold dimFl dimGr
    rw [← h]
    ring
  generalize Fintype.card D.what₂.Tau *
      ∑ i : Fin O.N, (if (i : ℕ) < O.j then O.j - 1 - (i : ℕ) else O.N - 1 - (i : ℕ)) = e at hV hdim
  have h1 := (isHomogeneous_C (EigWhole.Var O) (1 / 2 : ℝ)).mul
    (IsHomogeneous.sum (Finset.univ : Finset (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))
      (fun l => (X (Sum.inr l : EigWhole.Var O) : MvPolynomial (EigWhole.Var O) ℝ) ^ 2) 2
      fun l _ => isHomogeneous_X_pow _ 2)
  have h2 := hV.rename_isHomogeneous (f := (Sum.inl : DV.Rt D.what₂.Tau O.N → EigWhole.Var O))
  have h3 := (IsHomogeneous.sum (Finset.univ : Finset (Fin (D.R.f * O.N)))
      (fun i => (X (Sum.inr (Sum.inr i) : EigWhole.Var O) : MvPolynomial (EigWhole.Var O) ℝ)) 1
      fun l _ => isHomogeneous_X _ _).pow (dimGr D.what₂.Tau O.N O.j - 1)
  have e4 : dimFl D.what₂.Tau O.N + 1 = 0 + 2 + e + 1 * (dimGr D.what₂.Tau O.N O.j - 1) := by omega
  rw [e4]
  exact (h1.mul h2).mul h3

theorem aeval_pol : aeval (fun i => (C (RelabDR.sg O i : ℝ) * X (RelabDR.ix O i) :
      MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) (pol O) =
    (∏ σ, ((O.S.Dw.mult σ).factorial : ℝ))⁻¹ • pairPol O.S.Dw.mult (dimGr D.what₂.Tau O.N O.j - 1) := by
  have hsq : ∀ i, (C (RelabDR.sg O i : ℝ) * X (RelabDR.ix O i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2 =
      X (RelabDR.ix O i) ^ 2 := by
    intro i
    rw [mul_pow, ← C_pow, RelabDR.sg_sq_real, C_1, one_mul]
  have hR : ∑ x, (X (Sum.inl (RelabDR.rootL O x)) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2 =
      ∑ z, X (Sum.inl z) ^ 2 := Fintype.sum_bijective _ (RelabDR.rootL_bijective_sqs O) _ _ (fun _ => rfl)
  have h1 := RelabDR.aeval_halfWholeSq_sub_rootSq D O
  have h1' : aeval (fun i => (C (RelabDR.sg O i : ℝ) * X (RelabDR.ix O i) :
      MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) (∑ x, X (Sum.inl x) ^ 2 : MvPolynomial (EigWhole.Var O) ℝ) =
      ∑ z, X (Sum.inl z) ^ 2 := by
    rw [← hR]
    simp only [map_sum, map_pow, aeval_X, hsq]
    rfl
  rw [map_sub, h1', sub_left_inj] at h1
  have hc : ((fun i => (C (RelabDR.sg O i : ℝ) * X (RelabDR.ix O i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) ∘
      (Sum.inl : DV.Rt D.what₂.Tau O.N → EigWhole.Var O)) = fun x => rename Sum.inl (RelabDR.rootSub O x) := by
    funext x
    simp [RelabDR.sg, RelabDR.ix, RelabDR.rootSub]
  have hc2 : ∀ P : MvPolynomial (DV.Rt D.what₂.Tau O.N) ℝ,
      aeval (fun x => rename Sum.inl (RelabDR.rootSub O x)) P =
        rename (Sum.inl : Letter O.S.Dw → Letter O.S.Dw ⊕ Letter O.S.Dw) (aeval (RelabDR.rootSub O) P) := fun P =>
    (congrArg (fun φ => φ P) (comp_aeval (RelabDR.rootSub O)
      (rename (Sum.inl : Letter O.S.Dw → Letter O.S.Dw ⊕ Letter O.S.Dw)))).symm
  have h3 : aeval (fun i => (C (RelabDR.sg O i : ℝ) * X (RelabDR.ix O i) :
      MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ))
      (∑ i : Fin (D.R.f * O.N), X (Sum.inr (Sum.inr i)) : MvPolynomial (EigWhole.Var O) ℝ) = -∑ z, X (Sum.inr z) := by
    rw [← ((RelabDR.wholeL_bijective_sqs O).comp Fin.revPerm.bijective).sum_comp
      (fun z => (X (Sum.inr z) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)), ← Finset.sum_neg_distrib, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [RelabDR.sg, RelabDR.ix]
  have hf : (∏ σ, ((O.S.Dw.mult σ).factorial : ℝ))⁻¹ =
      ((O.j.factorial : ℝ)⁻¹ * ((O.N - O.j).factorial : ℝ)⁻¹) ^ Fintype.card D.what₂.Tau := by
    rw [← Nat.cast_prod, RelabDRVdm.prod_fact, ← mul_inv, inv_pow]
    push_cast
    rfl
  unfold pol pairPol
  rw [map_mul, map_mul, h1, map_pow, h3, aeval_rename, hc, hc2, RelabDRVdm.aeval_vdmCl, ← RelabDRVdm.rootDiscr_eq,
    rootDiscr_eq_vdm, hf, map_mul, rename_C, smul_eq_C_mul]
  ring

theorem termW_read : ArCalc → ArDegree → ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (V : Cover (O.var c)) (x x' : Letter O.S.Dw → HermLB V.p), (∀ z : Letter O.S.Dw, V.Induces (lineAdl O R c (.inl (z.1, z.2)) 1) (x z) 1) → (∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z → V.Induces (lineAdl O R c (.inr k) 1) (x' z) 1) → ∀ Φ : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ →ₗ[ℝ] ℝ, IsArFun (Sum.elim x x') (O.var c).dim Φ → termW O c R = Φ (pairPol O.S.Dw.mult (dimGr D.what₂.Tau O.N O.j - 1)) / ((∏ σ, ((O.S.Dw.mult σ).factorial : ℝ)) * V.ν) := by
  intro hC hD D O hO R hR c V x₁ x₂ h₁ h₂ Φ hΦ
  obtain ⟨hsg, hfam⟩ := RelabDR.fam_eq_single D O
  obtain ⟨t, P, hW⟩ := id hO
  have hm := hW.hm_eq
  obtain ⟨-, h2⟩ := GlobalTheory.ArTopTrue.arTop_true hC hD GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s t O.Φ c R hR
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := h2 (EigWhole.Var O) (EigWhole.fam O ∅ R) (EigWhole.fam_support O _ R)
  have hdim : (O.var c).dim = dimFl D.what₂.Tau O.N := O.dim_eq c
  have hnum' : ∀ μ : Multiset (EigWhole.Var O), Multiset.card μ = dimFl D.what₂.Tau O.N + 1 →
      (arIn O.s O.Φ O.met.hm).num c (μ.map (EigWhole.fam O ∅ R)) =
        Ψ ((μ.map X).prod) / ((((m : ℕ) : ℝ)) ^ ((O.var c).dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) := by
    intro μ hμ
    rw [hm]
    exact hnum μ (hμ.trans (congrArg (· + 1) hdim.symm))
  have key := GlobalTheory.NumLRename.numL_rename_of_agree _ _ _ Ψ _ hnum' _ (pol_isHomogeneous O)
  have hL : ∀ i, (adlOf (O.Φ.C c) (O.met.hm c) (EigWhole.fam O ∅ R i)).Induced M (L i) m 0 := by
    rw [hm]; exact hI
  set ix := RelabDR.ix O with hix
  set sg := RelabDR.sg O with hsgd
  let x : Letter O.S.Dw ⊕ Letter O.S.Dw → HermLB V.p := Sum.elim x₁ x₂
  let L' : EigWhole.Var O → HermLB V.p := fun i => if sg i = 1 then x (ix i) else (x (ix i)).dual
  have hIso : ArIso := hC.2.2.2.2.2.1
  have hΦ' := ((hIso _ V.X V.p _ V.ar).2 _ x Φ hΦ).2.2 _ L' (fun i => Pi.single (ix i) (sg i)) fun i => by
    refine HermLB.icls_eq_iff.1 ?_
    rw [icls_comb, Finset.sum_eq_single (ix i) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
      Pi.single_eq_same]
    rcases hsg i with e₁ | e₁
    · simp only [L', e₁, if_true, one_smul]
    · simp only [L', e₁, neg_smul, one_smul]
      rw [if_neg (by norm_num), HermLB.icls_dual]
  have hind : ∀ i, V.Induces (adlOf (O.Φ.C c) (O.met.hm c) (EigWhole.fam O ∅ R i)) (L' i) 1 := fun i => by
    have key (st) (hst : V.Induces (lineAdl O R c st 1) (x (ix i)) 1) : V.Induces (lineAdl O R c st (sg i)) (L' i) 1 := by
      rcases hsg i with e₁ | e₁
      · simpa only [L', e₁, if_true] using hst
      · simp only [L', e₁]
        rw [if_neg (by norm_num)]
        exact GlobalTheory.TwoLat.induces_lineAdl_neg D O hO R c V st _ hst
    rcases hfam R i with ⟨z, hz, e₁⟩ | ⟨z, k, hz, hk, e₁⟩
    · rw [e₁]
      exact key _ (by rw [hz]; exact h₁ z)
    · rw [e₁]
      exact key _ (by rw [hz]; exact h₂ k z hk)
  have hcmp := GlobalTheory.CoverModelTop.top_eq hC hD (O.var c) (Equiv.refl _) _ (fun _ => rfl) M L m Ψ hL hΨ V L' _ hind hΦ'
  obtain ⟨I, _, a, b, hs⟩ := FlagCmp.exists_sum_pow (pol_isHomogeneous O)
  have hA : (fun j : EigWhole.Var O => lin fun i => (((Pi.single (ix j) (sg j) : _ → ℤ) i : ℤ) : ℝ)) =
      fun i => (C (sg i : ℝ) * X (ix i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) := funext fun j => by
    rw [lin, Finset.sum_eq_single (ix j) (fun i _ hi => by rw [Pi.single_eq_of_ne hi]; simp) (by simp), Pi.single_eq_same]
  have halg := aeval_pol O
  rw [← hix, ← hsgd, ← hA] at halg
  have hfin : Φ (pairPol O.S.Dw.mult (dimGr D.what₂.Tau O.N O.j - 1)) / ((∏ σ, ((O.S.Dw.mult σ).factorial : ℝ)) * V.ν) =
      Φ ((∏ σ, ((O.S.Dw.mult σ).factorial : ℝ))⁻¹ • pairPol O.S.Dw.mult (dimGr D.what₂.Tau O.N O.j - 1)) / V.ν := by
    rw [map_smul, smul_eq_mul, inv_mul_eq_div, div_div]
  refine (termW_eq O R c).trans (key.trans ?_)
  rw [hfin, ← halg, ← hs, map_sum, Finset.sum_div, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hcmp (b j)
  rw [hdim] at this ⊢
  rw [map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc, mul_div_assoc, this]
  rfl

end GlobalTheory.DRRead

end
