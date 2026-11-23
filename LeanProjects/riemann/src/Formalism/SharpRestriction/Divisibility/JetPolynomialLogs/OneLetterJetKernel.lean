import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.DworkPowerSeriesWeights
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
import Formalism.GaussJetBounds.GaussJetProofs.OneGauss
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel

open Formalism.MainNotions Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights

theorem jetLogG_eq_entLog (l d N0 N1 : ℕ) [Fact l.Prime] [NeZero d] (v : ZV d N0 N1) :
    Formalism.BasicNotions.jetLogG l d (β := Fin N0 × Fin N1) v = entLog (K := ℂ_[l]) l v := by
  funext m
  have hdeg : Formalism.BasicNotions.JetTdeg m = m.degree := rfl
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1), _) = ∑ e ∈ Finset.range (m.degree + 1), _
  rw [hdeg]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2.1, v.2.2) ((l ^ 2) ^ e)
  · rw [if_pos (by exact h), if_pos h]
  · rw [if_neg (by exact h), if_neg h]

theorem cc_jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) :
    MvPowerSeries.constantCoeff (Formalism.BasicNotions.jetLogG l d v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg (0 : ZMod d × β →₀ ℕ) + 1), _) = 0
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)

theorem hasSubst_jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} [Finite β] [NeZero d] :
    MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β := β)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_jetLogG l d)

theorem hasSubst_CX {σ : Type*} [Finite σ] {K : Type*} [CommRing K] (c : K) :
    MvPowerSeries.HasSubst (fun v : σ => MvPowerSeries.C c * (MvPowerSeries.X v : MvPowerSeries σ K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp

theorem beSum_eq (L : product_zeroth_first_parts.Loc) (be : MvPowerSeries (ZMod L.d) ℂ_[L.l]) :
    L.beSum be = bSum (idM : ZV L.d L.N0 L.N1 → ZV L.d L.N0 L.N1 → ℂ_[L.l]) be := by
  unfold product_zeroth_first_parts.Loc.beSum bSum
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  funext s
  exact (OrbMul.linSub_idM (s, a, b)).symm

theorem kernel_from_twist_holds : KernelFromExponentialTwist := by
  intro L ep be hep hB0
  classical
  obtain ⟨sg, hsg, U, hU, hTh⟩ := hB0
  obtain ⟨g, hg0, hg, -⟩ := generalized_log_inverse.{0, 0} ℂ_[L.l] L.l (Fact.out)
    (ZV L.d L.N0 L.N1) (fun y => (y.1 - 2, y.2.1, y.2.2))
  have hent := (logarithm_weight_comparison.{0} ℂ_[L.l] L.l L.d L.N0 L.N1).2.1
  have hg' : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[L.l]) L.l y) = MvPowerSeries.X y :=
    fun y => by rw [hent]; exact hg y
  refine ⟨g, U, sg, hg0, hg', hU, hsg, ?_⟩
  rw [OrbMul.thetaZ_eq]
  have hgs : MvPowerSeries.HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg0
  have hlg := hasSubst_jetLogG L.l L.d (β := Fin L.N0 × Fin L.N1)
  set Φ := MvPowerSeries.subst (fun v : ZMod L.d × Fin L.N0 × Fin L.N1 =>
    MvPowerSeries.C ep * (MvPowerSeries.X v : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l])) L.Th
    with hΦ
  have h1 : L.Tht ep = MvPowerSeries.subst (Formalism.BasicNotions.jetLogG L.l L.d (β := Fin L.N0 × Fin L.N1)) Φ := by
    unfold product_zeroth_first_parts.Loc.Tht
    rw [hΦ, MvPowerSeries.subst_comp_subst_apply (hasSubst_CX ep) hlg]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hlg, MvPowerSeries.subst_C, MvPowerSeries.subst_X hlg]
  have hinv : ∀ F : MvPowerSeries (ZV L.d L.N0 L.N1) ℂ_[L.l],
      MvPowerSeries.subst g (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG L.l L.d (β := Fin L.N0 × Fin L.N1)) F) = F := by
    intro F
    rw [MvPowerSeries.subst_comp_subst_apply hlg hgs]
    have : (fun v => MvPowerSeries.subst g (Formalism.BasicNotions.jetLogG L.l L.d (β := Fin L.N0 × Fin L.N1) v)) =
        (MvPowerSeries.X : ZV L.d L.N0 L.N1 → MvPowerSeries (ZV L.d L.N0 L.N1) ℂ_[L.l]) := by
      funext v
      rw [jetLogG_eq_entLog]
      exact hg' v
    rw [this, MvPowerSeries.subst_self]
    rfl
  have h2 := congrArg (MvPowerSeries.subst g) (h1.symm.trans hTh)
  rw [hinv, MvPowerSeries.subst_mul hgs, hinv] at h2
  rw [h2, beSum_eq]
  rfl

abbrev V1 (N0 N1 : ℕ) := ZMod 1 × Fin N0 × Fin N1

def prEquiv (N0 N1 : ℕ) : V1 N0 N1 ≃ Fin N0 × Fin N1 where
  toFun w := w.2
  invFun x := (0, x)
  left_inv w := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv x := rfl

theorem hasSubst_pr (N0 N1 : ℕ) {K : Type} [CommRing K] :
    MvPowerSeries.HasSubst (fun w : V1 N0 N1 => (MvPowerSeries.X w.2 : MvPowerSeries (Fin N0 × Fin N1) K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => MvPowerSeries.constantCoeff_X _

theorem subst_pr_eq_rename (N0 N1 : ℕ) {K : Type} [CommRing K] (f : MvPowerSeries (V1 N0 N1) K) :
    MvPowerSeries.subst (fun w : V1 N0 N1 => (MvPowerSeries.X w.2 : MvPowerSeries (Fin N0 × Fin N1) K)) f =
      MvPowerSeries.rename (prEquiv N0 N1).toEmbedding f := by
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem exists_embDomain_pr (N0 N1 : ℕ) (n : Fin N0 × Fin N1 →₀ ℕ) :
    ∃ m, Finsupp.embDomain (prEquiv N0 N1).toEmbedding m = n :=
  ⟨Finsupp.comapDomain (prEquiv N0 N1).toEmbedding n (prEquiv N0 N1).toEmbedding.injective.injOn,
    Finsupp.embDomain_comapDomain (by
      intro x _
      exact ⟨(0, x), rfl⟩)⟩

theorem integral_subst_pr (N0 N1 : ℕ) {K : Type} [NormedField K] {U : MvPowerSeries (V1 N0 N1) K}
    (hU : Integral U) :
    Integral (MvPowerSeries.subst (fun w : V1 N0 N1 => (MvPowerSeries.X w.2 : MvPowerSeries (Fin N0 × Fin N1) K)) U) := by
  intro n
  rw [subst_pr_eq_rename]
  obtain ⟨m, rfl⟩ := exists_embDomain_pr N0 N1 n
  rw [MvPowerSeries.coeff_embDomain_rename]
  exact hU m

theorem subst_pr_jetLogG (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (v : V1 N0 N1) :
    MvPowerSeries.subst (fun w : V1 N0 N1 => (MvPowerSeries.X w.2 : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]))
      (Formalism.BasicNotions.jetLogG l 1 v) = oneLog (K := ℂ_[l]) l v.2 := by
  classical
  rw [subst_pr_eq_rename]
  ext n
  obtain ⟨m, rfl⟩ := exists_embDomain_pr N0 N1 n
  rw [MvPowerSeries.coeff_embDomain_rename]
  have hdeg : (Finsupp.embDomain (prEquiv N0 N1).toEmbedding m).degree = Formalism.BasicNotions.JetTdeg m := by
    show (Finsupp.embDomain (prEquiv N0 N1).toEmbedding m).sum (fun _ k => k) = m.sum (fun _ k => k)
    rw [Finsupp.sum_embDomain]
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1), _) = ∑ e ∈ Finset.range (_ + 1), _
  rw [hdeg]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hs : Finsupp.single v.2 ((l ^ 2) ^ e) =
      Finsupp.embDomain (prEquiv N0 N1).toEmbedding
        (Finsupp.single (v.1 - 2 * (e : ZMod 1), v.2) ((l ^ 2) ^ e)) := by
    rw [Finsupp.embDomain_single]
    rfl
  have hiff : (m = Finsupp.single (v.1 - 2 * (e : ZMod 1), v.2) ((l ^ 2) ^ e)) ↔
      (Finsupp.embDomain (prEquiv N0 N1).toEmbedding m = Finsupp.single v.2 ((l ^ 2) ^ e)) := by
    rw [hs, Finsupp.embDomain_inj]
  by_cases h : m = Finsupp.single (v.1 - 2 * (e : ZMod 1), v.2) ((l ^ 2) ^ e)
  · rw [if_pos (by exact h), if_pos (hiff.mp h)]
  · rw [if_neg (by exact h), if_neg (fun h' => h (hiff.mpr h'))]

theorem constant_coeff_zero_of_vanishing_alt (l d : ℕ) [Fact l.Prime] [NeZero d] {be : MvPowerSeries (ZMod d) ℂ_[l]}
    (h3 : product_zeroth_first_parts.B3 l d be) : MvPowerSeries.constantCoeff be = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  by_contra h
  have := (h3 0 h).1
  apply this
  simp [product_zeroth_first_parts.bideg]

def KernelTwistOneLetterVanishing : Prop :=
  ∀ (L : product_zeroth_first_parts.Loc1) (ep0 : ℂ_[L.l]) (be : MvPowerSeries (ZMod 2) ℂ_[L.l]), ‖ep0‖ = 1 → product_zeroth_first_parts.B3 L.l 2 be →
    L.B0 ep0 be →
    ∃ (g : Fin L.N0 × Fin L.N1 → MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l])
      (U : MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l]) (sgn ep : ℂ_[L.l]), ‖ep‖ = 1 ∧
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) ∧
      (∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[L.l]) L.l y) = MvPowerSeries.X y) ∧
      Integral U ∧ (sgn = 1 ∨ sgn = -1) ∧
      MvPowerSeries.subst (fun v : ZMod 1 × Fin L.N0 × Fin L.N1 =>
        MvPowerSeries.C ep0 * (MvPowerSeries.X v.2 : MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l])) L.Th =
        thetaOne g U sgn ep be

theorem kernel_twist_one_letter_vanishing : KernelTwistOneLetterVanishing := by
  intro L ep0 be hep0 h3 hB0
  classical
  obtain ⟨ep, hep, sg, hsg, U, hU, hTh⟩ := hB0
  have hbe := constant_coeff_zero_of_vanishing_alt L.l 2 h3
  obtain ⟨G, hG0, hG, -⟩ := generalized_log_inverse.{0, 0} ℂ_[L.l] L.l (Fact.out)
    (ZV 1 L.N0 L.N1) (fun y => (y.1 - 2, y.2.1, y.2.2))
  have hent := (logarithm_weight_comparison.{0} ℂ_[L.l] L.l 1 L.N0 L.N1).2.1
  have hG' : ∀ y, MvPowerSeries.subst G (Formalism.BasicNotions.jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1) y) = MvPowerSeries.X y :=
    fun y => by rw [jetLogG_eq_entLog, hent]; exact hG y
  have hGs : MvPowerSeries.HasSubst G := MvPowerSeries.hasSubst_of_constantCoeff_zero hG0
  have hlg := hasSubst_jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1)
  have hπ := hasSubst_pr L.N0 L.N1 (K := ℂ_[L.l])
  set Pπ := (fun w : V1 L.N0 L.N1 => (MvPowerSeries.X w.2 : MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l])) with hPπ
  set Ψ := MvPowerSeries.subst (fun v : V1 L.N0 L.N1 =>
    MvPowerSeries.C ep0 * (MvPowerSeries.X v : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l])) L.Th with hΨ
  have h1 : L.Tht ep0 = MvPowerSeries.subst (Formalism.BasicNotions.jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1)) Ψ := by
    unfold product_zeroth_first_parts.Loc1.Tht
    rw [hΨ, MvPowerSeries.subst_comp_subst_apply (hasSubst_CX ep0) hlg]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hlg, MvPowerSeries.subst_C, MvPowerSeries.subst_X hlg]
  have hinv : ∀ F : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l],
      MvPowerSeries.subst G (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1)) F) = F := by
    intro F
    rw [MvPowerSeries.subst_comp_subst_apply hlg hGs]
    have : (fun v => MvPowerSeries.subst G (Formalism.BasicNotions.jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1) v)) =
        (MvPowerSeries.X : V1 L.N0 L.N1 → MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l]) := funext hG'
    rw [this, MvPowerSeries.subst_self]
    rfl
  have h2 := congrArg (MvPowerSeries.subst G) (h1.symm.trans hTh)
  rw [hinv, MvPowerSeries.subst_mul hGs, hinv] at h2

  set g : Fin L.N0 × Fin L.N1 → MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
    fun x => MvPowerSeries.subst Pπ (G (0, x)) with hgdef
  have hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0 := fun y =>
    MvPowerSeries.constantCoeff_subst_eq_zero hπ (fun w => MvPowerSeries.constantCoeff_X _) (hG0 _)
  have hgs : MvPowerSeries.HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg0
  have hgπ : (fun w : V1 L.N0 L.N1 => MvPowerSeries.subst g (Pπ w)) =
      fun w => MvPowerSeries.subst Pπ (G w) := by
    funext w
    have hw : ((0 : ZMod 1), w.2) = w := Prod.ext (Subsingleton.elim _ _) rfl
    show MvPowerSeries.subst g (MvPowerSeries.X w.2) = _
    rw [MvPowerSeries.subst_X hgs, hgdef]
    show MvPowerSeries.subst Pπ (G (0, w.2)) = _
    rw [hw]
  have hcomp : ∀ F : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l],
      MvPowerSeries.subst g (MvPowerSeries.subst Pπ F) = MvPowerSeries.subst Pπ (MvPowerSeries.subst G F) := by
    intro F
    rw [MvPowerSeries.subst_comp_subst_apply hπ hgs, MvPowerSeries.subst_comp_subst_apply hGs hπ, hgπ]
  refine ⟨g, MvPowerSeries.subst Pπ U, sg, ep, hep, hg0, ?_, integral_subst_pr L.N0 L.N1 hU, hsg, ?_⟩
  · intro x
    rw [← subst_pr_jetLogG L.l L.N0 L.N1 (0, x), hcomp, hG', MvPowerSeries.subst_X hπ]
  · have hL : MvPowerSeries.subst (fun v : ZMod 1 × Fin L.N0 × Fin L.N1 =>
        MvPowerSeries.C ep0 * (MvPowerSeries.X v.2 : MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l])) L.Th =
        MvPowerSeries.subst Pπ Ψ := by
      rw [hΨ, MvPowerSeries.subst_comp_subst_apply (hasSubst_CX ep0) hπ]
      congr 1
      funext v
      rw [MvPowerSeries.subst_mul hπ, MvPowerSeries.subst_C, MvPowerSeries.subst_X hπ]
    rw [hL, h2, MvPowerSeries.subst_mul hπ, OneGauss.thetaOne_eq, hcomp]
    congr 1
    have hE : ∀ a b, (MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (0, a, b) : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l])
        else MvPowerSeries.C ep * MvPowerSeries.X (0, a, b)) be) =
        MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : ℂ_[L.l]) else ep) •
          (fun x : Fin L.N0 × Fin L.N1 => (MvPowerSeries.X (0, x) : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l])) (a, b)) be := by
      intro a b
      congr 1
      funext s
      split_ifs
      · rw [one_smul]
      · rw [MvPowerSeries.smul_eq_C_mul]
    have hexpo : ((sg / 2) • ∑ a : Fin L.N0, ∑ b : Fin L.N1,
        MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (0, a, b) : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l])
        else MvPowerSeries.C ep * MvPowerSeries.X (0, a, b)) be) =
        OneGauss.expo (fun x : Fin L.N0 × Fin L.N1 => (MvPowerSeries.X (0, x) : MvPowerSeries (V1 L.N0 L.N1) ℂ_[L.l]))
          sg ep be := by
      unfold OneGauss.expo
      rw [Fintype.sum_prod_type]
      simp only [hE]
    show MvPowerSeries.subst Pπ (DworkPowerSeriesWeights.mvExp _) = _
    rw [hexpo, subst_mvExp hπ _ (OneGauss.cc_expo _ (fun x => MvPowerSeries.constantCoeff_X _) _ _ _ hbe),
      OneGauss.subst_expo hπ _ (fun x => MvPowerSeries.constantCoeff_X _)]
    congr 2
    funext x
    rw [MvPowerSeries.subst_X hπ]

section Apply

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime]

def psi : MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ →+*
    MvPolynomial (Lt × Fin N0 × Fin N1) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C).comp ((MvPolynomial.C).comp (Int.castRingHom ℂ_[l])))
    (Sum.elim (fun v => MvPolynomial.C (MvPolynomial.X v)) MvPolynomial.X)

theorem psi_monomial (μ : product_zeroth_first_parts.XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    psi N0 N1 l (MvPolynomial.monomial μ c) =
      MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).2
        (MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (c : ℂ_[l])) := by
  classical
  obtain ⟨ab, rfl⟩ : ∃ ab, Finsupp.sumFinsuppEquivProdFinsupp.symm ab = μ :=
    ⟨Finsupp.sumFinsuppEquivProdFinsupp μ, Equiv.symm_apply_apply _ _⟩
  rw [Equiv.apply_symm_apply]
  obtain ⟨a, b⟩ := ab
  have hμ : (Finsupp.sumFinsuppEquivProdFinsupp.symm (a, b) : product_zeroth_first_parts.XZ Lt N0 N1 →₀ ℕ) =
      Finsupp.sumElim a b := rfl
  rw [hμ]
  unfold psi
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod_sumElim]
  have ha : (a.prod fun v e => ((Sum.elim (fun v => MvPolynomial.C (MvPolynomial.X v))
      (MvPolynomial.X : Lt × Fin N0 × Fin N1 → MvPolynomial (Lt × Fin N0 × Fin N1)
        (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))) (Sum.inl v)) ^ e) =
      MvPolynomial.C (MvPolynomial.monomial a (1 : ℂ_[l])) := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    simp only [Sum.elim_inl, map_pow]
  have hb : (b.prod fun z e => ((Sum.elim (fun v => MvPolynomial.C (MvPolynomial.X v))
      (MvPolynomial.X : Lt × Fin N0 × Fin N1 → MvPolynomial (Lt × Fin N0 × Fin N1)
        (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))) (Sum.inr z)) ^ e) =
      MvPolynomial.monomial b 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
    simp only [Sum.elim_inr]
  simp only [Function.comp_def] at ha hb ⊢
  rw [ha, hb, ← mul_assoc, RingHom.comp_apply, RingHom.comp_apply, ← MvPolynomial.C_mul,
    MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.C_mul_monomial, mul_one]
  rfl

theorem applyAt0_eq_sum (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ) (S : Finset (product_zeroth_first_parts.XZ Lt N0 N1 →₀ ℕ)) (hS : P.support ⊆ S) :
    product_zeroth_first_parts.applyAt0 N0 N1 l Th P = ∑ μ ∈ S, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
      (((MvPolynomial.coeff μ P : ℤ) : ℂ_[l]) *
        ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
        MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th) := by
  unfold product_zeroth_first_parts.applyAt0
  refine Finset.sum_subset hS fun μ _ hμ => ?_
  rw [MvPolynomial.notMem_support_iff.mp hμ]
  simp

theorem applyAt0_eq_jet (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ) :
    product_zeroth_first_parts.applyAt0 N0 N1 l Th P = jetPairPoly (psi N0 N1 l P) Th := by
  classical
  refine MvPolynomial.induction_on' P (fun μ c => ?_) (fun p q hp hq => ?_)
  · rw [applyAt0_eq_sum N0 N1 l Th _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, psi_monomial, OrbMul.jetPairPoly_monomial,
      mul_comm (MvPolynomial.monomial _ (c : ℂ_[l])), MvPolynomial.C_mul_monomial]
    congr 1
    rw [DworkPowerSeriesWeights.mfact, Nat.cast_finsuppProd]
    ring
  · rw [map_add, OrbMul.jetPairPoly_add_left, ← hp, ← hq,
      applyAt0_eq_sum N0 N1 l Th (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      applyAt0_eq_sum N0 N1 l Th p (p.support ∪ q.support) Finset.subset_union_left,
      applyAt0_eq_sum N0 N1 l Th q (p.support ∪ q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.coeff_add, Int.cast_add, add_mul, add_mul, map_add]

end Apply

theorem jetPairPoly_map_rename {K : Type} [Field K] {σ τ ι : Type} (ρ : σ → τ)
    (P : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K) :
    jetPairPoly (MvPolynomial.map (MvPolynomial.rename ρ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K).toRingHom P) Th =
      MvPolynomial.rename ρ (jetPairPoly P Th) := by
  rw [OrbMul.jetPairPoly_eq_sum _ Th P.support (MvPolynomial.support_map_subset _ _)]
  unfold jetPairPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPolynomial.coeff_map, map_mul (MvPolynomial.rename ρ), MvPolynomial.rename_C]
  rfl

theorem isHomogeneous_det {S R : Type*} [CommRing R] {p : ℕ} (M : Matrix (Fin p) (Fin p) (MvPolynomial S R))
    (h : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous p := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp : (∏ i, M (σ i) i).IsHomogeneous p := by
    have := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1) (fun i _ => h _ _)
    simpa using this
  rw [Units.smul_def]
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp
    (zsmul_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hp) _)

theorem minorProd_hom {R : Type} [CommRing R] {σ : Type} {N0 N1 C : ℕ}
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (hrow : ∀ i b, (row i b).IsHomogeneous 1)
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    (minorProd row p hp I).IsHomogeneous (∑ c, p c) := by
  unfold minorProd
  exact MvPolynomial.IsHomogeneous.prod _ _ _ fun c _ => isHomogeneous_det _ fun r r' => hrow _ _

theorem coeff_subst_CX {σ : Type} [Finite σ] {K : Type} [CommRing K] (ep : K) (f : MvPowerSeries σ K)
    (κ : σ →₀ ℕ) :
    MvPowerSeries.coeff κ (MvPowerSeries.subst
      (fun v => MvPowerSeries.C ep * (MvPowerSeries.X v : MvPowerSeries σ K)) f) =
      ep ^ κ.degree * MvPowerSeries.coeff κ f := by
  have : (fun v => MvPowerSeries.C ep * (MvPowerSeries.X v : MvPowerSeries σ K)) =
      ((fun _ : σ => ep) : σ → K) • (MvPowerSeries.X : σ → MvPowerSeries σ K) := by
    funext v
    rw [Pi.smul_apply', MvPowerSeries.smul_eq_C_mul]
  rw [this, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale]
  congr 1
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem jetPairPoly_subst_CX {K : Type} [Field K] {σ ι : Type} [Finite ι]
    (P : MvPolynomial ι (MvPolynomial σ K)) (D : ℕ) (hP : P.IsHomogeneous D) (Th : MvPowerSeries ι K) (ep : K) :
    jetPairPoly P (MvPowerSeries.subst (fun v => MvPowerSeries.C ep * (MvPowerSeries.X v : MvPowerSeries ι K)) Th) =
      MvPolynomial.C (ep ^ D) * jetPairPoly P Th := by
  unfold jetPairPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  have hd : κ.degree = D := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hκ) (hP.coeff_eq_zero h)
  rw [coeff_subst_CX, hd, show ((DworkPowerSeriesWeights.mfact κ : ℕ) : K) * (ep ^ D * MvPowerSeries.coeff κ Th) =
    ep ^ D * (((DworkPowerSeriesWeights.mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) by ring, MvPolynomial.C_mul]
  ring

def frIdx {Lt : Type} {N0 : ℕ} : Lt × Fin N0 × Fin N0 → Lt × ℕ × Fin N0 := fun v => (v.1, (v.2.1 : ℕ), v.2.2)

theorem frIdx_injective {Lt : Type} {N0 : ℕ} : Function.Injective (frIdx (Lt := Lt) (N0 := N0)) := by
  intro a b h
  simp only [frIdx, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext (Fin.ext h.2.1) h.2.2)

theorem psi_Gxz (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d] (nu : ZMod d → YoungDiagram)
    (hp : ∀ s (c : Fin ((nu s).rowLen 0)), (nu s).colLen c ≤ N0) (I : product_zeroth_first_parts.ColChoice N1 nu) :
    psi N0 N1 l (product_zeroth_first_parts.Gxz N0 N1 nu I) =
      MvPolynomial.map (MvPolynomial.rename frIdx : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₐ[ℂ_[l]]
        MvPolynomial (ZMod d × ℕ × Fin N0) ℂ_[l]).toRingHom
        (∏ s : ZMod d, minorProd
          (fun (i : Fin N0) (b : Fin N1) =>
            (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
              MvPolynomial (ZV d N0 N1) (MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l])))
          (fun c : Fin ((nu s).rowLen 0) => (nu s).colLen c) (hp s) (fun c => ⇑(I s c))) := by
  classical
  unfold product_zeroth_first_parts.Gxz
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, ringMap_minorProd]
  unfold minorProd product_zeroth_first_parts.minorXZ
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext r r'
  simp [psi, frIdx, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.rename_X]

theorem tieFrame : TieFrame := by
  intro l _ d N0 N1 _ nu hp Th ep B hep hyp I m
  classical
  set Pop := ∏ s : ZMod d, minorProd
    (fun (i : Fin N0) (b : Fin N1) =>
      (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (ZV d N0 N1) (MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l])))
    (fun c : Fin ((nu s).rowLen 0) => (nu s).colLen c) (hp s) (fun c => ⇑(I s c)) with hPop
  have hhom : Pop.IsHomogeneous (∑ s : ZMod d, ∑ c : Fin ((nu s).rowLen 0), (nu s).colLen c) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => minorProd_hom _ (fun i b =>
      MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => MvPolynomial.isHomogeneous_C_mul_X _ _) _ _ _
  have hbound : ∀ n, ‖MvPolynomial.coeff n (jetPairPoly Pop Th)‖ ≤ (l : ℝ) ^ (-B) := by
    intro n
    have h := hyp (fun s c => ⇑(I s c)) n
    unfold frameJet at h
    rw [← hPop, jetPairPoly_subst_CX Pop _ hhom, MvPolynomial.coeff_C_mul, norm_mul, norm_pow, hep,
      one_pow, one_mul] at h
    exact h
  have heq : product_zeroth_first_parts.applyAt0 N0 N1 l Th (product_zeroth_first_parts.Gxz N0 N1 nu I) = MvPolynomial.rename frIdx (jetPairPoly Pop Th) := by
    rw [applyAt0_eq_jet, psi_Gxz, jetPairPoly_map_rename]
  rw [heq]
  exact OrbMul.norm_coeff_rename_le frIdx frIdx_injective _ hbound m

section One

variable (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime]

def psi1 : MvPolynomial (product_zeroth_first_parts.XZ (ZMod 1) N0 N1) ℤ →+*
    MvPolynomial (Fin N0 × Fin N1) (MvPolynomial (ZMod 1 × ℕ × Fin N0) ℂ_[l]) :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C).comp ((MvPolynomial.C).comp (Int.castRingHom ℂ_[l])))
    (Sum.elim (fun v => MvPolynomial.C (MvPolynomial.X v)) (fun z => MvPolynomial.X z.2))

theorem jet_map_monomial (μ : product_zeroth_first_parts.XZ (ZMod 1) N0 N1 →₀ ℕ) (c : ℤ) :
    psi1 N0 N1 l (MvPolynomial.monomial μ c) =
      MvPolynomial.monomial ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.embDomain (prEquiv N0 N1).toEmbedding)
        (MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (c : ℂ_[l])) := by
  classical
  obtain ⟨ab, rfl⟩ : ∃ ab, Finsupp.sumFinsuppEquivProdFinsupp.symm ab = μ :=
    ⟨Finsupp.sumFinsuppEquivProdFinsupp μ, Equiv.symm_apply_apply _ _⟩
  rw [Equiv.apply_symm_apply]
  obtain ⟨a, b⟩ := ab
  have hμ : (Finsupp.sumFinsuppEquivProdFinsupp.symm (a, b) : product_zeroth_first_parts.XZ (ZMod 1) N0 N1 →₀ ℕ) =
      Finsupp.sumElim a b := rfl
  rw [hμ]
  unfold psi1
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod_sumElim]
  have ha : (a.prod fun v e => ((Sum.elim (fun v => MvPolynomial.C (MvPolynomial.X v))
      (fun z : ZMod 1 × Fin N0 × Fin N1 => (MvPolynomial.X z.2 : MvPolynomial (Fin N0 × Fin N1)
        (MvPolynomial (ZMod 1 × ℕ × Fin N0) ℂ_[l])))) (Sum.inl v)) ^ e) =
      MvPolynomial.C (MvPolynomial.monomial a (1 : ℂ_[l])) := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    simp only [Sum.elim_inl, map_pow]
  have hb : (b.prod fun z e => ((Sum.elim (fun v => MvPolynomial.C (MvPolynomial.X v))
      (fun z : ZMod 1 × Fin N0 × Fin N1 => (MvPolynomial.X z.2 : MvPolynomial (Fin N0 × Fin N1)
        (MvPolynomial (ZMod 1 × ℕ × Fin N0) ℂ_[l])))) (Sum.inr z)) ^ e) =
      MvPolynomial.monomial (b.embDomain (prEquiv N0 N1).toEmbedding) 1 := by
    rw [Finsupp.embDomain_eq_mapDomain, ← MvPolynomial.rename_monomial, MvPolynomial.monomial_eq,
      MvPolynomial.C_1, one_mul, map_finsuppProd]
    simp only [Sum.elim_inr, map_pow, MvPolynomial.rename_X]
    rfl
  simp only [Function.comp_def] at ha hb ⊢
  rw [ha, hb, ← mul_assoc, RingHom.comp_apply, RingHom.comp_apply, ← MvPolynomial.C_mul,
    MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.C_mul_monomial, mul_one]
  rfl

theorem apply_at_zero_eq_jet_pair (Th : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (product_zeroth_first_parts.XZ (ZMod 1) N0 N1) ℤ) :
    product_zeroth_first_parts.applyAt0 N0 N1 l Th P = jetPairPoly (psi1 N0 N1 l P)
      (MvPowerSeries.subst (fun w : V1 N0 N1 => (MvPowerSeries.X w.2 : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) Th) := by
  classical
  rw [subst_pr_eq_rename]
  refine MvPolynomial.induction_on' P (fun μ c => ?_) (fun p q hp hq => ?_)
  · rw [applyAt0_eq_sum N0 N1 l Th _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, jet_map_monomial, OrbMul.jetPairPoly_monomial,
      mul_comm (MvPolynomial.monomial _ (c : ℂ_[l])), MvPolynomial.C_mul_monomial,
      MvPowerSeries.coeff_embDomain_rename]
    congr 1
    rw [DworkPowerSeriesWeights.mfact, Finsupp.prod_embDomain, Nat.cast_finsuppProd]
    ring
  · rw [map_add, OrbMul.jetPairPoly_add_left, ← hp, ← hq,
      applyAt0_eq_sum N0 N1 l Th (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      applyAt0_eq_sum N0 N1 l Th p (p.support ∪ q.support) Finset.subset_union_left,
      applyAt0_eq_sum N0 N1 l Th q (p.support ∪ q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.coeff_add, Int.cast_add, add_mul, add_mul, map_add]

def frIdx1 : Fin N0 × Fin N0 → ZMod 1 × ℕ × Fin N0 := fun v => (default, (v.1 : ℕ), v.2)

theorem frIdx1_injective : Function.Injective (frIdx1 N0) := by
  intro a b h
  simp only [frIdx1, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.2.1) h.2.2

theorem jet_map_minor_product (nu : YoungDiagram) (hp : ∀ c : Fin (nu.rowLen 0), nu.colLen c ≤ N0)
    (I : product_zeroth_first_parts.ColChoice N1 (fun _ : ZMod 1 => nu)) :
    psi1 N0 N1 l (product_zeroth_first_parts.Gxz N0 N1 (fun _ : ZMod 1 => nu) I) =
      MvPolynomial.map (MvPolynomial.rename (frIdx1 N0) : MvPolynomial (Fin N0 × Fin N0) ℂ_[l] →ₐ[ℂ_[l]]
        MvPolynomial (ZMod 1 × ℕ × Fin N0) ℂ_[l]).toRingHom
        (minorProd (fun (i : Fin N0) (b : Fin N1) =>
            (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (i, a)) * MvPolynomial.X (a, b) :
              MvPolynomial (Fin N0 × Fin N1) (MvPolynomial (Fin N0 × Fin N0) ℂ_[l])))
          (fun c : Fin (nu.rowLen 0) => nu.colLen c) hp (fun c => ⇑(I default c))) := by
  classical
  unfold product_zeroth_first_parts.Gxz
  rw [Fintype.prod_unique, map_prod, ringMap_minorProd]
  unfold minorProd product_zeroth_first_parts.minorXZ
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext r r'
  simp [psi1, frIdx1, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.rename_X]
  all_goals rfl

end One

theorem tieFrameOne : TieFrameOne := by
  intro l _ N0 N1 nu hp Th ep0 B hep hyp I m
  classical
  set Pop := minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (i, a)) * MvPolynomial.X (a, b) :
        MvPolynomial (Fin N0 × Fin N1) (MvPolynomial (Fin N0 × Fin N0) ℂ_[l])))
    (fun c : Fin (nu.rowLen 0) => nu.colLen c) hp (fun c => ⇑(I default c)) with hPop
  have hhom : Pop.IsHomogeneous (∑ c : Fin (nu.rowLen 0), nu.colLen c) :=
    minorProd_hom _ (fun i b =>
      MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => MvPolynomial.isHomogeneous_C_mul_X _ _) _ _ _
  have hπ := hasSubst_pr N0 N1 (K := ℂ_[l])
  set ThF := MvPowerSeries.subst (fun w : V1 N0 N1 =>
    (MvPowerSeries.X w.2 : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) Th with hThF
  have hcomp : MvPowerSeries.subst (fun v : ZMod 1 × Fin N0 × Fin N1 =>
      MvPowerSeries.C ep0 * (MvPowerSeries.X v.2 : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) Th =
      MvPowerSeries.subst (fun x => MvPowerSeries.C ep0 *
        (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) ThF := by
    rw [hThF, MvPowerSeries.subst_comp_subst_apply hπ (hasSubst_CX ep0)]
    congr 1
    funext v
    rw [MvPowerSeries.subst_X (hasSubst_CX ep0)]
  have hbound : ∀ n, ‖MvPolynomial.coeff n (jetPairPoly Pop ThF)‖ ≤ (l : ℝ) ^ (-B) := by
    intro n
    have h := hyp (fun c => ⇑(I default c)) n
    unfold frameJetOne at h
    rw [← hPop, hcomp, jetPairPoly_subst_CX Pop _ hhom, MvPolynomial.coeff_C_mul, norm_mul, norm_pow, hep,
      one_pow, one_mul] at h
    exact h
  have heq : product_zeroth_first_parts.applyAt0 N0 N1 l Th (product_zeroth_first_parts.Gxz N0 N1 (fun _ : ZMod 1 => nu) I) =
      MvPolynomial.rename (frIdx1 N0) (jetPairPoly Pop ThF) := by
    rw [apply_at_zero_eq_jet_pair, jet_map_minor_product, jetPairPoly_map_rename]
  rw [heq]
  exact OrbMul.norm_coeff_rename_le (frIdx1 N0) (frIdx1_injective N0) _ hbound m

theorem kernel_twist_one_letter_holds : KernelFromTwistOneLetter := kernel_twist_one_letter_vanishing

section Unr

variable (l : ℕ) [Fact l.Prime]

def iZ : ℤ_[l] →+* ℂ_[l] := (algebraMap ℚ_[l] ℂ_[l]).comp (PadicInt.Coe.ringHom)

def muN (N : ℕ) : Set ℂ_[l] := {w | w ^ N = 1}

def RN (N : ℕ) : Subring ℂ_[l] := Subring.closure (muN l N ∪ Set.range (iZ l))

theorem iZ_apply (a : ℤ_[l]) : iZ l a = algebraMap ℚ_[l] ℂ_[l] (a : ℚ_[l]) := rfl

theorem norm_iZ (a : ℤ_[l]) : ‖iZ l a‖ = ‖a‖ := by
  rw [iZ_apply, norm_algebraMap', PadicInt.norm_def]

theorem muN_sub_RN (N : ℕ) : muN l N ⊆ RN l N := fun w hw => Subring.subset_closure (Or.inl hw)

theorem iZ_mem_RN (N : ℕ) (a : ℤ_[l]) : iZ l a ∈ RN l N := Subring.subset_closure (Or.inr ⟨a, rfl⟩)

theorem norm_le_one_of_mem_RN {N : ℕ} (hN : 0 < N) {z : ℂ_[l]} (hz : z ∈ RN l N) : ‖z‖ ≤ 1 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨a, rfl⟩
    · have hx' : x ^ N = 1 := hx
      have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx', norm_one]
      exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').mp h)
    · rw [norm_iZ]; exact a.norm_le_one
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => rwa [norm_neg]
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem frob_RN {N : ℕ} (hcop : Nat.Coprime l N) (hl2 : l ≠ 2) {z : ℂ_[l]} (hz : z ∈ RN l N) :
    ∃ r ∈ RN l N, z ^ (l ^ Nat.totient N) - z = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have hq1 : l ^ Nat.totient N ≡ 1 [MOD N] := Nat.ModEq.pow_totient hcop
  have hq0 : l ^ Nat.totient N ≠ 0 := pow_ne_zero _ hp.ne_zero
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨a, rfl⟩
    · refine ⟨0, zero_mem _, ?_⟩
      have hx' : x ^ N = 1 := hx
      obtain ⟨t, ht⟩ : N ∣ l ^ Nat.totient N - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hq1.symm
      have h1 := Nat.one_le_pow (Nat.totient N) l hp.pos
      have : l ^ Nat.totient N = N * t + 1 := by omega
      rw [mul_zero, sub_eq_zero, this, pow_succ, pow_mul, hx', one_pow, one_mul]
    · have h0 : PadicInt.toZMod (a ^ (l ^ Nat.totient N) - a) = 0 := by
        rw [map_sub, map_pow, ZMod.pow_card_pow, sub_self]
      have hmem : a ^ (l ^ Nat.totient N) - a ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
        rw [← PadicInt.ker_toZMod]; exact h0
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
      obtain ⟨r, hr⟩ := hmem
      refine ⟨iZ l r, iZ_mem_RN l N r, ?_⟩
      rw [← map_pow, ← map_sub, ← hr, map_mul, map_natCast, mul_comm]
  | zero => exact ⟨0, zero_mem _, by simp [zero_pow hq0]⟩
  | one => exact ⟨0, zero_mem _, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨r1, hr1, e1⟩ := ihx
    obtain ⟨r2, hr2, e2⟩ := ihy
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨x, hx⟩ : RN l N) ⟨y, hy⟩ (Nat.totient N)
    have hr' := congrArg Subtype.val hr
    push_cast at hr'
    refine ⟨x * y * r + r1 + r2, add_mem (add_mem (mul_mem (mul_mem hx hy) r.2) hr1) hr2, ?_⟩
    rw [hr']
    linear_combination e1 + e2
  | neg x hx ih =>
    obtain ⟨r, hr, e⟩ := ih
    refine ⟨-r, neg_mem hr, ?_⟩
    have hodd : Odd (l ^ Nat.totient N) := (hp.odd_of_ne_two hl2).pow
    rw [hodd.neg_pow]
    linear_combination -e
  | mul x y hx hy ihx ihy =>
    obtain ⟨r1, hr1, e1⟩ := ihx
    obtain ⟨r2, hr2, e2⟩ := ihy
    refine ⟨x ^ (l ^ Nat.totient N) * r2 + r1 * y,
      add_mem (mul_mem (pow_mem hx _) hr2) (mul_mem hr1 hy), ?_⟩
    rw [mul_pow]
    linear_combination x ^ (l ^ Nat.totient N) * e2 + y * e1

theorem muN_finite {N : ℕ} (hN : 0 < N) : (muN l N).Finite := by
  classical
  refine (Polynomial.nthRoots N (1 : ℂ_[l])).toFinset.finite_toSet.subset fun w hw => ?_
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_nthRoots hN).mpr hw

theorem RN_sub_span {N : ℕ} {z : ℂ_[l]} (hz : z ∈ RN l N) :
    z ∈ Submodule.span ℚ_[l] (muN l N) := by
  have h1 : (1 : ℂ_[l]) ∈ Submodule.span ℚ_[l] (muN l N) :=
    Submodule.subset_span (show (1 : ℂ_[l]) ^ N = 1 from one_pow N)
  have hmul : ∀ x y, x ∈ Submodule.span ℚ_[l] (muN l N) → y ∈ Submodule.span ℚ_[l] (muN l N) →
      x * y ∈ Submodule.span ℚ_[l] (muN l N) := by
    intro x y hx hy
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨a, ha, b, hb, rfl⟩
    show (a * b) ^ N = 1
    rw [mul_pow, show a ^ N = 1 from ha, show b ^ N = 1 from hb, one_mul]
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨a, rfl⟩
    · exact Submodule.subset_span hx
    · rw [iZ_apply, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ h1
  | zero => exact zero_mem _
  | one => exact h1
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem open_RN {N : ℕ} (hN : 0 < N) :
    ∃ δ > (0 : ℝ), ∀ z ∈ RN l N, ‖z‖ < δ → ∃ r ∈ RN l N, z = (l : ℂ_[l]) * r := by
  classical
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℚ_[l] (muN l N)
  let _ : Fintype b := ((muN_finite l hN).subset hbs).fintype
  let f : (b → ℚ_[l]) →ₗ[ℚ_[l]] ℂ_[l] :=
    { toFun := fun c => ∑ j, c j • (j : ℂ_[l])
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.mp hli c hc j
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith f hker
  refine ⟨1 / K, by positivity, fun z hz hzn => ?_⟩
  have hzb : z ∈ Submodule.span ℚ_[l] (Set.range (Subtype.val : b → ℂ_[l])) := by
    rw [Subtype.range_coe, hbspan]; exact RN_sub_span l hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).mp hzb
  have hfc : f c = z := hc
  have hcn : ‖c‖ < 1 := by
    have h := hanti.le_mul_dist c 0
    rw [dist_zero_right, map_zero, dist_zero_right, hfc] at h
    calc ‖c‖ ≤ K * ‖z‖ := h
      _ < K * (1 / K) := mul_lt_mul_of_pos_left hzn (by exact_mod_cast hK)
      _ = 1 := by field_simp
  have hcj : ∀ j, ∃ u : ℤ_[l], (c j : ℚ_[l]) = (l : ℚ_[l]) * (u : ℚ_[l]) := by
    intro j
    have hj : ‖c j‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm c j) hcn
    let a : ℤ_[l] := ⟨c j, hj.le⟩
    have ha : ‖a‖ < 1 := by rw [PadicInt.norm_def]; exact hj
    obtain ⟨u, hu⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp ha
    refine ⟨u, ?_⟩
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) hu
    simpa using this
  choose u hu using hcj
  refine ⟨∑ j, iZ l (u j) * (j : ℂ_[l]),
    sum_mem fun j _ => mul_mem (iZ_mem_RN l N _) (muN_sub_RN l N (hbs j.2)), ?_⟩
  rw [← hfc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, hu j, map_mul, map_natCast, iZ_apply, mul_assoc]

theorem dvd_of_norm_lt_one {N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime l N) (hl2 : l ≠ 2) {z : ℂ_[l]}
    (hz : z ∈ RN l N) (hz1 : ‖z‖ < 1) : ∃ r ∈ RN l N, z = (l : ℂ_[l]) * r := by
  obtain ⟨δ, hδ, hopen⟩ := open_RN l hN
  have hl : (l : ℂ_[l]) ∈ RN l N := natCast_mem _ _

  have hit : ∀ m : ℕ, ∃ s ∈ RN l N, z = z ^ ((l ^ Nat.totient N) ^ m) - (l : ℂ_[l]) * s := by
    intro m
    induction m with
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨s, hs, e⟩ := ih
      obtain ⟨r, hr, er⟩ := frob_RN l hcop hl2 (pow_mem hz ((l ^ Nat.totient N) ^ m))
      refine ⟨s + r, add_mem hs hr, ?_⟩
      rw [pow_succ, pow_mul]
      linear_combination e - er
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hz1
  obtain ⟨s, hs, e⟩ := hit n
  have hq2 : 2 ≤ l ^ Nat.totient N :=
    le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow (Nat.totient_pos.mpr hN).ne' l)
  have hle : n ≤ (l ^ Nat.totient N) ^ n := (Nat.lt_pow_self (by omega)).le
  have hsmall : ‖z ^ ((l ^ Nat.totient N) ^ n)‖ < δ := by
    rw [norm_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hle) hn
  obtain ⟨r', hr', er'⟩ := hopen _ (pow_mem hz _) hsmall
  exact ⟨r' - s, sub_mem hr' hs, by rw [e, er']; ring⟩

theorem norm_RN {N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime l N) (hl2 : l ≠ 2) {z : ℂ_[l]}
    (hz : z ∈ RN l N) (hz0 : z ≠ 0) : ∃ k : ℕ, ‖z‖ = ‖(l : ℂ_[l])‖ ^ k := by
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_l]; exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
  have key : ∀ n : ℕ, ∀ z ∈ RN l N, ‖(l : ℂ_[l])‖ ^ n < ‖z‖ → ∃ k : ℕ, ‖z‖ = ‖(l : ℂ_[l])‖ ^ k := by
    intro n
    induction n with
    | zero =>
      intro z hz h
      exact absurd (norm_le_one_of_mem_RN l hN hz) (by rw [pow_zero] at h; exact not_le.mpr h)
    | succ n ih =>
      intro z hz h
      rcases eq_or_lt_of_le (norm_le_one_of_mem_RN l hN hz) with h1 | h1
      · exact ⟨0, by rw [h1, pow_zero]⟩
      · obtain ⟨r, hr, rfl⟩ := dvd_of_norm_lt_one l hN hcop hl2 hz h1
        rw [norm_mul, pow_succ, mul_comm (‖(l : ℂ_[l])‖ ^ n)] at h
        obtain ⟨k, hk⟩ := ih r hr (lt_of_mul_lt_mul_left h hl0.le)
        exact ⟨k + 1, by rw [norm_mul, hk, pow_succ, mul_comm]⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hz0) hl1
  exact key n z hz hn

end Unr

section Unr2

variable (l : ℕ) [Fact l.Prime]

theorem RN_mono {N M : ℕ} (h : N ∣ M) : RN l N ≤ RN l M := by
  refine Subring.closure_mono (Set.union_subset_union_left _ fun w hw => ?_)
  obtain ⟨t, rfl⟩ := h
  show w ^ (N * t) = 1
  rw [pow_mul, show w ^ N = 1 from hw, one_pow]

theorem adjoin_RN {y : ℂ_[l]} (hy : y ∈ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)) :
    ∃ N : ℕ, 0 < N ∧ Nat.Coprime l N ∧ ∃ K : ℕ, (l : ℂ_[l]) ^ K * y ∈ RN l N := by
  have hp : l.Prime := Fact.out
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, hn, hcop, hxn⟩ := hx
    exact ⟨n, hn, hcop.symm, 0, by rw [pow_zero, one_mul]; exact muN_sub_RN l n hxn⟩
  | algebraMap r =>
    refine ⟨1, one_pos, Nat.coprime_one_right _, ?_⟩
    have hl1 : ‖(l : ℚ_[l])‖ < 1 := by
      rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖r‖ + 1) by positivity) hl1
    have hnorm : ‖(l : ℚ_[l]) ^ K * r‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      have h0 : 0 ≤ ‖r‖ := norm_nonneg _
      calc ‖(l : ℚ_[l])‖ ^ K * ‖r‖ ≤ 1 / (‖r‖ + 1) * ‖r‖ :=
            mul_le_mul_of_nonneg_right hK.le h0
        _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    refine ⟨K, ?_⟩
    have : (l : ℂ_[l]) ^ K * algebraMap ℚ_[l] ℂ_[l] r = iZ l (⟨(l : ℚ_[l]) ^ K * r, hnorm⟩ : ℤ_[l]) := by
      show _ = algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ K * r)
      rw [map_mul, map_pow, map_natCast]
    rw [this]
    exact iZ_mem_RN l 1 _
  | add x y _ _ hx hy =>
    obtain ⟨N1, hN1, hc1, K1, h1⟩ := hx
    obtain ⟨N2, hN2, hc2, K2, h2⟩ := hy
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, Nat.Coprime.mul_right hc1 hc2, K1 + K2, ?_⟩
    have hl : (l : ℂ_[l]) ∈ RN l (N1 * N2) := natCast_mem _ _
    have e : (l : ℂ_[l]) ^ (K1 + K2) * (x + y) =
        (l : ℂ_[l]) ^ K2 * ((l : ℂ_[l]) ^ K1 * x) + (l : ℂ_[l]) ^ K1 * ((l : ℂ_[l]) ^ K2 * y) := by ring
    rw [e]
    exact add_mem (mul_mem (pow_mem hl _) (RN_mono l (dvd_mul_right N1 N2) h1))
      (mul_mem (pow_mem hl _) (RN_mono l (dvd_mul_left N2 N1) h2))
  | mul x y _ _ hx hy =>
    obtain ⟨N1, hN1, hc1, K1, h1⟩ := hx
    obtain ⟨N2, hN2, hc2, K2, h2⟩ := hy
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, Nat.Coprime.mul_right hc1 hc2, K1 + K2, ?_⟩
    have e : (l : ℂ_[l]) ^ (K1 + K2) * (x * y) = ((l : ℂ_[l]) ^ K1 * x) * ((l : ℂ_[l]) ^ K2 * y) := by ring
    rw [e]
    exact mul_mem (RN_mono l (dvd_mul_right N1 N2) h1) (RN_mono l (dvd_mul_left N2 N1) h2)

theorem norm_l_ne_zero : ‖(l : ℂ_[l])‖ ≠ 0 := by
  rw [norm_l]; exact inv_ne_zero (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

theorem norm_adjoin (hl2 : l ≠ 2) {y : ℂ_[l]} (hy : y ∈ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l))
    (hy0 : y ≠ 0) : ∃ k : ℤ, ‖y‖ = ‖(l : ℂ_[l])‖ ^ k := by
  obtain ⟨N, hN, hcop, K, hK⟩ := adjoin_RN l hy
  have hl0 : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨k, hk⟩ := norm_RN l hN hcop hl2 hK (mul_ne_zero (pow_ne_zero _ hl0) hy0)
  refine ⟨(k : ℤ) - K, ?_⟩
  rw [norm_mul, norm_pow] at hk
  rw [zpow_sub₀ (norm_l_ne_zero l), zpow_natCast, zpow_natCast, ← hk]
  field_simp [pow_ne_zero K (norm_l_ne_zero l)]

theorem norm_Wfrac (hl2 : l ≠ 2) {x : ℂ_[l]} (hx : x ∈ product_zeroth_first_parts.Wfrac l) (hx0 : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = ‖(l : ℂ_[l])‖ ^ k := by
  have hx' : x ∈ closure (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := by
    rw [← Subalgebra.topologicalClosure_coe]; exact hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx' ‖x‖ hpos
  rw [dist_eq_norm] at hxy
  have h1 : ‖y‖ ≤ ‖x‖ := by
    have := IsUltrametricDist.norm_add_le_max x (y - x)
    rw [add_sub_cancel, norm_sub_rev] at this
    exact this.trans (max_le le_rfl hxy.le)
  have h2 : ‖x‖ ≤ ‖y‖ := by
    have := IsUltrametricDist.norm_add_le_max y (x - y)
    rw [add_sub_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hxy)
  have hyx : ‖y‖ = ‖x‖ := le_antisymm h1 h2
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hyx; exact hpos.ne hyx
  obtain ⟨k, hk⟩ := norm_adjoin l hl2 hy hy0
  exact ⟨k, by rw [← hyx, hk]⟩

theorem wfrac_unram (hl2 : l ≠ 2) : ∃ K0 : Subfield ℂ_[l], (∀ x ∈ product_zeroth_first_parts.Wfrac l, x ∈ K0) ∧ Unram l K0 := by
  refine ⟨Subfield.closure (product_zeroth_first_parts.Wfrac l : Set ℂ_[l]), fun x hx => Subfield.subset_closure hx, ?_⟩
  intro a ha ha0
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp ha
  have hS : Subring.closure (product_zeroth_first_parts.Wfrac l : Set ℂ_[l]) = (product_zeroth_first_parts.Wfrac l).toSubring :=
    Subring.closure_eq (product_zeroth_first_parts.Wfrac l).toSubring
  rw [hS] at hy hz
  have hz0 : z ≠ 0 := by rintro rfl; exact ha0 (div_zero y)
  have hy0 : y ≠ 0 := by rintro rfl; exact ha0 (zero_div z)
  obtain ⟨k1, hk1⟩ := norm_Wfrac l hl2 hy hy0
  obtain ⟨k2, hk2⟩ := norm_Wfrac l hl2 hz hz0
  exact ⟨k1 - k2, by rw [norm_div, hk1, hk2, zpow_sub₀ (norm_l_ne_zero l)]⟩

end Unr2

end Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel
