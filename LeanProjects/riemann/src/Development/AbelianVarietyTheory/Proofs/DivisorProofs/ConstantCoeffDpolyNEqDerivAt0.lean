import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0EqSumOfSubset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpCoord

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (pderiv_subst)

section Deriv

variable {C : Type} [Field C] {σ : Type}

theorem mfact_eq_prod [Fintype σ] (α : σ →₀ ℕ) : (mfact α : C) = ∏ s, ((α s).factorial : C) := by
  first
  | exact Finsupp.prod_fintype α _ (fun _ => by simp)
  | (unfold mfact; rw [Finsupp.prod_fintype]; intro; simp)

theorem mfact_add_single [Fintype σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : C) = mfact α * ((α l : C) + 1) := by
  classical
  first
  | (have h : ∀ s, (((α + Finsupp.single l 1 : σ →₀ ℕ) s).factorial : C) =
        ((α s).factorial : C) * (if s = l then ((α l : C) + 1) else 1) := by
      intro s
      by_cases hs : s = l
      · rw [if_pos hs]
        subst hs
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hs, mul_one]
        simp [Finsupp.single_apply, Ne.symm hs]
     rw [mfact_eq_prod, mfact_eq_prod, Finset.prod_congr rfl (fun s _ => h s), Finset.prod_mul_distrib]
     simp
     done)

theorem derivAt0_monomial (α : σ →₀ ℕ) (a : C) (S : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.monomial α a) S = a * mfact α * coeff α S := by
  classical
  first
  | (rw [derivAt0_eq_sum_of_subset _ _ MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]; done)
  | (by_cases ha : a = 0 <;> simp [derivAt0, ha, MvPolynomial.support_monomial]; done)

private lemma hasSubst_lemma {ι τ : Type} [Finite ι] {a : ι → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha]; exact IsNilpotent.zero)

private lemma cc_subst_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    constantCoeff (subst a f) = 0 := by
  first
  | exact constantCoeff_subst_eq_zero (hasSubst_lemma ha) ha hf
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_lemma ha) ha hf
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_lemma ha) hf

private lemma subst_zero_lemma_3 {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ C) = 0 := by
  first
  | (rw [← MvPowerSeries.coe_substAlgHom ha]; exact map_zero _)
  | simp

private lemma subst_C_eq_C' {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (r : C) :
    subst a (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
  first
  | (rw [← MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes,
      MvPowerSeries.c_eq_algebraMap])
  | (rw [← MvPowerSeries.coe_substAlgHom ha]; exact AlgHom.commutes _ r)
  | simp [ha]

private lemma subst_subst_eq_subst_comp {σ τ ρ : Type} {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ C) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f := by
  first
  | exact MvPowerSeries.subst_comp_subst_apply ha hb f
  | exact (MvPowerSeries.subst_comp_subst_apply ha hb f).symm
  | exact congrFun (MvPowerSeries.subst_comp_subst ha hb) f

private lemma pderiv_inr_subst_twoVars {d : ℕ} (f : MvPowerSeries (Fin 2 × Fin d) C) (k : Fin d) :
    pderiv C (Sum.inr k) (subst (GlobalTheory.LawLog.twoVars C d) f) =
      subst (GlobalTheory.LawLog.twoVars C d) (pderiv C ((1 : Fin 2), k) f) := by
  classical
  rw [pderiv_subst GlobalTheory.LawLog.cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply]
  · rintro ⟨a, i⟩ _ hs
    fin_cases a
    · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply]
    · have hik : i ≠ k := fun h => hs (by subst h; rfl)
      simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply, hik]
  · simp

variable [CharZero C] (v : AddValuation C (WithTop ℝ))
include v

theorem derivAt0_pderiv [Fintype σ] (Q : MvPolynomial σ C) (l : σ) (S : MvPowerSeries σ C) :
    derivAt0 Q (pderiv C l S) = derivAt0 (Q * MvPolynomial.X l) S := by
  classical
  first
  | (unfold derivAt0
     rw [MvPolynomial.support_mul_X, Finset.sum_map]
     refine Finset.sum_congr rfl fun α _ => ?_
     simp only [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, mfact_add_single]
     first
     | (rw [MvPowerSeries.coeff_pderiv]; ring)
     | (simp [MvPowerSeries.coeff_pderiv]; ring)
     | (simp [MvPowerSeries.coeff_pderiv])
     done)

end Deriv

section Chain

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem subst_jacEntry (G : FGLaw C d) (L : LogFGL v d)
    (hL : ∀ a, L.F a = subst (twoVars C d) (G.F a)) {n : ℕ} {Λ : Type} [Finite Λ]
    (ψ : Fin n × Fin d → MvPowerSeries Λ C) (hψ : ∀ q, constantCoeff (ψ q) = 0) (j : Fin n) (k e : Fin d) :
    subst (fun i => ψ (j, i)) (GlobalTheory.LogJacobian.jacEntry L k e) =
      subst ψ (ev (n := n) ![pt C d j, 0] (pderiv C ((1 : Fin 2), k) (G.F e))) := by
  classical
  have hA : HasSubst (GlobalTheory.LogJacobian.substSecondBlockZero (C := C) d) := hasSubst_lemma (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d)
  have hT : HasSubst (GlobalTheory.LawLog.twoVars C d) := hasSubst_lemma GlobalTheory.LawLog.cc_twoVars
  have hB : HasSubst (fun i => ψ (j, i)) := hasSubst_lemma (fun i => hψ (j, i))
  have hΨ : HasSubst ψ := hasSubst_lemma hψ
  have hAT : HasSubst (fun s => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := C) d) (GlobalTheory.LawLog.twoVars C d s)) :=
    hasSubst_lemma (fun s => cc_subst_lemma_2 (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (GlobalTheory.LawLog.cc_twoVars s))
  have hP : HasSubst (fun p : Fin 2 × Fin d => (![fun i => X (j, i), 0] : Fin 2 → Fin d → MvPowerSeries (Fin n × Fin d) C) p.1 p.2) := by
    refine hasSubst_lemma (fun p => ?_)
    rcases p with ⟨a, i⟩
    fin_cases a <;> simp
  unfold GlobalTheory.LogJacobian.jacEntry ev pt
  rw [hL e, pderiv_inr_subst_twoVars, subst_subst_eq_subst_comp hT hA, subst_subst_eq_subst_comp hAT hB, subst_subst_eq_subst_comp hP hΨ]
  congr 1
  funext p
  rcases p with ⟨a, i⟩
  fin_cases a
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.subst_X hA, MvPowerSeries.subst_X hΨ]
    all_goals simp [GlobalTheory.LogJacobian.substSecondBlockZero, MvPowerSeries.subst_X hB]
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.subst_X hA, MvPowerSeries.subst_X hΨ, subst_zero_lemma_3 hΨ]
    all_goals simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_zero_lemma_3 hB]

variable (L : LogFGL v d) {n : ℕ} {Λ : Type} [Fintype Λ] (β : Λ → Fin n → C) (w : Λ → Fin d → C)

def lin (j : Fin n) : Fin d → MvPowerSeries Λ C :=
  fun e => ∑ l, (β l j * w l e) • (X l : MvPowerSeries Λ C)

def psi : Fin n × Fin d → MvPowerSeries Λ C :=
  fun q => subst (lin β w q.1) (expOf L q.2)

theorem cc_lin (j : Fin n) (e : Fin d) : constantCoeff (lin β w j e) = 0 := by
  first
  | (simp [lin, MvPowerSeries.smul_eq_C_mul]; done)
  | (unfold lin
     rw [map_sum]
     refine Finset.sum_eq_zero fun l _ => ?_
     rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])

theorem cc_psi (q : Fin n × Fin d) : constantCoeff (psi L β w q) = 0 := by
  have hs : MvPowerSeries.HasSubst (lin β w q.1) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (cc_lin β w q.1)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_lin β w q.1)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [cc_lin]; exact IsNilpotent.zero)
  first
  | exact constantCoeff_subst_eq_zero hs (cc_lin β w q.1) ((isExp_expOf L).1 q.2)
  | exact MvPowerSeries.constantCoeff_subst_eq_zero hs (cc_lin β w q.1) ((isExp_expOf L).1 q.2)
  | exact MvPowerSeries.constantCoeff_subst_eq_zero hs ((isExp_expOf L).1 q.2)

theorem pderiv_lin (l : Λ) (j : Fin n) (e : Fin d) :
    pderiv C l (lin β w j e) = MvPowerSeries.C (β l j * w l e) := by
  classical
  first
  | (simp only [lin, map_sum, Derivation.map_smul, MvPowerSeries.pderiv_X]
     simp [Pi.single_apply, MvPowerSeries.smul_eq_C_mul]
     done)
  | (simp [lin, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]; done)

theorem pderiv_subst_psi (G : FGLaw C d) (hL : ∀ a, L.F a = subst (twoVars C d) (G.F a)) (l : Λ) (g : PS C n d) :
    pderiv C l (subst (psi L β w) g) =
      subst (psi L β w) (∑ j, MvPowerSeries.C (β l j) * DofN G.F j (w l) g) := by
  classical
  have hΨ : HasSubst (psi L β w) := hasSubst_lemma (cc_psi L β w)
  have hpt : ∀ (j : Fin n) (i : Fin d), constantCoeff (pt C d j i) = 0 := fun j i => by simp [pt]
  have hcol : ∀ (j : Fin n) (c : Fin d), pderiv C l (psi L β w (j, c)) =
      ∑ e, subst (psi L β w) (ev ![pt C d j, 0] (pderiv C ((1 : Fin 2), e) (G.F c))) *
        MvPowerSeries.C (β l j * w l e) := by
    intro j c
    have hlin : HasSubst (lin β w j) := hasSubst_lemma (cc_lin β w j)
    have hE : HasSubst (expOf L) := hasSubst_lemma (isExp_expOf L).1
    show pderiv C l (subst (lin β w j) (expOf L c)) = _
    rw [pderiv_subst (cc_lin β w j)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [pderiv_lin, GlobalTheory.LogJacobian.pderiv_expOf, subst_subst_eq_subst_comp hE hlin]
    congr 1
    exact subst_jacEntry G L hL (psi L β w) (cc_psi L β w) j e c
  rw [pderiv_subst (cc_psi L β w), Fintype.sum_prod_type]
  simp only [hcol]
  simp only [GlobalTheory.MatChain.dofN_eq G, GlobalTheory.MatChain.jv]
  rw [← MvPowerSeries.coe_substAlgHom hΨ]
  simp only [map_sum, map_mul, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [GlobalTheory.MatChain.ev_jac G (hpt j)]
  try rw [map_mul]
  ring

end Chain

open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies GlobalTheory.MatChain in

theorem constantCoeff_dpolyN_eq_derivAt0 : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : FGLaw C d) (L : LogFGL v d), (∀ a, L.F a = MvPowerSeries.subst (twoVars C d) (G.F a)) → ∀ (n : ℕ) (ι Λ : Type) [Fintype ι] [Fintype Λ] (cp : ι → Fin n) (u : ι → Fin d → C) (β : Λ → Fin n → C) (t : Λ → Fin n → ι) (w : Λ → Fin d → C), (∀ l j, cp (t l j) = j) → (∀ l j, u (t l j) = w l) → ∀ (P : MvPolynomial Λ C) (g : PS C n d), MvPowerSeries.constantCoeff (DpolyN G.F cp u (MvPolynomial.aeval (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) P) g) = derivAt0 P (MvPowerSeries.subst (fun q : Fin n × Fin d => (MvPowerSeries.subst (fun e : Fin d => ∑ l, (β l q.1 * w l e) • (MvPowerSeries.X l : MvPowerSeries Λ C)) (expOf L q.2) : MvPowerSeries Λ C)) g) := by
  intro C _ _ v d G L hL n ι Λ _ _ cp u β t w hcp hu P g
  classical
  show constantCoeff (DpolyN G.F cp u (MvPolynomial.aeval
      (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) P) g) =
    derivAt0 P (subst (psi L β w) g)
  have hΨ : HasSubst (psi L β w) := hasSubst_lemma (cc_psi L β w)
  have hmon0 : ∀ f : PS C n d, DmonN G.F cp u 0 f = f := by
    intro f
    simp [DmonN]
  have hsub : ∀ (Q : MvPolynomial ι C) (s : Finset (ι →₀ ℕ)) (f : PS C n d), Q.support ⊆ s →
      DpolyN G.F cp u Q f = ∑ m ∈ s, MvPowerSeries.C (MvPolynomial.coeff m Q) * DmonN G.F cp u m f := by
    intro Q s f hs
    unfold DpolyN
    refine Finset.sum_subset hs fun m _ hm => ?_
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
  have hadd : ∀ (Q1 Q2 : MvPolynomial ι C) (f : PS C n d),
      DpolyN G.F cp u (Q1 + Q2) f = DpolyN G.F cp u Q1 f + DpolyN G.F cp u Q2 f := by
    intro Q1 Q2 f
    rw [hsub (Q1 + Q2) (Q1.support ∪ Q2.support) f MvPolynomial.support_add,
      hsub Q1 (Q1.support ∪ Q2.support) f Finset.subset_union_left,
      hsub Q2 (Q1.support ∪ Q2.support) f Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_add, map_add, add_mul]
  have hC : ∀ (a : C) (f : PS C n d), DpolyN G.F cp u (MvPolynomial.C a) f = MvPowerSeries.C a * f := by
    intro a f
    rw [hsub (MvPolynomial.C a) {0} f (by rw [MvPolynomial.C_apply]; exact MvPolynomial.support_monomial_subset),
      Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl, hmon0]
  have hfin : ∀ (Q : Fin n → MvPolynomial ι C) (f : PS C n d),
      DpolyN G.F cp u (∑ j, Q j) f = ∑ j, DpolyN G.F cp u (Q j) f := fun Q f =>
    map_sum (AddMonoidHom.mk' (fun Q => DpolyN G.F cp u Q f) (fun Q1 Q2 => hadd Q1 Q2 f)) Q Finset.univ
  have hcomm1 : ∀ (j : Fin n) (x : Fin d → C) (Q : MvPolynomial ι C) (f : PS C n d),
      DofN G.F j x (DpolyN G.F cp u Q f) = DpolyN G.F cp u Q (DofN G.F j x f) := by
    intro j x Q
    induction Q using MvPolynomial.induction_on
    next a =>
      intro f
      rw [hC, hC, GlobalTheory.MatChain.dofN_C_mul]
    next Q1 Q2 h1 h2 =>
      intro f
      rw [hadd, hadd, GlobalTheory.MatChain.dofN_add, h1, h2]
    next Q m h =>
      intro f
      rw [GlobalTheory.MatChain.dpoly_mul_X, GlobalTheory.MatChain.dpoly_mul_X, Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_comm, h]
  have hccs : ∀ f : PS C n d, constantCoeff (subst (psi L β w) f) = constantCoeff f := by
    intro f
    have h0 : constantCoeff (f - MvPowerSeries.C (constantCoeff f)) = 0 := by simp
    have h1 := cc_subst_lemma_2 (cc_psi L β w) h0
    rw [← MvPowerSeries.coe_substAlgHom hΨ, map_sub, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ,
      map_sub] at h1
    simpa [sub_eq_zero] using h1
  have hlinD : ∀ (Q : MvPolynomial Λ C) (b : Fin n → C) (s : Fin n → MvPowerSeries Λ C),
      derivAt0 Q (∑ j, MvPowerSeries.C (b j) * s j) = ∑ j, b j * derivAt0 Q (s j) := by
    intro Q b s
    simp only [derivAt0, map_sum, MvPowerSeries.coeff_C_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => by ring
  revert g
  induction P using MvPolynomial.induction_on
  next a =>
    intro g
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hC, MvPolynomial.C_apply, derivAt0_monomial]
    simp [mfact, hccs, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  next P1 P2 h1 h2 =>
    intro g
    rw [map_add, hadd, map_add, h1, h2,
      (derivAt0_linear C v Λ P1 P2 (subst (psi L β w) g) (subst (psi L β w) g) 0).2.2.1]
  next Q l h =>
    intro g
    have hφ : MvPolynomial.aeval (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C))
          (Q * MvPolynomial.X l) =
        ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.aeval
          (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) Q *
            MvPolynomial.X (t l j)) := by
      rw [map_mul, MvPolynomial.aeval_X, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hφ, hfin]
    simp only [GlobalTheory.MatChain.dpoly_C_mul, GlobalTheory.MatChain.dpoly_mul_X, hcp, hu, hcomm1]
    rw [← derivAt0_pderiv v Q l, pderiv_subst_psi L β w G hL l g, ← MvPowerSeries.coe_substAlgHom hΨ]
    simp only [map_sum, map_mul, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ, MvPowerSeries.constantCoeff_C, h]
    rw [hlinD]

end GlobalTheory.ExpCoord
