import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteTwistingNotIsGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeParameterMaxTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairStatementOfHeightAlterationStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.OmTerm

open GlobalTheory.PairTerm GlobalTheory.TrivFlag GlobalTheory.VertTerm

section Algebra

theorem mem_span_prod_X {ι : Type} {d : ℕ} {g : MvPolynomial ι ℚ} (hg : g.IsHomogeneous d) :
    g ∈ Submodule.span ℚ (Set.range fun ν : Fin d → ι => ∏ i, (X (ν i) : MvPolynomial ι ℚ)) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  have h1 : u.degree = d := by
    have := hg (mem_support_iff.1 hu)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have e₁ : (monomial u (g.coeff u) : MvPolynomial ι ℚ) = g.coeff u • monomial u 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e₁]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have e₂ : (monomial u 1 : MvPolynomial ι ℚ) = ((Finsupp.toMultiset u).map X).prod := by
    rw [monomial_eq, C_1, one_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]
  have e₃ : Multiset.card (Finsupp.toMultiset u) = d := by
    rw [Finsupp.card_toMultiset, ← h1]; rfl
  obtain ⟨l, hl⟩ := Quotient.exists_rep (Finsupp.toMultiset u)
  rw [e₂, ← hl]
  rw [← hl] at e₃
  obtain rfl : l.length = d := e₃
  refine ⟨l.get, ?_⟩
  change _ = (Multiset.map X (l : Multiset ι)).prod
  rw [Multiset.map_coe, Multiset.prod_coe]
  exact Fin.prod_univ_fun_getElem l (fun a => (X a : MvPolynomial ι ℚ))

theorem numL_prod_X {A : Type} (num : Multiset A → ℝ) (d : ℕ) (μ : Multiset A) (h : Multiset.card μ = d) :
    numL num d (μ.map X).prod = num μ := by
  classical
  have e₂ : (monomial (Multiset.toFinsupp μ) 1 : MvPolynomial A ℝ) = (μ.map X).prod := by
    conv_rhs => rw [← Multiset.toFinsupp_toMultiset μ]
    rw [monomial_eq, C_1, one_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]
  rw [← e₂, ← congrFun (coe_basisMonomials A ℝ), numL, Module.Basis.constr_basis, if_pos, Multiset.toFinsupp_toMultiset]
  rw [← h]
  conv_rhs => rw [← Multiset.toFinsupp_toMultiset μ, Finsupp.card_toMultiset]
  rfl

theorem numL_X_mul_prod {A : Type} (num : Multiset A → ℝ) (d : ℕ) (a : A) (f : Fin d → A) :
    numL num (d + 1) (X a * ∏ i, X (f i)) = num (a ::ₘ Finset.univ.val.map f) := by
  rw [← numL_prod_X num (d + 1) _ (by simp), Multiset.map_cons, Multiset.prod_cons, Multiset.map_map]
  rfl

def evIdxQ (D : D7) (N : ℕ) : MvPolynomial (Vm D.what₂.Tau N) ℚ →ₐ[ℚ] MvPolynomial (Idx D N) ℚ :=
  aeval fun v => match v with
    | Sum.inl q => X (Sum.inl q)
    | Sum.inr (b, k) => C ((k.factorial : ℚ)⁻¹) * ∑ l, X (Sum.inr (b, l)) ^ k

theorem evIdx_toR (D : D7) (N : ℕ) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) :
    evIdx D N (toR G) = toR (evIdxQ D N G) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [toR]
  | add P Q hP hQ => simp only [toR, map_add] at *; rw [hP, hQ]
  | mul_X P v hP =>
    simp only [toR, map_mul] at *
    rw [hP]
    congr 1
    rcases v with q | ⟨b, k⟩ <;> simp [evIdx, evIdxQ]

theorem isHomogeneous_evIdxQ (D : D7) (N : ℕ) {G : MvPolynomial (Vm D.what₂.Tau N) ℚ} {d : ℕ}
    (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau N) d) : (evIdxQ D N G).IsHomogeneous d := by
  classical
  have hv : ∀ v, (evIdxQ D N (X v)).IsHomogeneous (wt D.what₂.Tau N v) := by
    rintro (q | ⟨b, k⟩)
    · simpa [evIdxQ, wt] using isHomogeneous_X ℚ (Sum.inl q : Idx D N)
    · simp only [evIdxQ, aeval_X, wt]
      refine IsHomogeneous.C_mul ?_ _
      exact IsHomogeneous.sum _ _ _ fun l _ => by simpa using (isHomogeneous_X ℚ (Sum.inr (b, l) : Idx D N)).pow k
  rw [G.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun u hu => ?_
  have h1 : Finsupp.weight (wt D.what₂.Tau N) u = d := hG (mem_support_iff.1 hu)
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, ← h1, Finsupp.weight_apply, Finsupp.sum]
  have : evIdxQ D N (C (G.coeff u)) = C (G.coeff u) := by simp [evIdxQ]
  rw [this]
  refine IsHomogeneous.C_mul ?_ _
  refine IsHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, smul_eq_mul, mul_comm]
  exact (hv v).pow _

end Algebra

section Lines

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

def rootLn (y : Rt D.what₂.Tau N) : Ln S.Dw :=
  if h : (y.2 : ℕ) < S.Dw.p then
    (false, ⟨.inl (tauEmb D y.1, y.2), by
      have : (y.2 : ℕ) < S.Dw.mult (tauEmb D y.1) := by rw [Datum.mult, if_pos (A.cm y.1)]; exact h
      simp [letterOf, this]⟩)
  else
    (true, ⟨.inl (conjEmb (tauEmb D y.1), S.Dw.p + S.Dw.q - 1 - y.2), by
      have h₁ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (tauEmb D y.1)
      rw [Datum.mult.eq_1 _ (tauEmb D y.1), if_pos (A.cm y.1)] at h₁
      have h₂ := S.rank_eq
      have := y.2.2
      have : S.Dw.p + S.Dw.q - 1 - y.2 < S.Dw.mult (conjEmb (tauEmb D y.1)) := by omega
      simp [letterOf, this]⟩)

def wholeLn : Fin (D.R.f * N) ⊕ Fin (D.R.f * N) → Ln S.Dw
  | .inl k => (false, ⟨.inr k, by rw [letterOf_whole S k]; rfl⟩)
  | .inr k => (true, ⟨.inr k.rev, by rw [letterOf_whole S k.rev]; rfl⟩)

def lnOf : Idx D N → Bool × Ln S.Dw := Sum.elim (fun q => (q.1, rootLn S q.2)) fun q => (q.1, wholeLn S q.2)

theorem lnSym_rootLn (a : ℕ → Bool) (R : Option ℝ) (y : Rt D.what₂.Tau N) :
    lnSym a R (rootLn S y) = rootSym S.Dw a R (tauEmb D y.1) y.2 := by
  unfold rootLn rootSym
  split_ifs <;> rfl

theorem lnSym_lnOf (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (k : Idx D N) :
    lnSym (Function.update (ArIn.ind Sx) p (lnOf S k).1) (some R) (lnOf S k).2 = symOf S Sx R p k := by
  rcases k with q | ⟨b, k | k⟩
  · exact lnSym_rootLn S _ _ _
  · rfl
  · rfl

variable {S} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ)

theorem lnLB_rootLn (b : Bool) (y : Rt D.what₂.Tau N) : lnLB z b (rootLn S y) = rootOf z jc (b, y) := by
  unfold rootLn rootOf admitted.rootLB
  split_ifs
  · exact lnLB_false z b _
  · exact lnLB_true z b _

theorem evC_eq_aeval (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) :
    evC (mdlOf z jc) (rootOf z jc) G =
      aeval (fun k => (mdlOf z jc).Z.c1 (lnLB z (lnOf S k).1 (lnOf S k).2)) (evIdxQ D N G) := by
  have : (aeval (mdlOf z jc).Z.c1).comp (evV (mdlOf z jc) (rootOf z jc)) =
      (aeval (fun k => (mdlOf z jc).Z.c1 (lnLB z (lnOf S k).1 (lnOf S k).2))).comp (evIdxQ D N) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rcases v with ⟨b, y⟩ | ⟨b, k⟩
    · simp only [AlgHom.comp_apply, evV, evIdxQ, aeval_X, lnOf, Sum.elim_inl, lnLB_rootLn z jc]
    · cases b <;>
      · simp only [AlgHom.comp_apply, evV, evIdxQ, aeval_X, lnOf, Sum.elim_inr, map_mul, map_add, map_sum, map_pow, aeval_C,
          Fintype.sum_sum_type, wholeLn, lnLB_false, lnLB_true, mdlOf_lieW, mdlOf_omW]
        refine congrArg (_ * ·) (congrArg₂ (· + ·) ?_ ?_) <;>
          exact Finset.sum_congr rfl fun x _ => congrArg (· ^ k) (aeval_X _ _)
  exact congrArg (fun f => f G) this

theorem om_Dv_eq {t : D.what₂.Tau} {τ : Emb D p} (ht : jc.comp τ = tauEmb D t)
    (i : Fin (N - rkOf (PsiOf D jc) N j τ)) (i' : Fin N) (h : (i' : ℕ) = j + i) :
    ((mdlOf z jc).om τ).Dv i = vdiv hp hW _ _ _ (lnId z hp hW (rootLn S (t, i'))) := by
  have hr : rkOf (PsiOf D jc) N j τ = j := if_pos ⟨t, ht⟩
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  have hi : ¬ (i' : ℕ) < S.Dw.p := by omega
  have e' : (i.rev : ℕ) = S.Dw.p + S.Dw.q - 1 - i' := by rw [Fin.val_rev]; omega
  have e : rootLn S (t, i') = (true, ⟨.inl (conjEmb (jc.comp τ), i.rev), by rw [letterOf_om S jc τ i]; rfl⟩) := by
    rw [rootLn, dif_neg hi]
    simp only [ht, e']
  rw [mdlOf_om_Dv, e, vdiv_lnId_true z hp hW _ _ (letterOf_om S jc τ i)]

end Lines

theorem mixEv_eq {D : D7} (O : Setup D) (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (c : O.s.Comp) :
    (arIn O.s O.Φ O.met.hm).mixEv Sx R p c = (rename (symOf O.S Sx R p)).comp (evIdx D O.N) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with ⟨b, y⟩ | ⟨b, k⟩
  · refine (aeval_X _ _).trans (Eq.symm ?_)
    change rename (symOf O.S Sx R p) (evIdx D O.N (X (Sum.inl (b, y)))) = X (symOf O.S Sx R p (Sum.inl (b, y)))
    simp only [evIdx, aeval_X, rename_X]
  · refine (aeval_X _ _).trans (Eq.symm ?_)
    change rename (symOf O.S Sx R p) (evIdx D O.N (X (Sum.inr (b, k)))) =
      (C ((k.factorial : ℝ)⁻¹) : MvPolynomial (Sym D.host.E →₀ ℤ) ℝ) * ∑ l, X (symOf O.S Sx R p (Sum.inr (b, l))) ^ k
    simp only [evIdx, aeval_X, rename_X, map_mul, rename_C, map_sum, map_pow]
    rfl

theorem sum_numL_eq {ι A C' L : Type} [Fintype C'] [Fintype L] {d : ℕ} (num : C' → Multiset A → ℝ) (s : ι → A) (a a' : ι)
    (Ch : L → Type) [∀ la, CommRing (Ch la)] [∀ la, Algebra ℚ (Ch la)] (φ : ∀ la, Ch la →ₗ[ℚ] ℚ) (cl : ∀ la, ι → Ch la)
    (t : ℝ) (w v : L → ℝ)
    (h : ∀ ν : Fin d → ι, ∑ c, (num c (s a ::ₘ Finset.univ.val.map fun i => s (ν i)) -
      num c (s a' ::ₘ Finset.univ.val.map fun i => s (ν i))) =
      t * ∑ la, w la * (((φ la (∏ i, cl la (ν i)) : ℚ) : ℝ) / v la))
    {g : MvPolynomial ι ℚ} (hg : g.IsHomogeneous d) :
    ∑ c, numL (num c) (d + 1) (rename s ((X a - X a') * toR g)) =
      t * ∑ la, w la * (((φ la (aeval (cl la) g) : ℚ) : ℝ) / v la) := by
  have hm := mem_span_prod_X hg
  clear hg
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, rfl⟩ := hx
    simp only [toR, map_prod, map_X, aeval_X, sub_mul, map_sub, map_mul, rename_X]
    rw [← h ν]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [numL_X_mul_prod, numL_X_mul_prod]
  | zero => simp [toR]
  | add x y _ _ hx hy =>
    simp only [toR, map_add, mul_add, Finset.sum_add_distrib, Rat.cast_add, add_div] at *
    rw [hx, hy]
  | smul q x _ hx =>
    have e : toR (q • x) = (q : ℝ) • toR x := by
      simp [toR, smul_eq_C_mul]
    simp only [e, mul_smul_comm, map_smul, smul_eq_mul, Rat.cast_mul, ← Finset.mul_sum, hx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun la _ => ?_
    ring

theorem arMix_dRt (hP : PairSt) {D : D7} (O : Setup D) (hO : O.Core) (p : ℕ) [Fact p.Prime]
    (W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : Formalism.L2.Geo.PlL D p → (KW p →+* ℂ))
    (hWv : ∀ la (x : D.what₂.LL), D.what₂.embLL x ∈ W la ↔ IsDedekindDomain.HeightOneSpectrum.valuation D.what₂.LL la.1 x ≤ 1)
    (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)) (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (y : Rt D.what₂.Tau O.N)
    (G : MvPolynomial (Vm D.what₂.Tau O.N) ℚ) (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau O.N) (dimFl D.what₂.Tau O.N)) :
    (arIn O.s O.Φ O.met.hm).arMix Sx R p (dRt D.what₂.Tau O.N y * toR G) = Real.log p * (letI := Formalism.L2.Geo.finPl D p;
      ∑ la, Formalism.L2.Geo.wtL D p la * ((((mdlOf (z la) (jc la)).Z.capDeg
        (vdiv Fact.out (hW la) _ _ _ (lnId (z la) Fact.out (hW la) (rootLn O.S y)))
        (evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G) : ℚ) : ℝ) / ((mdlOf (z la) (jc la)).cov : ℝ))) := by
  letI := Formalism.L2.Geo.finPl D p
  have key := sum_numL_eq (d := dimFl D.what₂.Tau O.N) (A := Sym D.host.E →₀ ℤ) (arIn O.s O.Φ O.met.hm).num
    (symOf O.S Sx R p) (Sum.inl (false, y)) (Sum.inl (true, y)) (fun la => (mdlOf (z la) (jc la)).Z.Ch)
    (fun la => (mdlOf (z la) (jc la)).Z.capDeg
      (vdiv Fact.out (hW la) _ _ _ (lnId (z la) Fact.out (hW la) (rootLn O.S y))))
    (fun la k => (mdlOf (z la) (jc la)).Z.c1 (lnLB (z la) (lnOf O.S k).1 (lnOf O.S k).2))
    (Real.log p) (Formalism.L2.Geo.wtL D p) (fun la => ((mdlOf (z la) (jc la)).cov : ℝ)) (fun ν => by
      have := hP D O hO p W hW hWv z Sx R hR (rootLn O.S y) fun i => lnOf O.S (ν i)
      simp only [lnSym_lnOf, lnSym_rootLn] at this
      exact this) (isHomogeneous_evIdxQ D O.N hG)
  simp only [evC_eq_aeval]
  rw [← key, ArIn.arMix]
  erw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  change numL _ _ ((arIn O.s O.Φ O.met.hm).mixEv Sx R p c _) = _
  rw [mixEv_eq]
  refine congrArg (numL _ _) (congrArg (rename (symOf O.S Sx R p)) ?_)
  change evIdx D O.N (_ * _) = _
  rw [map_mul, evIdx_toR]
  simp only [dRt, map_sub, evIdx, aeval_X]

theorem arMix_dRt_om : GlobalTheory.Published.RegularAlteration → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    UnramE D p → p ∉ O.Y.lev → ∀ (W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : Formalism.L2.Geo.PlL D p → (KW p →+* ℂ)), (∀ la, Pin (W la) (jc la)) →
    (∀ la (x : D.what₂.LL), D.what₂.embLL x ∈ W la ↔ IsDedekindDomain.HeightOneSpectrum.valuation D.what₂.LL la.1 x ≤ 1) →
    ∀ (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)) (Sx : Finset ℕ) (R : ℝ), 2 ≤ R →
    ∀ (τ0 : D.what₂.Tau) (τ' : Formalism.L2.Geo.PlL D p → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (O.Y.N - rkOf (PsiOf D (jc la)) O.Y.N O.Y.j (τ' la))) (i' : Fin O.Y.N), (∀ la, (i' : ℕ) = O.Y.j + i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau O.Y.N) (dimFl D.what₂.Tau O.Y.N) →
      O.Y.arMix Sx R p (dRt D.what₂.Tau O.Y.N (τ0, i') * toR G) = Real.log p * (letI := Formalism.L2.Geo.finPl D p;
        ∑ la, Formalism.L2.Geo.wtL D p la * ((((mdlOf (z la) (jc la)).Z.capDeg (((mdlOf (z la) (jc la)).om (τ' la)).Dv (i la))
          (evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G) : ℚ) : ℝ) / ((mdlOf (z la) (jc la)).cov : ℝ))) := by
  intro hA h2 hH D O hO p _ _ _ _ W hW jc _ hWv z Sx R hR τ0 τ' hτ i i' hi G hG
  refine (arMix_dRt (GlobalTheory.T.pair_statement_of_height_alteration h2 hH hA) O hO p W hW jc hWv z Sx R hR (τ0, i') G hG).trans ?_
  refine congrArg (Real.log p * ·) (Finset.sum_congr rfl fun la _ => ?_)
  rw [om_Dv_eq (z la) (jc la) (hτ la) (i la) i' (hi la)]

end GlobalTheory.OmTerm
end
