import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDenOfValLeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValDetLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemExtLatOfMemLocP

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetPoint

section Expand

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

abbrev expL (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : (ι × Fin b × Fin b) →₀ ℕ :=
  μ.comapDomain Sum.inl Sum.inl_injective.injOn

abbrev expR (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : DVar ι a b →₀ ℕ :=
  μ.comapDomain Sum.inr Sum.inr_injective.injOn

omit [Fintype ι] in
theorem constr_monomial {σ V : Type} [AddCommGroup V] [Module K V] (f : (σ →₀ ℕ) → V) (μ : σ →₀ ℕ) (c : K) :
    (basisMonomials σ K).constr K f (monomial μ c) = c • f μ := by
  have h : (monomial μ c : MvPolynomial σ K) = c • basisMonomials σ K μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Module.Basis.constr_basis]

omit [Fintype ι] in
theorem jetLin_eq_sum (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J Q = ∑ μ ∈ Q.support, J (expR μ) • monomial (expL μ) (Q.coeff μ) := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [jetLin, constr_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_comm]

theorem jetMap_eq_sum (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J n P = ∑ μ ∈ (subD K ι a b (sharp n P)).support,
      J (expR μ) • monomial (expL μ) ((subD K ι a b (sharp n P)).coeff μ) :=
  jetLin_eq_sum J _

def ptEval (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L) :
    MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →+* Pol L ι b :=
  eval₂Hom (C.comp σ) (Sum.elim X fun k => C (ap k.1 k.2.2 k.2.1))

theorem ptEval_monomial (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L)
    (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    ptEval σ ap (monomial μ c) = ptTable ap (expR μ) • monomial (expL μ) (σ c) := by
  rw [ptEval, eval₂Hom_monomial, monomial_eq, ptTable, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, smul_eq_C_mul,
    map_prod]
  simp only [RingHom.comp_apply, Sum.elim_inl, Sum.elim_inr, Finsupp.comapDomain_apply, map_pow]
  ring

omit [Fintype ι] in
theorem ptEval_subD (hab : a ≤ b) (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L) (P : Pol K ι a) :
    ptEval σ ap (subD K ι a b P) = substAdj hab ap (map σ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [ptEval, subD, substAdj]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    have h : v.2.2.1 < b := lt_of_lt_of_le v.2.2.2 hab
    simp only [subD, substAdj, aeval_X, dif_pos h, map_sum, map_mul, ptEval, eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    exact Finset.sum_congr rfl fun β _ => mul_comm _ _

theorem sum_ptTable (hab : a ≤ b) (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L) (P : Pol K ι a) :
    ∑ μ ∈ (subD K ι a b P).support, ptTable ap (expR μ) • monomial (expL μ) (σ ((subD K ι a b P).coeff μ)) =
      substAdj hab ap (map σ P) := by
  rw [← ptEval_subD]
  conv_rhs => rw [(subD K ι a b P).as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun μ _ => (ptEval_monomial σ ap μ _).symm

theorem jetMap_ptTable (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (ptTable ap) n P = substAdj hab ap (sharp n P) := by
  rw [jetMap_eq_sum]
  have h := sum_ptTable hab (RingHom.id K) ap (sharp n P)
  rwa [map_id] at h

theorem jetMap_mem [Infinite K] (hab : a ≤ b) (n : ι → ℕ) (P : Pol K ι a) (U : Submodule K (Pol K ι b))
    (h : ∀ ap : ι → Matrix (Fin a) (Fin b) K, substAdj hab ap (sharp n P) ∈ U) (J : (DVar ι a b →₀ ℕ) → K) :
    jetMap J n P ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set Q := subD K ι a b (sharp n P) with hQ
  have h0 : (∑ μ ∈ Q.support, monomial (expR μ) (φ (monomial (expL μ) (Q.coeff μ))) :
      MvPolynomial (DVar ι a b) K) = 0 := by
    refine MvPolynomial.funext fun x => ?_
    have h1 := hφ _ (h fun τ => Matrix.of fun α β => x (τ, β, α))
    rw [← jetMap_ptTable, jetMap_eq_sum, map_sum] at h1
    rw [map_zero, map_sum, ← h1]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, mul_comm]
    rfl
  have h2 := congrArg ((basisMonomials (DVar ι a b) K).constr K J) h0
  rw [map_zero, map_sum] at h2
  rw [jetMap_eq_sum, map_sum, ← h2]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [constr_monomial, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

theorem coe_jetOp (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (F : VV K lam) (h : jetMap J n (F : Pol K ι a) ∈ VV K lam') :
    ((jetOp lam lam' J n F : VV K lam') : Pol K ι b) = jetMap J n (F : Pol K ι a) := by
  have h1 : retrVV K lam' ((⟨_, h⟩ : VV K lam') : Pol K ι b) = ⟨_, h⟩ := Submodule.projectionOnto_apply_left _ _
  exact congrArg Subtype.val h1

omit [Fintype ι] in
theorem detShift_eq {hab : a < b} {lam : ι → DomWeight a} {lam' : ι → DomWeight b} {s s' : ι → ℤ} {n : ι → ℕ}
    (h : WtCompat hab lam lam' s s' n) (τ : ι) : (lam' τ).detShift = -s τ := by
  rw [DomWeight.detShift, dif_pos (by omega)]
  exact h.2.1 τ _ (by simp only; omega)

omit [Fintype ι] in
theorem map_frDet {R : Type} [CommRing R] (φ : Pol K ι a →+* R) (τ : ι) :
    φ (frDet K a τ) = (Matrix.of fun α s : Fin a => φ (X (τ, α, s))).det := by
  rw [frDet, RingHom.map_det]
  rfl

omit [Fintype ι] in
theorem evalFr_substAdj (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) K) (y : ι → Matrix (Fin b) (Fin b) K)
    (P : Pol K ι a) :
    evalFr y (substAdj hab ap P) = evalFr (fun τ => (ap τ * y τ).submatrix id (Fin.castLE hab)) P := by
  unfold evalFr
  induction P using MvPolynomial.induction_on with
  | C c => simp [substAdj]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [substAdj, Matrix.mul_apply]

end Expand

theorem substitution : Substitution := by
  intro K _ ι _ a b hab lam lam' s s' n hw ap F
  have h1 : ((jetOp lam lam' (ptTable ap) n F : VV K lam') : Pol K ι b) =
      substAdj hab.le ap (sharp n (F : Pol K ι a)) := by
    rw [coe_jetOp, jetMap_ptTable hab.le]
    rw [jetMap_ptTable hab.le]
    exact GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hab lam lam' s s' n hw ap _ F.2
  refine ⟨h1, fun y => ?_, fun y => ?_⟩
  · unfold fnOf sharp evalFr
    rw [map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_frDet, ← zpow_add₀ (y τ).det_ne_zero, ← hw.2.2 τ, zpow_natCast]
    congr 2
    ext α t
    simp
  · rw [h1, fnOf, evalFr_substAdj, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [detShift_eq hw, zpow_neg]

section Integral

open Formalism.GradedWeylDivisibility (blockAct)

variable {K L Γ : Type} [Field K] [Field L] [LinearOrderedCommGroupWithZero Γ] {ι : Type} [Fintype ι] {a b : ℕ}

theorem mem_range_iff (v : Valuation L Γ) {τ : Type} (P : MvPolynomial τ L) :
    P ∈ (map (σ := τ) v.integer.subtype).range ↔ ∀ m, v (P.coeff m) ≤ 1 := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (Q.coeff m).2
  · intro h
    rw [P.as_sum]
    exact sum_mem fun m _ => ⟨monomial m ⟨_, h m⟩, by rw [map_monomial]; rfl⟩

omit [Fintype ι] in
theorem substAdj_int (v : Valuation L Γ) (hab : a ≤ b) (A : ι → Matrix (Fin a) (Fin b) L)
    (hA : ∀ τ i j, v (A τ i j) ≤ 1) {P : Pol L ι a} (hP : P ∈ (map v.integer.subtype).range) :
    substAdj hab A P ∈ (map v.integer.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [substAdj]⟩
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | mul_X p x hp =>
    rw [map_mul, map_mul, map_X]
    refine mul_mem hp ?_
    rw [substAdj, aeval_X]
    exact sum_mem fun β _ => mul_mem ⟨C ⟨_, hA _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩

theorem sharp_int (v : Valuation L Γ) (n : ι → ℕ) {P : Pol L ι a} (hP : P ∈ (map v.integer.subtype).range) :
    sharp n P ∈ (map v.integer.subtype).range := by
  refine mul_mem hP (prod_mem fun τ _ => pow_mem ?_ _)
  rw [frDet, Matrix.det_apply']
  exact sum_mem fun g _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => ⟨X _, map_X _ _⟩)

omit [Fintype ι] in
theorem blockAct_substAdj (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) L) (g : ι → Matrix (Fin b) (Fin b) L)
    (P : Pol L ι a) : blockAct L g (substAdj hab ap P) = substAdj hab (fun τ => ap τ * g τ) P := by
  have h : (blockAct L g).comp (substAdj hab ap) = substAdj hab (fun τ => ap τ * g τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, blockAct, substAdj, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply]
    simp only [algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  exact congrArg (fun φ => φ P) h

omit [Fintype ι] in
theorem substAdj_blockAct (hab : a ≤ b) (A : ι → Matrix (Fin a) (Fin b) L) (g : ι → Matrix (Fin a) (Fin a) L)
    (P : Pol L ι a) : substAdj hab A (blockAct L g P) = substAdj hab (fun τ => g τ * A τ) P := by
  have h : (substAdj hab A).comp (blockAct L g) = substAdj hab (fun τ => g τ * A τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, blockAct, substAdj, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply]
    simp only [algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  exact congrArg (fun φ => φ P) h

omit [Fintype ι] in
theorem map_blockAct (σ : K →+* L) (g : ι → Matrix (Fin a) (Fin a) K) (P : Pol K ι a) :
    map σ (blockAct K g P) = blockAct L (fun τ => (g τ).map σ) (map σ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [blockAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    simp [blockAct]

theorem map_sharp (σ : K →+* L) (n : ι → ℕ) (P : Pol K ι a) : map σ (sharp n P) = sharp n (map σ P) := by
  simp only [sharp, map_mul, map_prod, map_pow, map_frDet, map_X]
  rfl

theorem blockAct_sharp (g : ι → Matrix (Fin a) (Fin a) K) (n : ι → ℕ) (P : Pol K ι a) :
    blockAct K g (sharp n P) = (∏ τ, (g τ).det ^ n τ) • sharp n (blockAct K g P) := by
  have h : ∀ τ, blockAct K g (frDet K a τ) = C (g τ).det * frDet K a τ := fun τ => by
    have h1 := map_frDet (blockAct K (n := a) g : Pol K ι a →+* Pol K ι a) τ
    rw [RingHom.coe_coe] at h1
    rw [h1, RingHom.map_det, frDet, ← Matrix.det_mul]
    congr 1
    ext1 α t
    simp [blockAct, Matrix.mul_apply]
  simp only [sharp, map_mul, map_prod, map_pow, h, mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul]
  ring

theorem point_int (v : Valuation L Γ) (σ : K →+* L) (hab : a ≤ b) (e s' : ι → ℤ) (n : ι → ℕ)
    (hn : ∀ τ, (n τ : ℤ) = e τ + s' τ) (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K)
    (ap : ι → Matrix (Fin a) (Fin b) L)
    (hA : ∀ τ i j, v (((((B τ)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap τ *
      (BW τ : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1)
    (F : Pol K ι a) (hF : ∀ m, v (σ (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ e τ) •
      blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F).coeff m)) ≤ 1) :
    ∃ Z : Pol L ι b, (∀ m, v (Z.coeff m) ≤ 1) ∧
      blockAct L (fun τ => (BW τ : Matrix (Fin b) (Fin b) K).map σ) (substAdj hab ap (map σ (sharp n F))) =
        σ (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ) • Z := by
  refine ⟨_, (mem_range_iff v _).mp (substAdj_int v hab _ hA (sharp_int v n ((mem_range_iff v (map σ
    ((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ e τ) •
      blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F))).mpr fun m => by rw [coeff_map]; exact hF m))), ?_⟩
  have h1 : (fun τ => ap τ * (BW τ : Matrix (Fin b) (Fin b) K).map σ) = fun τ =>
      (B τ : Matrix (Fin a) (Fin a) K).map σ * ((((B τ)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap τ *
      (BW τ : Matrix (Fin b) (Fin b) K).map σ) := by
    funext τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ σ.map_zero σ.map_one,
      Matrix.one_mul]
  have h2 : (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ n τ) =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ) * ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ e τ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (B τ).det_ne_zero, add_comm, ← hn τ, zpow_natCast]
  rw [blockAct_substAdj, h1, ← substAdj_blockAct, ← map_blockAct, blockAct_sharp, h2, ← map_smul, ← map_sharp]
  congr 1
  simp only [sharp, smul_eq_C_mul, map_mul, map_C]
  ring

end Integral

section Closure

open Formalism.GradedWeylDivisibility (blockAct)

variable {K L Γ : Type} [Field K] [NumberField K] [Field L] [LinearOrderedCommGroupWithZero Γ]

theorem exists_mul_of_approx (w : HeightOneSpectrum (𝓞 K)) (v : Valuation L Γ) (σ : K →+* L)
    (hσ : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) (x c : K)
    (h : ∀ ε : K, ε ≠ 0 → ∃ z : L, v z ≤ 1 ∧ v (σ x - σ c * z) ≤ v (σ ε)) :
    ∃ u : K, w.valuation K u ≤ 1 ∧ x = c * u := by
  have hdiv : ∀ y ε : K, ε ≠ 0 → v (σ y) ≤ v (σ ε) → w.valuation K (y / ε) ≤ 1 := fun y ε hε hy => by
    rw [← hσ, map_div₀, map_div₀]
    exact div_le_one_of_le₀ hy zero_le
  by_cases hc : c = 0
  · subst hc
    refine ⟨0, by simp, ?_⟩
    rw [mul_zero]
    by_contra hx
    obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer K
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    obtain ⟨z, -, hz⟩ := h (x * π) (mul_ne_zero hx hπ0)
    rw [map_zero, zero_mul, sub_zero] at hz
    have h1 := hdiv _ _ (mul_ne_zero hx hπ0) hz
    rw [div_mul_cancel_left₀ hx, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · obtain ⟨z, hz1, hz⟩ := h c hc
    refine ⟨x / c, hdiv _ _ hc ?_, by field_simp⟩
    have h1 : σ x = (σ x - σ c * z) + σ c * z := by ring
    rw [h1]
    refine v.map_add_le hz ?_
    rw [map_mul]
    exact mul_le_of_le_one_right' hz1

theorem closureIntegral : ClosureIntegral := by
  intro K _ _ w L Γ _ _ v σ hσ ι _ a b hab lam lam' s s' n hw M MW B BW hM hMW κ J hJ F hF
  have hmem : jetMap J n (F : Pol K ι a) ∈ VV K lam' :=
    jetMap_mem hab.le n _ _ (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hab lam lam' s s' n hw ap _ F.2) J
  rw [GlobalTheory.HAtBasis.mem_HAt_iff K w ι a lam M B hM] at hF
  set Q := subD K ι a b (sharp n (F : Pol K ι a)) with hQ
  set D := ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ with hD
  set T := blockAct K (n := b) (fun τ => (BW τ : Matrix (Fin b) (Fin b) K)) with hT
  set d := fun μ => T (monomial (expL μ) (Q.coeff μ)) with hd
  have hH : T (jetMap J n (F : Pol K ι a)) = ∑ μ ∈ Q.support, J (expR μ) • d μ := by
    rw [jetMap_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_smul _ _ _
  have hpt : ∀ ap : ι → Matrix (Fin a) (Fin b) L, admitted v σ M MW ap → ∀ p, ∃ z : L, v z ≤ 1 ∧
      ∑ μ ∈ Q.support, ptTable ap (expR μ) * σ ((d μ).coeff p) = σ D * z := by
    intro ap hap p
    obtain ⟨Z, hZ, hZ'⟩ := point_int v σ hab.le (fun τ => (lam τ).detShift) s' n hw.2.2 B BW ap
      (fun τ => (GlobalTheory.ExtLatMatrix.extLat_matrix_integral K w L Γ v σ hσ).2 a b (M τ) (MW τ) (B τ) (BW τ) (hM τ).2 (hMW τ).2 (ap τ) (hap τ))
      F fun m => (hσ _).mpr (hF m)
    refine ⟨Z.coeff p, hZ p, ?_⟩
    have h1 := congrArg (coeff p) hZ'
    rw [← sum_ptTable, map_sum, coeff_sum, coeff_smul, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_smul, coeff_smul, smul_eq_mul, ← map_monomial, ← map_blockAct, coeff_map]
  have hu : ∀ p, ∃ u : K, w.valuation K u ≤ 1 ∧ (T (jetMap J n (F : Pol K ι a))).coeff p = κ * D * u := by
    intro p
    refine exists_mul_of_approx w v σ hσ _ _ fun ε hε => ?_
    obtain ⟨⟨t, ht⟩, htd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Q.support
      fun μ => (d μ).coeff p
    have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by simpa using nonZeroDivisors.ne_zero ht
    obtain ⟨k, c, ap, hc, hap, happ⟩ := hJ (ε * algebraMap (𝓞 K) K t) (mul_ne_zero hε ht0)
    choose z hz hz' using fun i => hpt (ap i) (hap i) p
    refine ⟨∑ i, c i * z i, v.map_sum_le fun i _ => ?_, ?_⟩
    · rw [map_mul]
      exact mul_le_one' (hc i) (hz i)
    have h1 : σ ((T (jetMap J n (F : Pol K ι a))).coeff p) - σ (κ * D) * ∑ i, c i * z i =
        ∑ μ ∈ Q.support, (σ (J (expR μ)) - σ κ * ∑ i, c i * ptTable (ap i) (expR μ)) * σ ((d μ).coeff p) := by
      have h2 : σ D * ∑ i, c i * z i =
          ∑ μ ∈ Q.support, (∑ i, c i * ptTable (ap i) (expR μ)) * σ ((d μ).coeff p) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_left_comm, ← hz' i, Finset.mul_sum]
        simp only [mul_assoc]
      rw [hH, coeff_sum, map_sum, map_mul, mul_assoc, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [coeff_smul, smul_eq_mul, map_mul]
      ring
    rw [h1]
    refine v.map_sum_le fun μ hμ => ?_
    obtain ⟨y, hy⟩ := htd μ hμ
    have h3 : v (σ (algebraMap (𝓞 K) K t * (d μ).coeff p)) ≤ 1 := by
      rw [hσ, ← Algebra.smul_def]
      exact hy ▸ w.valuation_le_one y
    rw [map_mul]
    refine (mul_le_mul_left (happ _ (GlobalTheory.subD_sharp_inDeg K ι a b hab lam lam' s s' n hw _ F.2 μ hμ)) _).trans ?_
    rw [map_mul, map_mul] at h3
    rw [map_mul, map_mul, mul_assoc]
    exact mul_le_of_le_one_right' h3
  have hfac : detFac s s' B BW = D * ∏ τ, (BW τ : Matrix (Fin b) (Fin b) K).det ^ (lam' τ).detShift := by
    simp only [detFac, hD, detShift_eq hw, Finset.prod_mul_distrib]
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (B τ).det_ne_zero
  have hW0 : (∏ τ, (BW τ : Matrix (Fin b) (Fin b) K).det ^ (lam' τ).detShift) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (BW τ).det_ne_zero
  by_cases hκ : κ = 0
  · refine ⟨0, zero_mem _, Subtype.ext ?_⟩
    have h0 : T (jetMap J n (F : Pol K ι a)) = 0 := by
      ext p
      obtain ⟨u, -, hu'⟩ := hu p
      rw [hu', hκ, zero_mul, zero_mul, coeff_zero]
    have h1 := congrArg (blockAct K (n := b) fun τ => (((BW τ)⁻¹ : GL (Fin b) K) : Matrix (Fin b) (Fin b) K)) h0
    rw [map_zero, hT, ← AlgHom.comp_apply, blockAct_comp] at h1
    simp only [Units.mul_inv, blockAct_one, AlgHom.id_apply] at h1
    rw [smul_zero, coe_jetOp _ _ _ _ _ hmem, h1]
    rfl
  · refine ⟨(κ * detFac s s' B BW)⁻¹ • jetOp lam lam' J n F, ?_, ?_⟩
    · rw [GlobalTheory.HAtBasis.mem_HAt_iff K w ι b lam' MW BW hMW]
      intro p
      obtain ⟨u, hu1, hu'⟩ := hu p
      rw [Submodule.coe_smul, coe_jetOp _ _ _ _ _ hmem, map_smul, coeff_smul, coeff_smul, hu', hfac, smul_eq_mul,
        smul_eq_mul]
      convert hu1 using 2
      field_simp
    · rw [smul_inv_smul₀]
      rw [hfac]
      exact mul_ne_zero hκ (mul_ne_zero hD0 hW0)

theorem pointIntegral : PointIntegral := by
  intro K _ _ w ι _ a b hab lam lam' s s' n hw M MW B BW hM hMW ap hap F hF
  have hσ : ∀ x : K, w.valuation K (RingHom.id K x) ≤ 1 ↔ w.valuation K x ≤ 1 := fun _ => Iff.rfl
  have hadm : admitted (w.valuation K) (RingHom.id K) M MW ap := by
    intro τ y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact (GlobalTheory.ExtLatMatrix.extLat_matrix_integral K w K _ (w.valuation K) (RingHom.id K) hσ).1 a (M τ) _ (hap τ x hx)
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  have h := closureIntegral K w K _ (w.valuation K) (RingHom.id K) hσ ι a b hab lam lam' s s' n hw M MW B BW hM hMW
    1 (ptTable ap) (fun _ _ => ⟨1, fun _ => 1, fun _ => ap, fun _ => by simp, fun _ => hadm, fun m _ => by simp⟩) F hF
  rwa [one_mul] at h

end Closure

theorem jetPointStatement : JetPointStatement :=
  ⟨substitution, GlobalTheory.DetIndexPf.detIndex, pointIntegral, closureIntegral⟩

end GlobalTheory.JetPoint
