import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BlockShape

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker.TE

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Chain

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem perm_of_cnt {κ : Type} [DecidableEq κ] {k : ℕ} (f l : Fin k → κ)
    (h : ∀ i, (Finset.univ.filter fun j => f j = i).card = (Finset.univ.filter fun j => l j = i).card) :
    ∃ σ : Equiv.Perm (Fin k), f = l ∘ σ := by
  have e : ∀ c, {a // f a = c} ≃ {b // l b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

theorem cnt_toList {κ : Type} [DecidableEq κ] (α : κ →₀ ℕ) (i : κ) :
    (Finset.univ.filter fun j : Fin (Multiset.card α.toMultiset) =>
      α.toMultiset.toList.get ⟨j, by simpa using j.2⟩ = i).card = α i := by
  set l := fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩
  have hmap : Multiset.map l Finset.univ.val = α.toMultiset := by
    rw [Fin.univ_val_map]
    have : List.ofFn l = α.toMultiset.toList := by
      refine List.ext_get (by simp) ?_
      intro n h1 h2
      simp [l]
    rw [this, Multiset.coe_toList]
  have h := congrArg (Multiset.count i) hmap
  rw [Multiset.count_map, Finsupp.count_toMultiset] at h
  rw [← h, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => eq_comm

open Classical in

theorem iter_eq_derivAt0 (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G) (m : DVar ι a b →₀ ℕ) (k : ℕ) (hk : k = Multiset.card m.toMultiset)
    (r : Fin k → DVar ι a b) (hr : ∀ i, (Finset.univ.filter fun j => r j = i).card = m i) :
    iteratedFDeriv ℂ k G 0 (fun j => coordX (r j)) = derivAt0 G m := by
  subst hk
  obtain ⟨σ, hσ⟩ := perm_of_cnt r (fun j => m.toMultiset.toList.get ⟨j, by simpa using j.2⟩)
    (fun i => (hr i).trans (cnt_toList m i).symm)
  unfold derivAt0
  have h := (hG.contDiffAt (x := 0)).iteratedFDeriv_comp_perm
    (fun i : Fin (Multiset.card m.toMultiset) => (coordX (m.toMultiset.toList.get ⟨i, by simpa using i.2⟩) : VCx ι a b)) σ
  rw [← h]
  congr 1
  funext j
  rw [hσ]
  rfl

theorem atZero_prodX (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G) {k : ℕ} (r : Fin k → DVar ι a b) :
    atZero G (∏ j, X (r j)) = iteratedFDeriv ℂ k G 0 (fun j => coordX (r j)) := by
  classical
  have h1 : (∏ j, X (r j) : MvPolynomial (DVar ι a b) ℂ) = monomial (∑ j, Finsupp.single (r j) 1) 1 :=
    (monomial_sum_one Finset.univ fun j => Finsupp.single (r j) 1).symm
  rw [h1, atZero_monomial, one_mul]
  symm
  refine iter_eq_derivAt0 G hG _ k ?_ r ?_
  · rw [map_sum]
    simp [Finsupp.toMultiset_single, Multiset.card_sum]
  · intro i
    rw [Finsupp.finsetSum_apply, Finset.card_filter]
    simp only [Finsupp.single_apply]

theorem atZero_comp_prodX {κ : Type} [Fintype κ] (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G) (L : VCx ι a b →ₗ[ℂ] VCx ι a b)
    (c : DVar ι a b → κ → ℂ) (e : DVar ι a b → κ → DVar ι a b) (hL : ∀ k, L (coordX k) = ∑ p, c k p • coordX (e k p))
    {k : ℕ} (r : Fin k → DVar ι a b) :
    atZero (fun z => G (L z)) (∏ j, X (r j)) = atZero G (∏ j, ∑ p, C (c (r j) p) * X (e (r j) p)) := by
  classical
  have hGL : ContDiff ℂ ⊤ (fun z => G (L z)) := hG.comp (LinearMap.toContinuousLinearMap L).contDiff
  rw [atZero_prodX _ hGL]
  have h : (fun z => G (L z)) = G ∘ (LinearMap.toContinuousLinearMap L) := by
    funext z; simp
  rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hG _ le_top]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, LinearMap.coe_toContinuousLinearMap', hL]
  rw [ContinuousMultilinearMap.map_sum, Finset.prod_univ_sum, map_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_mul_distrib, ← map_prod, C_mul', map_smul, atZero_prodX G hG]

theorem exists_prodX {κ : Type} (m : κ →₀ ℕ) : ∃ (k : ℕ) (r : Fin k → κ), (monomial m 1 : MvPolynomial κ ℂ) = ∏ j, X (r j) := by
  classical
  have hl : ∃ l : List κ, (monomial m 1 : MvPolynomial κ ℂ) = (l.map X).prod := by
    induction m using Finsupp.induction with
    | zero => exact ⟨[], by simp⟩
    | single_add x n f _ _ ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨List.replicate n x ++ l, ?_⟩
      rw [monomial_single_add, hl]
      simp
  obtain ⟨l, hl⟩ := hl
  refine ⟨l.length, fun j => l.get j, ?_⟩
  rw [hl, ← List.prod_ofFn]
  congr 1
  refine List.ext_get (by simp) ?_
  intro n h1 h2
  simp

theorem atZero_comp {κ : Type} [Fintype κ] (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G) (L : VCx ι a b →ₗ[ℂ] VCx ι a b)
    (c : DVar ι a b → κ → ℂ) (e : DVar ι a b → κ → DVar ι a b) (hL : ∀ k, L (coordX k) = ∑ p, c k p • coordX (e k p))
    (P : MvPolynomial (DVar ι a b) ℂ) :
    atZero (fun z => G (L z)) P = atZero G (aeval (fun k => ∑ p, C (c k p) * X (e k p)) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m x =>
    obtain ⟨k, r, hr⟩ := exists_prodX m
    have h : (monomial m x : MvPolynomial (DVar ι a b) ℂ) = x • ∏ j, X (r j) := by
      rw [← hr, smul_monomial, smul_eq_mul, mul_one]
    have h2 : aeval (fun k => ∑ p, C (c k p) * X (e k p)) (∏ j, X (r j) : MvPolynomial (DVar ι a b) ℂ) =
        ∏ j, ∑ p, (C (c (r j) p) * X (e (r j) p) : MvPolynomial (DVar ι a b) ℂ) := by
      rw [map_prod]
      simp only [aeval_X]
    rw [h, map_smul, map_smul, map_smul, h2, atZero_comp_prodX G hG L c e hL r]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

end Chain

section Pull

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetLin_smul (κ : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (fun m => κ * J m) = κ • jetLin J := by
  apply (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext
  intro m
  simp only [coe_basisMonomials, jetLin_monomial, one_mul, LinearMap.smul_apply, smul_monomial, smul_eq_mul]

theorem eval_blockAct {n : ℕ} (h : ι → Matrix (Fin n) (Fin n) K) (y : ι × Fin n × Fin n → K) (R : Pol K ι n) :
    eval y (Formalism.GradedWeylDivisibility.blockAct K h R) = eval (fun v => ∑ β, h v.1 v.2.1 β * y (v.1, β, v.2.2)) R := by
  induction R using MvPolynomial.induction_on with
  | C c => simp [Formalism.GradedWeylDivisibility.blockAct]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, eval_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.blockAct]

theorem map_blockAct {L : Type} [Field L] (σ : K →+* L) {n : ℕ} (h : ι → Matrix (Fin n) (Fin n) K) (R : Pol K ι n) :
    MvPolynomial.map σ (Formalism.GradedWeylDivisibility.blockAct K h R) = Formalism.GradedWeylDivisibility.blockAct L (fun τ => (h τ).map σ) (MvPolynomial.map σ R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp [Formalism.GradedWeylDivisibility.blockAct]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.blockAct]

theorem blockAct_frDet (g : ι → Matrix (Fin a) (Fin a) K) (τ : ι) :
    Formalism.GradedWeylDivisibility.blockAct K g (frDet K a τ) = C (g τ).det * frDet K a τ := by
  unfold frDet
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext α s
  simp [Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]

def subC (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) :
    MvPolynomial (DVar ι a b) ℂ →ₐ[ℂ] MvPolynomial (DVar ι a b) ℂ :=
  aeval fun k => ∑ p : Fin b × Fin a, C (h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2) * X ((k.1, p.1, p.2) : DVar ι a b)

theorem subC_polDx (cD : ι → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (y' : ι × Fin b × Fin b → ℂ) :
    (subC g h).comp (polDx (a := a) cD y') =
      (polDx (a := a) cD fun v => ∑ β, h v.1 v.2.1 β * y' (v.1, β, v.2.2)).comp (Formalism.GradedWeylDivisibility.blockAct ℂ g) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, α, s⟩
  simp only [AlgHom.comp_apply, polDx, subC, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq]
  by_cases hs : s.1 < b
  · simp only [dif_pos hs, Fintype.sum_prod_type, Finset.mul_sum]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, k]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  · simp only [dif_neg hs, mul_zero, map_zero, zero_mul, Finset.sum_const_zero]

theorem atZero_subC (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G) (L : VCx ι a b →ₗ[ℂ] VCx ι a b)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ)
    (hL : ∀ k : DVar ι a b, L (coordX k) =
      ∑ p : Fin b × Fin a, (h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2) • coordX ((k.1, p.1, p.2) : DVar ι a b))
    (P : MvPolynomial (DVar ι a b) ℂ) : atZero (fun z => G (L z)) P = atZero G (subC g h P) := by
  have h0 := atZero_comp (κ := Fin b × Fin a) G hG L (fun k p => h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2)
    (fun k p => ((k.1, p.1, p.2) : DVar ι a b)) hL P
  unfold subC
  exact h0

theorem eval_map_jetMap (σ : K →+* ℂ) (cD : ι → ℂ) (n : ι → ℕ) (J₀ : (DVar ι a b →₀ ℕ) → K) (κ₀ : ℂ) (G₀ : VCx ι a b → ℂ)
    (h₀ : ∀ m, σ (J₀ m) = κ₀ * jetC cD G₀ m) (Q : Pol K ι a) (y : ι × Fin b × Fin b → ℂ) :
    eval y (MvPolynomial.map σ (jetMap J₀ n Q)) =
      κ₀ * atZero G₀ (polDx cD y (MvPolynomial.map σ Q * ∏ τ, frDet ℂ a τ ^ n τ)) := by
  rw [Shape.map_jetMap, funext h₀, jetLin_smul, LinearMap.smul_apply, smul_eval, eval_jetLin, ← evY_subD]
  rfl

theorem jetMap_pull (σ : K →+* ℂ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G)
    (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K) (L : VCx ι a b →ₗ[ℂ] VCx ι a b)
    (hL : ∀ k : DVar ι a b, L (coordX k) =
      ∑ p : Fin b × Fin a, (σ (h k.1 p.1 k.2.1) * σ (g k.1 k.2.2 p.2)) • coordX ((k.1, p.1, p.2) : DVar ι a b))
    (J J' : (DVar ι a b →₀ ℕ) → K) (κ κ' : ℂ) (hJ : ∀ m, σ (J m) = κ * jetC cD G m)
    (hJ' : ∀ m, σ (J' m) = κ' * jetC cD (fun z => G (L z)) m) (r : K) (hr : κ' = σ r * κ) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J' n P = (r * ∏ τ, (g τ).det ^ n τ) • Formalism.GradedWeylDivisibility.blockAct K h (jetMap J n (Formalism.GradedWeylDivisibility.blockAct K g P)) := by
  apply MvPolynomial.map_injective σ σ.injective
  apply MvPolynomial.funext
  intro y'
  obtain ⟨gc, hgc⟩ : ∃ gc : ι → Matrix (Fin a) (Fin a) ℂ, gc = fun τ => (g τ).map σ := ⟨_, rfl⟩
  obtain ⟨hc, hhc⟩ : ∃ hc : ι → Matrix (Fin b) (Fin b) ℂ, hc = fun τ => (h τ).map σ := ⟨_, rfl⟩
  have hL' : ∀ k : DVar ι a b, L (coordX k) =
      ∑ p : Fin b × Fin a, (hc k.1 p.1 k.2.1 * gc k.1 k.2.2 p.2) • coordX ((k.1, p.1, p.2) : DVar ι a b) := by
    intro k
    rw [hL k, hgc, hhc]
    simp only [Matrix.map_apply]
  have e1 : ∀ T : Pol K ι a, MvPolynomial.map σ (Formalism.GradedWeylDivisibility.blockAct K g T) = Formalism.GradedWeylDivisibility.blockAct ℂ gc (MvPolynomial.map σ T) := by
    intro T
    rw [map_blockAct, hgc]
  have e2 : ∀ T : Pol K ι b, MvPolynomial.map σ (Formalism.GradedWeylDivisibility.blockAct K h T) = Formalism.GradedWeylDivisibility.blockAct ℂ hc (MvPolynomial.map σ T) := by
    intro T
    rw [map_blockAct, hhc]
  have hdet : ∀ τ, (gc τ).det = σ (g τ).det := by
    intro τ
    rw [hgc, RingHom.map_det]
    rfl
  have hR : ∀ (x : K) (T : Pol K ι b), eval y' (MvPolynomial.map σ (x • T)) = σ x * eval y' (MvPolynomial.map σ T) := by
    intro x T
    rw [smul_eq_C_mul, map_mul, map_C, map_mul, eval_C]
  have h2 : Formalism.GradedWeylDivisibility.blockAct ℂ gc (MvPolynomial.map σ P * ∏ τ, frDet ℂ a τ ^ n τ) =
      (∏ τ, (gc τ).det ^ n τ) • (Formalism.GradedWeylDivisibility.blockAct ℂ gc (MvPolynomial.map σ P) * ∏ τ, frDet ℂ a τ ^ n τ) := by
    rw [← C_mul', map_mul, map_prod]
    simp only [map_pow, blockAct_frDet, mul_pow, Finset.prod_mul_distrib, map_prod]
    ring
  have h1 := AlgHom.congr_fun (subC_polDx cD gc hc y') (MvPolynomial.map σ P * ∏ τ, frDet ℂ a τ ^ n τ)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h2, map_smul] at h1
  rw [hR, e2, eval_blockAct, eval_map_jetMap σ cD n J κ G hJ, e1, eval_map_jetMap σ cD n J' κ' _ hJ' P y',
    atZero_subC G hG L gc hc hL', h1, map_smul, smul_eq_mul, hr]
  have h3 : σ (r * ∏ τ, (g τ).det ^ n τ) = σ r * ∏ τ, (gc τ).det ^ n τ := by
    rw [map_mul, map_prod]
    simp only [map_pow, hdet]
  rw [h3]
  ring

end Pull

section MulL

variable {ι : Type} [Fintype ι] {a b : ℕ}

def mulL (h : ι → Matrix (Fin b) (Fin b) ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : VCx ι a b →ₗ[ℂ] VCx ι a b where
  toFun z := fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j
  map_add' z w := by
    funext τ i j
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring

theorem mulL_apply (h : ι → Matrix (Fin b) (Fin b) ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : VCx ι a b) (τ : ι) (i : Fin b) (j : Fin a) :
    mulL h g z τ i j = ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j := rfl

theorem mulL_coordX (h : ι → Matrix (Fin b) (Fin b) ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (k : DVar ι a b) :
    mulL h g (coordX k) = ∑ p : Fin b × Fin a, (h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2) • coordX ((k.1, p.1, p.2) : DVar ι a b) := by
  funext τ i j
  rw [mulL_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordX]
  by_cases hτ : τ = k.1
  · rw [← Finset.sum_product', Finset.sum_eq_single (k.2.1, k.2.2), Finset.sum_eq_single (i, j)]
    · rw [if_pos ⟨hτ, rfl, rfl⟩, if_pos ⟨hτ, rfl, rfl⟩, hτ]
      ring
    · intro p _ hp
      rw [if_neg (fun hh => hp (Prod.ext hh.2.1.symm hh.2.2.symm)), mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
    · intro p _ hp
      rw [if_neg (fun hh => hp (Prod.ext hh.2.1 hh.2.2)), mul_zero, zero_mul]
    · intro hh
      exact absurd (Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩) hh
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro p _
      rw [if_neg (fun hh => hτ hh.1), mul_zero]
    · intro k' _
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (fun hh => hτ hh.1), mul_zero, zero_mul]

end MulL

end Formalism.L2.Ker.TE
