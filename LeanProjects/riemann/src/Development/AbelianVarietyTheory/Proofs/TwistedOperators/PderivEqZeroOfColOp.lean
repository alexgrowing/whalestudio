import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.JointHarm

section Pair

variable {σ : Type} {k l n : ℕ}

def harmSub (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {P | ∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0}
  add_mem' := fun ha hb i j => by simp only [map_add, Finset.sum_add_distrib, ha i j, hb i j, add_zero]
  zero_mem' := fun i j => by simp
  smul_mem' := fun c _ ha i j => by
    simp only [Derivation.map_smul, ← Finset.smul_sum, ha i j, smul_zero]

theorem pderiv_pderiv_polar [DecidableEq σ] (u v a b : σ) (P : MvPolynomial σ ℂ) :
    pderiv u (pderiv v (X a * pderiv b P)) = X a * pderiv b (pderiv u (pderiv v P)) +
      (if u = a then pderiv b (pderiv v P) else 0) +
      (if v = a then pderiv u (pderiv b P) else 0) := by
  rw [pderiv_X_mul', map_add, pderiv_X_mul', pderiv_swap v b, pderiv_swap u b]
  split_ifs <;> simp [pderiv_swap u b]

theorem lap_colOp [DecidableEq σ] (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) {I J : Type}
    [Fintype I] (x : I × J → σ) (a b : J) {P : MvPolynomial σ ℂ} (hP : P ∈ harmSub z y) (i j) :
    ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) (colOp ℂ x a b P)) =
      ∑ t, ∑ c, (if z (i, t) = x (c, a) then pderiv (x (c, b)) (pderiv (y (j, t)) P) else 0) +
      ∑ t, ∑ c, (if y (j, t) = x (c, a) then pderiv (z (i, t)) (pderiv (x (c, b)) P) else 0) := by
  simp only [colOp_apply, map_sum, pderiv_pderiv_polar, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← map_sum, hP i j]
  simp

theorem harmSub_mixedOp {z : Fin k × Fin n → σ} {y : Fin l × Fin n → σ}
    (hz : Function.Injective z) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (a b : Fin n) {P : MvPolynomial σ ℂ} (hP : P ∈ harmSub z y) :
    mixedOp ℂ z y a b P ∈ harmSub z y := by
  classical
  intro i j
  simp only [mixedOp, LinearMap.sub_apply, map_sub, Finset.sum_sub_distrib, lap_colOp z y _ _ _ hP,
    hz.eq_iff, hy.eq_iff, hzy, (hzy _ _).symm, Prod.mk.injEq, ite_and]
  simp

theorem harmSub_mixedOp' {z : Fin k × Fin n → σ} {y : Fin l × Fin n → σ} {k' l' n' : ℕ}
    {z' : Fin k' × Fin n' → σ} {y' : Fin l' × Fin n' → σ}
    (h1 : ∀ u w, z u ≠ z' w) (h2 : ∀ u w, z u ≠ y' w) (h3 : ∀ u w, y u ≠ z' w)
    (h4 : ∀ u w, y u ≠ y' w)
    (a b : Fin n') {P : MvPolynomial σ ℂ} (hP : P ∈ harmSub z y) :
    mixedOp ℂ z' y' a b P ∈ harmSub z y := by
  classical
  intro i j
  simp [mixedOp, lap_colOp z y _ _ _ hP, h1, h2, h3, h4]

def Sep (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) (A B : Fin n → ℕ)
    (P : MvPolynomial σ ℂ) : Prop :=
  (∀ t, colOp ℂ z t t P = (A t : ℂ) • P) ∧ (∀ t, colOp ℂ y t t P = (B t : ℂ) • P) ∧
    (∀ i j, i < j → colOp ℂ z i j P = 0) ∧ ∀ i j, i < j → colOp ℂ y j i P = 0

theorem sep_of_degrees {z : Fin k × Fin n → σ} {y : Fin l × Fin n → σ}
    (hz : Function.Injective z) (hzy : ∀ u w, z u ≠ y w) {A B : Fin n → ℕ} {P : MvPolynomial σ ℂ}
    (hA : ∀ m ∈ P.support, ∀ t, ∑ i, m (z (i, t)) = A t)
    (hB : ∀ m ∈ P.support, ∀ t, ∑ i, m (y (i, t)) = B t)
    (hup : ∀ i j, i < j → mixedOp ℂ z y i j P = 0) : Sep z y A B P := by
  have h1 : ∀ t, colOp ℂ z t t P = (A t : ℂ) • P := fun t =>
    (colOp_eq_smul_iff z t P _).2 fun m hm => by rw [hA m hm]
  have key : ∀ i j, i < j → colOp ℂ z i j P = 0 ∧ colOp ℂ y j i P = 0 := by
    intro i j hij
    have e : colOp ℂ z i j P = colOp ℂ y j i P := sub_eq_zero.1 (hup i j hij)
    have e1 := LinearMap.congr_fun (colOp_lie (K := ℂ) z hz i i i j) P
    have e2 := LinearMap.congr_fun (commute_colOp_colOp (K := ℂ) z y hzy i i j i).eq P
    simp only [if_neg hij.ne', if_true, sub_zero, LinearMap.sub_apply, Module.End.mul_apply, h1,
      map_smul] at e1 e2
    rw [← e] at e2
    rw [e2, sub_self] at e1
    exact ⟨e1.symm, e.symm.trans e1.symm⟩
  exact ⟨h1, fun t => (colOp_eq_smul_iff y t P _).2 fun m hm => by rw [hB m hm],
    fun i j h => (key i j h).1, fun i j h => (key i j h).2⟩

theorem pderiv_eq_zero_of_colOp {I J : Type} [Fintype I] (z : I × J → σ) (t : J)
    {P : MvPolynomial σ ℂ} (h : colOp ℂ z t t P = ((0 : ℕ) : ℂ) • P) (i : I) :
    pderiv (z (i, t)) P = 0 := by
  classical
  refine pderiv_eq_zero_of_notMem_vars fun hv => ?_
  obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
  have := (colOp_eq_smul_iff z t P _).1 h m hm
  rw [Nat.cast_inj, Finset.sum_eq_zero_iff] at this
  exact Finsupp.mem_support_iff.1 hv (this i (Finset.mem_univ _))

theorem Sep.mixed {z : Fin k × Fin n → σ} {y : Fin l × Fin n → σ} {A B : Fin n → ℕ}
    {P : MvPolynomial σ ℂ} (h : Sep z y A B P) (hAB : ∀ t, A t = 0 ∨ B t = 0) :
    P ∈ harmSub z y ∧ (∀ i j, i < j → mixedOp ℂ z y i j P = 0) ∧
      ∀ t, mixedOp ℂ z y t t P = ((A t : ℂ) - B t) • P := by
  refine ⟨fun i j => Finset.sum_eq_zero fun t _ => ?_, fun i j hij => ?_, fun t => ?_⟩
  · rcases hAB t with e | e
    · rw [pderiv_swap, pderiv_eq_zero_of_colOp z t (e ▸ h.1 t), map_zero]
    · rw [pderiv_eq_zero_of_colOp y t (e ▸ h.2.1 t), map_zero]
  · rw [mixedOp, LinearMap.sub_apply, h.2.2.1 i j hij, h.2.2.2 i j hij, sub_zero]
  · rw [mixedOp, LinearMap.sub_apply, h.1, h.2.1, sub_smul]

theorem mixed_weight (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) {P : MvPolynomial σ ℂ}
    {t : Fin n} {w : ℚ} (h : mixedOp ℂ z y t t P = (w : ℂ) • P) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    w = ((∑ i, m (z (i, t)) : ℕ) : ℚ) - (∑ j, m (y (j, t)) : ℕ) := by
  have := congrArg (coeff m) h
  rw [mixedOp_apply, coeff_sub, coeff_sum, coeff_sum, coeff_smul] at this
  simp only [GlobalTheory.Harm.HighestUnique.coeff_X_mul_pderiv, ← Finset.sum_mul, ← sub_mul,
    smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hm) this
  exact_mod_cast h2.symm

theorem mixed_diag (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) :
    ⨆ κ : Fin n → ℤ, (⨅ i, Module.End.eigenspace (mixedOp ℂ z y i i) (κ i : ℂ)) = ⊤ :=
  iSup_eigenspace_eq_top _ (fun m t => ∑ a, (m (z (a, t)) : ℤ) - ∑ a, (m (y (a, t)) : ℤ))
    fun m t => by
      rw [mixedOp, LinearMap.sub_apply, colOp_monomial, colOp_monomial, ← sub_smul, Int.cast_sub]

end Pair

section Side

variable {σ : Type} {p q r s : ℕ}

def zA (e : Ln p q r s → σ) : Fin r × Fin p → σ := fun w => e (.inl w.2, .inl w.1)

def zB (e : Ln p q r s → σ) : Fin s × Fin p → σ := fun w => e (.inl w.2, .inr w.1)

def zC (e : Ln p q r s → σ) : Fin s × Fin q → σ := fun w => e (.inr w.2, .inr w.1)

def zD (e : Ln p q r s → σ) : Fin r × Fin q → σ := fun w => e (.inr w.2, .inl w.1)

variable {e : Ln p q r s → σ} (he : Function.Injective e)
include he

theorem zA_inj : Function.Injective (zA e) := fun u w h => by
  simpa [Prod.ext_iff, and_comm] using he h
theorem zB_inj : Function.Injective (zB e) := fun u w h => by
  simpa [Prod.ext_iff, and_comm] using he h
theorem zC_inj : Function.Injective (zC e) := fun u w h => by
  simpa [Prod.ext_iff, and_comm] using he h
theorem zD_inj : Function.Injective (zD e) := fun u w h => by
  simpa [Prod.ext_iff, and_comm] using he h
theorem zAB (u w) : zA e u ≠ zB e w := fun h => by simpa using he h
theorem zAC (u w) : zA e u ≠ zC e w := fun h => by simpa using he h
theorem zAD (u w) : zA e u ≠ zD e w := fun h => by simpa using he h
theorem zBC (u w) : zB e u ≠ zC e w := fun h => by simpa using he h
theorem zBD (u w) : zB e u ≠ zD e w := fun h => by simpa using he h
theorem zCD (u w) : zC e u ≠ zD e w := fun h => by simpa using he h

omit he

def IsSide (e : Ln p q r s → σ) (act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  (∀ a b P, act (Eab (.inl a) (.inl b)) P =
    mixedOp ℂ (zA e) (zB e) a b P + (if a = b then (cPair r s : ℂ) else 0) • P) ∧
  (∀ a b P, act (Eab (.inr a) (.inr b)) P =
    mixedOp ℂ (zC e) (zD e) a b P - (if a = b then (cPair r s : ℂ) else 0) • P)

theorem omE_pos_pos {l l' : Ln p q r s} (h : linePos l = true) (h' : linePos l' = true)
    (P : Pol p q r s) : omE l l' P = X l * pderiv l' P + (if l = l' then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, h, h', if_true]
  split_ifs <;> simp

theorem omE_neg_neg {l l' : Ln p q r s} (h : linePos l = false) (h' : linePos l' = false)
    (P : Pol p q r s) :
    omE l l' P = -(X l' * pderiv l P) - (if l = l' then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, h, h', Bool.false_eq_true, if_false]
  rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pderiv_X_mul']
  split_ifs
  · simp only [LinearMap.smul_apply, Module.End.one_apply]; module
  · simp

theorem isSide_one : IsSide (id : Ln p q r s → Ln p q r s) (fockAct1 p q r s) := by
  constructor <;> intro a b P <;>
    rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, mixedOp_apply]
  · simp only [omE_pos_pos (l := (.inl a, .inl _)) (l' := (.inl b, .inl _)) rfl rfl,
      omE_neg_neg (l := (.inl a, .inr _)) (l' := (.inl b, .inr _)) rfl rfl, zA, zB, id,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
    by_cases h : a = b <;> simp [h, cPair] <;> module
  · simp only [omE_pos_pos (l := (.inr a, .inr _)) (l' := (.inr b, .inr _)) rfl rfl,
      omE_neg_neg (l := (.inr a, .inl _)) (l' := (.inr b, .inl _)) rfl rfl, zC, zD, id,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
    by_cases h : a = b <;> simp [h, cPair] <;> module

theorem isSide_two : IsSide (Prod.swap : Ln r s p q → Ln p q r s) (fockAct2 p q r s) := by
  constructor <;> intro a b P <;>
    rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, mixedOp_apply]
  · simp only [omE_pos_pos (l := (.inl _, .inl a)) (l' := (.inl _, .inl b)) rfl rfl,
      omE_neg_neg (l := (.inr _, .inl a)) (l' := (.inr _, .inl b)) rfl rfl, zA, zB, Prod.swap,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
    by_cases h : a = b <;> simp [h, cPair] <;> module
  · simp only [omE_pos_pos (l := (.inr _, .inr a)) (l' := (.inr _, .inr b)) rfl rfl,
      omE_neg_neg (l := (.inl _, .inr a)) (l' := (.inl _, .inr b)) rfl rfl, zC, zD, Prod.swap,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
    by_cases h : a = b <;> simp [h, cPair] <;> module

variable {act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}

theorem IsSide.mem_wtSub (h : IsSide e act) (μ : Ix p q → ℚ) (P : MvPolynomial σ ℂ) :
    P ∈ wtSub act μ ↔
      (∀ a, mixedOp ℂ (zA e) (zB e) a a P = (shiftNu (cPair r s) μ (.inl a) : ℂ) • P) ∧
      ∀ a, mixedOp ℂ (zC e) (zD e) a a P = (shiftNu (cPair r s) μ (.inr a) : ℂ) • P := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Sum.forall, h.1, h.2, if_true, shiftNu, Rat.cast_sub,
    Rat.cast_add, sub_smul, add_smul, sub_eq_zero, eq_sub_iff_add_eq, sub_eq_iff_eq_add, zero_add]

theorem IsSide.mem_hwSub (h : IsSide e act) (μ : Ix p q → ℚ) (P : MvPolynomial σ ℂ) :
    P ∈ hwSub act μ ↔ P ∈ wtSub act μ ∧
      (∀ a b, a < b → mixedOp ℂ (zA e) (zB e) a b P = 0) ∧
      ∀ a b, a < b → mixedOp ℂ (zC e) (zD e) a b P = 0 := by
  simp only [hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall, posC,
    h.1, h.2, IsEmpty.forall_iff, implies_true, and_true, true_and, forall_and]
  refine and_congr_right fun _ => and_congr ?_ ?_ <;>
    exact forall₃_congr fun a b hab => by simp [hab.ne]

theorem degree_eq_blocks [Fintype σ] (he : Function.Bijective e) (m : σ →₀ ℕ) :
    m.degree = ∑ t, (∑ i, m (zA e (i, t)) + ∑ i, m (zB e (i, t))) +
      ∑ t, (∑ i, m (zC e (i, t)) + ∑ i, m (zD e (i, t))) := by
  rw [Finsupp.degree_eq_sum, ← he.sum_comp, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, zA, zB, zC, zD, add_comm]

theorem IsSide.degW_le [Fintype σ] (he : Function.Bijective e) (h : IsSide e act) {d : ℕ}
    {μ : Ix p q → ℚ} {P : MvPolynomial σ ℂ} (hd : P ∈ homog σ d) (hP : IsHW act μ P) :
    degW (cPair r s) μ ≤ d := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hP.1
  obtain ⟨h1, h2⟩ := (h.mem_wtSub μ P).1 hP.2.1
  have e1 : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (mem_support_iff.1 hm)
  rw [← e1, degree_eq_blocks he, degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum,
    Nat.cast_sum]
  refine add_le_add (Finset.sum_le_sum fun t _ => ?_) (Finset.sum_le_sum fun t _ => ?_)
  · rw [mixed_weight _ _ (h1 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])
  · rw [mixed_weight _ _ (h2 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])

theorem lowering_iff (e : Ln p q r s → σ) (P : MvPolynomial σ ℂ) :
    (∀ Z : Mat r s, IsPC Z → (∑ a, ∑ c, ∑ d, if linePos ((a, c) : Ln p q r s) then 0 else
      -Z c d • pderiv (e (a, c)) (pderiv (e (a, d)) P)) = 0) ↔
    P ∈ harmSub (zA e) (zB e) ⊓ harmSub (zC e) (zD e) := by
  have key : ∀ (c₀ d₀ : Ix r s) (F : Ix p q → Ix r s → Ix r s → MvPolynomial σ ℂ),
      (∑ a, ∑ c, ∑ d, if linePos ((a, c) : Ln p q r s) then 0 else -Eab c₀ d₀ c d • F a c d) =
        -∑ a, if linePos ((a, c₀) : Ln p q r s) then 0 else F a c₀ d₀ := by
    intro c₀ d₀ F
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c₀, Finset.sum_eq_single d₀]
    · split_ifs <;> simp [Eab]
    · intro d _ hd; simp [Eab, Matrix.single_apply, hd.symm]
    · simp
    · intro c _ hc; simp [Eab, Matrix.single_apply, hc.symm]
    · simp
  have pc : ∀ c₀ d₀ : Ix r s, ¬ sameBlock c₀ d₀ → IsPC (Eab c₀ d₀) := by
    intro c₀ d₀ h a b hab
    rw [Eab, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h hab
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have := h _ (pc (.inr j) (.inl i) id)
      rw [key, neg_eq_zero, Fintype.sum_sum_type] at this
      simp only [linePos, if_true, Bool.false_eq_true, if_false, Finset.sum_const_zero,
        add_zero] at this
      exact (Finset.sum_congr rfl fun _ _ => pderiv_swap _ _ _).trans this
    · have := h _ (pc (.inl j) (.inr i) id)
      rw [key, neg_eq_zero, Fintype.sum_sum_type] at this
      simp only [linePos, if_true, Bool.false_eq_true, if_false, Finset.sum_const_zero,
        zero_add] at this
      exact (Finset.sum_congr rfl fun _ _ => pderiv_swap _ _ _).trans this
  · rintro ⟨h1, h2⟩ Z hZ
    have z1 : ∀ c d, Z (.inl c) (.inl d) = 0 := fun c d => hZ _ _ trivial
    have z2 : ∀ c d, Z (.inr c) (.inr d) = 0 := fun c d => hZ _ _ trivial
    have g1 : ∀ c d, ∑ a : Fin p, pderiv (e (.inl a, .inr c)) (pderiv (e (.inl a, .inl d)) P) = 0 :=
      fun c d => (Finset.sum_congr rfl fun _ _ => pderiv_swap _ _ _).trans (h1 d c)
    have g2 : ∀ c d, ∑ a : Fin q, pderiv (e (.inr a, .inl c)) (pderiv (e (.inr a, .inr d)) P) = 0 :=
      fun c d => (Finset.sum_congr rfl fun _ _ => pderiv_swap _ _ _).trans (h2 d c)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rcases c with c | c <;> rcases d with d | d <;>
      simp [linePos, z1, z2, ← Finset.smul_sum, g1, g2]

theorem mem_harm1 (P : Pol p q r s) : (∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0) ↔
    P ∈ harmSub (zA id) (zB id) ⊓ harmSub (zC id) (zD id) := by
  rw [← lowering_iff]
  exact forall₂_congr fun Z hZ => by rw [minusPart_fockAct2_offDiagonal hZ]; rfl

theorem mem_harm2 (P : Pol p q r s) : (∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) P = 0) ↔
    P ∈ harmSub (zA Prod.swap) (zB Prod.swap) ⊓ harmSub (zC Prod.swap) (zD Prod.swap) := by
  rw [← lowering_iff]
  exact forall₂_congr fun Z hZ => by rw [minusPart_fockAct1_offDiagonal hZ]; rfl

end Side

end GlobalTheory.JointHarm
