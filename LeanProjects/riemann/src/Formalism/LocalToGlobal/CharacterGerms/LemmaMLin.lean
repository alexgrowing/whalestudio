import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.FrobeniusBaseCase.BaseCaseFalseGeneral

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.BaseCaseIdentities (OrdGE NoConst)

section General

variable {C : Type*} [Field C] {σ τ : Type*}

theorem ordGE_one_iff (f : MvPowerSeries τ C) : OrdGE 1 f ↔ constantCoeff f = 0 := by
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h A hA
    have hA0 : A = 0 := by
      have : A.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff A).1 this
    subst hA0
    simpa using h

theorem ordGE_zero (f : MvPowerSeries τ C) : OrdGE 0 f := fun _ h => absurd h (Nat.not_lt_zero _)

theorem ordGE_finset_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → MvPowerSeries τ C)
    (h : ∀ i ∈ s, OrdGE (n i) (f i)) : OrdGE (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using ordGE_zero (1 : MvPowerSeries τ C)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Formalism.BaseCaseIdentities.OrdGE.mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ordGE_finsupp_prod (a : σ → MvPowerSeries τ C) (ha : ∀ s, OrdGE 1 (a s)) (d : σ →₀ ℕ) :
    OrdGE d.degree (d.prod fun s n => a s ^ n) := by
  have h := ordGE_finset_prod d.support (fun s => d s) (fun s => a s ^ d s)
    (fun s _ => Formalism.BaseCaseIdentities.OrdGE.pow (ha s) (d s))
  exact h

theorem hasSubst_of_ordGE [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) :
    HasSubst a := hasSubst_of_constantCoeff_zero fun s => (ordGE_one_iff _).1 (ha s)

theorem coeff_subst_congr [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F G : MvPowerSeries σ C} {N : ℕ} (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G)
    (e : τ →₀ ℕ) (he : e.degree ≤ N) : coeff e (subst a F) = coeff e (subst a G) := by
  rw [coeff_subst (hasSubst_of_ordGE ha), coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree ≤ N
  · rw [h d hd]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero, smul_zero]

theorem ordGE_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE n F) : OrdGE n (subst a F) := by
  intro e he
  rw [coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d.degree < n
  · rw [hF d hd, zero_smul]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero]

def killV (P : σ → Prop) (F : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ w ∈ μ.support, P w then coeff μ F else 0

theorem coeff_killV (P : σ → Prop) (F : MvPowerSeries σ C) (μ : σ →₀ ℕ) :
    coeff μ (killV P F) = if ∀ w ∈ μ.support, P w then coeff μ F else 0 := rfl

theorem subst_kill [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (P : σ → Prop)
    (hP : ∀ w, ¬ P w → a w = 0) (F : MvPowerSeries σ C) :
    subst a (killV P F) = subst a F := by
  ext e
  rw [coeff_subst (hasSubst_of_ordGE ha), coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : ∀ w ∈ d.support, P w
  · rw [coeff_killV, if_pos hd]
  · simp only [not_forall] at hd
    obtain ⟨w, hw, hPw⟩ := hd
    have h0 : (d.prod fun s n => a s ^ n) = 0 := by
      refine Finset.prod_eq_zero hw ?_
      show a w ^ d w = 0
      rw [hP w hPw, zero_pow (Finsupp.mem_support_iff.1 hw)]
    rw [h0, map_zero, smul_zero, smul_zero]

theorem dVar_eq_pderiv {C : Type} [Field C] {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = pderiv C w F := by
  ext μ
  rw [coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem ordGE_pderiv {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE (n + 1) F) (w : σ) :
    OrdGE n (pderiv C w F) := by
  intro e he
  rw [coeff_pderiv, hF _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

theorem pderiv_subst_coe [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (b : τ)
    (p : MvPolynomial σ C) :
    pderiv C b (subst a (p : MvPowerSeries σ C)) =
      ∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C)) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.coe_C]
    have : subst a (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
      rw [← substAlgHom_apply ha]
      exact (substAlgHom ha).commutes r
    rw [this, pderiv_C]
    symm
    refine Finset.sum_eq_zero fun w _ => ?_
    have h0 : subst a (0 : MvPowerSeries σ C) = 0 := by
      rw [← substAlgHom_apply ha, map_zero]
    rw [pderiv_C, h0, mul_zero]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_add, subst_add ha, mul_add]
  | mul_X p w0 hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha, Derivation.leibniz, hp]
    have h1 : ∀ w, pderiv C b (a w) * subst a (pderiv C w ((p : MvPowerSeries σ C) * X w0)) =
        a w0 * (pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
          (if w = w0 then pderiv C b (a w0) * subst a (p : MvPowerSeries σ C) else 0) := by
      intro w
      rw [Derivation.leibniz, subst_add ha, smul_eq_mul, smul_eq_mul, subst_mul ha, subst_mul ha,
        subst_X ha]
      by_cases hw : w = w0
      · subst hw
        rw [pderiv_X_self, if_pos rfl]
        have : subst a (1 : MvPowerSeries σ C) = 1 := by
          rw [← substAlgHom_apply ha, map_one]
        rw [this]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hw), if_neg hw]
        have : subst a (0 : MvPowerSeries σ C) = 0 := by
          rw [← substAlgHom_apply ha, map_zero]
        rw [this]
        ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ w0, if_pos (Finset.mem_univ _),
      ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (b : τ)
    (H : MvPowerSeries σ C) :
    pderiv C b (subst a H) = ∑ w, pderiv C b (a w) * subst a (pderiv C w H) := by
  have hs := hasSubst_of_ordGE ha
  ext e
  obtain ⟨p, hp⟩ : ∃ p : MvPolynomial σ C, p = truncTotal (e.degree + 2) H := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : MvPowerSeries σ C, R = H - (p : MvPowerSeries σ C) := ⟨_, rfl⟩
  have hRo : OrdGE (e.degree + 2) R := by
    intro d hd
    rw [hR, map_sub, MvPolynomial.coeff_coe, hp, coeff_truncTotal _ hd, sub_self]
  have hH : H = (p : MvPowerSeries σ C) + R := by rw [hR]; ring
  have hL : coeff e (pderiv C b (subst a R)) = 0 :=
    ordGE_pderiv (n := e.degree + 1) (ordGE_subst ha hRo) b e (by omega)
  have hRr : coeff e (∑ w, pderiv C b (a w) * subst a (pderiv C w R)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have h1 : OrdGE (0 + (e.degree + 1)) (pderiv C b (a w) * subst a (pderiv C w R)) :=
      Formalism.BaseCaseIdentities.OrdGE.mul (ordGE_zero _) (ordGE_subst ha (ordGE_pderiv (n := e.degree + 1) hRo w))
    exact h1 e (by omega)
  have hsum : ∑ w, pderiv C b (a w) * subst a (pderiv C w H) =
      (∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
        ∑ w, pderiv C b (a w) * subst a (pderiv C w R) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hH, map_add, subst_add hs, mul_add]
  rw [hsum, map_add, hRr, add_zero, ← pderiv_subst_coe hs, hH, subst_add hs, map_add, map_add, hL,
    add_zero]

end General

section Lin

variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

def linS (M : τ → σ → C) : σ → MvPowerSeries τ C := fun w => ∑ c, M c w • (X c : MvPowerSeries τ C)

theorem ordGE_linS (M : τ → σ → C) (w : σ) : OrdGE 1 (linS M w) := by
  unfold linS
  refine Formalism.BaseCaseIdentities.OrdGE.sum _ fun c _ => ?_
  rw [smul_eq_C_mul]
  exact Formalism.BaseCaseIdentities.OrdGE.C_mul _ (Formalism.BaseCaseIdentities.OrdGE.X c)

theorem constantCoeff_linS (M : τ → σ → C) (w : σ) : constantCoeff (linS M w) = 0 :=
  (ordGE_one_iff _).1 (ordGE_linS M w)

theorem hasSubst_linS [Finite σ] (M : τ → σ → C) : HasSubst (linS M) :=
  hasSubst_of_ordGE (ordGE_linS M)

theorem subst_linS_add [Finite σ] (M : τ → σ → C) (F G : MvPowerSeries σ C) :
    subst (linS M) (F + G) = subst (linS M) F + subst (linS M) G := subst_add (hasSubst_linS M) F G

theorem subst_linS_sub [Finite σ] (M : τ → σ → C) (F G : MvPowerSeries σ C) :
    subst (linS M) (F - G) = subst (linS M) F - subst (linS M) G := subst_sub (hasSubst_linS M) F G

theorem subst_linS_mul [Finite σ] (M : τ → σ → C) (F G : MvPowerSeries σ C) :
    subst (linS M) (F * G) = subst (linS M) F * subst (linS M) G := subst_mul (hasSubst_linS M) F G

theorem subst_linS_pow [Finite σ] (M : τ → σ → C) (F : MvPowerSeries σ C) (n : ℕ) :
    subst (linS M) (F ^ n) = subst (linS M) F ^ n := subst_pow (hasSubst_linS M) F n

theorem subst_linS_smul [Finite σ] (M : τ → σ → C) (r : C) (F : MvPowerSeries σ C) :
    subst (linS M) (r • F) = r • subst (linS M) F := subst_smul (hasSubst_linS M) r F

theorem subst_linS_X [Finite σ] (M : τ → σ → C) (w : σ) :
    subst (linS M) (X w : MvPowerSeries σ C) = linS M w := subst_X (hasSubst_linS M) w

theorem subst_linS_sum [Finite σ] (M : τ → σ → C) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ C) :
    subst (linS M) (∑ i ∈ s, F i) = ∑ i ∈ s, subst (linS M) (F i) := by
  rw [← substAlgHom_apply (hasSubst_linS M), map_sum]
  simp only [substAlgHom_apply]

theorem subst_linS_neg [Finite σ] (M : τ → σ → C) (F : MvPowerSeries σ C) :
    subst (linS M) (-F) = -subst (linS M) F := by
  rw [← substAlgHom_apply (hasSubst_linS M), map_neg]
  simp only [substAlgHom_apply]

theorem subst_linS_C [Finite σ] (M : τ → σ → C) (r : C) :
    subst (linS M) (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
  rw [← substAlgHom_apply (hasSubst_linS M)]
  exact (substAlgHom (hasSubst_linS M)).commutes r

theorem ordGE_subst_linS [Finite σ] (M : τ → σ → C) {F : MvPowerSeries σ C} {n : ℕ}
    (hF : OrdGE n F) : OrdGE n (subst (linS M) F) := ordGE_subst (ordGE_linS M) hF

theorem coeff_subst_linS_congr [Finite σ] (M : τ → σ → C) {F G : MvPowerSeries σ C} {N : ℕ}
    (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G) (e : τ →₀ ℕ) (he : e.degree ≤ N) :
    coeff e (subst (linS M) F) = coeff e (subst (linS M) G) :=
  coeff_subst_congr (ordGE_linS M) h e he

theorem pderiv_linS (M : τ → σ → C) (b : τ) (w : σ) :
    pderiv C b (linS M w) = MvPowerSeries.C (M b w) := by
  unfold linS
  rw [map_sum, Finset.sum_eq_single b]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, pderiv_X_of_ne hc, smul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem pderiv_subst_linS [Fintype σ] (M : τ → σ → C) (b : τ) (H : MvPowerSeries σ C) :
    pderiv C b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (pderiv C w H) := by
  rw [pderiv_subst (ordGE_linS M)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pderiv_linS, smul_eq_C_mul]

theorem subst_linS_subst [Finite σ] {ρ : Type*} [Finite ρ] (M : τ → σ → C)
    {a : ρ → MvPowerSeries σ C} (ha : ∀ s, constantCoeff (a s) = 0) (γ : MvPowerSeries ρ C) :
    subst (linS M) (subst a γ) = subst (fun s => subst (linS M) (a s)) γ :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_linS M) γ

theorem subst_linS_kill [Finite σ] (M : τ → σ → C) (P : σ → Prop) (hP : ∀ w, ¬ P w → ∀ c, M c w = 0)
    (F : MvPowerSeries σ C) : subst (linS M) (killV P F) = subst (linS M) F := by
  refine subst_kill (ordGE_linS M) P (fun w hw => ?_) F
  unfold linS
  exact Finset.sum_eq_zero fun c _ => by rw [hP w hw c, zero_smul]

end Lin

theorem dVar_subst_linS {C : Type} [Field C] {σ τ : Type} [Fintype σ] [Fintype τ] (M : τ → σ → C)
    (b : τ) (H : MvPowerSeries σ C) :
    dVar b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (dVar w H) := by
  rw [dVar_eq_pderiv, pderiv_subst_linS]
  exact Finset.sum_congr rfl fun w _ => by rw [dVar_eq_pderiv]

section Rows

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem one_sub_ne (g : Fin 2) : 1 - g ≠ g := by revert g; decide

theorem finset_fin_two_eq_cases (g g' : Fin 2) : g' = g ∨ g' = 1 - g := by revert g g'; decide

theorem toW_same (g : Fin 2) (u : I g → C) (x : I g) : toW g u (⟨g, x⟩ : WV I) = u x := by
  simp [toW]

theorem toW_other (g g' : Fin 2) (h : g' ≠ g) (u : I g → C) (x : I g') :
    toW g u (⟨g', x⟩ : WV I) = 0 := by
  simp [toW, h]

def rowM (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) : ι ⊕ ι' → WV I → C :=
  Sum.elim (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))

theorem hPullW_eq (H : MvPowerSeries (WV I) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) :
    hPullW H (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = subst (linS (rowM g e v')) H := by
  unfold hPullW
  congr 1
  funext w
  unfold linS rowM
  rw [Fintype.sum_sum_type]
  rfl

theorem linS_rowM_self (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (x : I g) :
    linS (rowM g e v') (⟨g, x⟩ : WV I) =
      rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (linS e x) := by
  unfold linS rowM
  rw [Fintype.sum_sum_type, map_sum]
  have h2 : ∑ b : ι', (Sum.elim (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) (Sum.inr b)
      (⟨g, x⟩ : WV I)) • (X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Sum.elim_inr, toW_other _ _ (one_sub_ne g).symm, zero_smul]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Sum.elim_inl, toW_same, map_smul, rename_X]
  rfl

theorem linS_rowM_other (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (x : I (1 - g)) :
    linS (rowM g e v') (⟨1 - g, x⟩ : WV I) =
      rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (linS v' x) := by
  unfold linS rowM
  rw [Fintype.sum_sum_type, map_sum]
  have h2 : ∑ c : ι, (Sum.elim (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) (Sum.inl c)
      (⟨1 - g, x⟩ : WV I)) • (X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Sum.elim_inl, toW_other _ _ (one_sub_ne g), zero_smul]
  rw [h2, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Sum.elim_inr, toW_same, map_smul, rename_X]
  rfl

theorem rename_subst_linS {σ τ τ' : Type} [Fintype σ] [Fintype τ] (f : τ ↪ τ') (M : τ → σ → C)
    (F : MvPowerSeries σ C) :
    rename f (subst (linS M) F) = subst (fun x => rename f (linS M x)) F := by
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_linS M) (HasSubst.X_comp _)]
  congr 1
  funext x
  rw [rename_eq_subst]

theorem subst_row_upG_self (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (F : MvPowerSeries (I g) C) :
    subst (linS (rowM g e v')) (upG g F) =
      rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (subst (linS e) F) := by
  unfold upG
  rw [subst_linS_subst _ (fun s => by simp), rename_subst_linS]
  congr 1
  funext x
  rw [subst_linS_X, linS_rowM_self]

theorem subst_row_upG_other (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (F : MvPowerSeries (I (1 - g)) C) :
    subst (linS (rowM g e v')) (upG (1 - g) F) =
      rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (subst (linS v') F) := by
  unfold upG
  rw [subst_linS_subst _ (fun s => by simp), rename_subst_linS]
  congr 1
  funext x
  rw [subst_linS_X, linS_rowM_other]

theorem toLeaf_eq_killV {V : VF C} {d : ℕ} {J : Fin 2 → Type} (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (F : MvPowerSeries (WV I) C) :
    toLeaf G g a a' F = killV (OnLeafV G g a a') F := by
  ext μ
  have h1 : coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ := rfl
  rw [h1, coeff_killV]
  unfold toLeaf
  by_cases h : ∀ w ∈ μ.support, OnLeafV G g a a' w
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem subst_row_toLeaf {V : VF C} {d : ℕ} {J : Fin 2 → Type} (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b x, (G (1 - g)).ty (Sum.inl x) ≠ a' → v' b x = 0) (F : MvPowerSeries (WV I) C) :
    subst (linS (rowM g e v')) (toLeaf G g a a' F) = subst (linS (rowM g e v')) F := by
  rw [toLeaf_eq_killV]
  refine subst_linS_kill _ _ (fun w hw c => ?_) F
  obtain ⟨g', x⟩ := w
  have hg : g' = g ∨ g' = 1 - g := finset_fin_two_eq_cases g g'
  rcases hg with rfl | rfl
  · have hx : (G g').ty (Sum.inl x) ≠ a := fun h => hw (Or.inl ⟨rfl, h⟩)
    rcases c with c | b
    · show toW g' (e c) _ = 0
      rw [toW_same, he c x hx]
    · show toW (1 - g') (v' b) _ = 0
      rw [toW_other _ _ (one_sub_ne g').symm]
  · have hx : (G (1 - g)).ty (Sum.inl x) ≠ a' := fun h => hw (Or.inr ⟨rfl, h⟩)
    rcases c with c | b
    · show toW g (e c) _ = 0
      rw [toW_other _ _ (one_sub_ne g)]
    · show toW (1 - g) (v' b) _ = 0
      rw [toW_same, hv b x hx]

end Rows

section Bridge

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)

theorem Sys.al_zeroM (c k : I) : S.al c 0 k = S.tan c k := by
  unfold Sys.al
  rw [(S.curve c).2.1]
  rfl

theorem Sys.det_ne_zero : (Matrix.of fun c k : I => S.al c 0 k).det ≠ 0 := by
  intro h
  have h1 := S.unimod
  have h2 : (Matrix.of fun c k : I => S.al c 0 k) = Matrix.of S.tan := by
    ext c k
    exact S.al_zeroM c k
  rw [← h2, h, V.v.map_zero] at h1
  exact WithTop.top_ne_zero h1

theorem Sys.ordGE_alt {t : I → MvPowerSeries I C} (ht : S.IsT t) (c : I) : OrdGE 1 (t c) :=
  (ordGE_one_iff _).2 (ht.1 c)

theorem coeff_pow_eq_zero_of_lt {τ : Type} {f : MvPowerSeries τ C} (hf : OrdGE 1 f) {l s : ℕ}
    (hl : 1 < l) {μ : τ →₀ ℕ} (h : μ.degree < s) : coeff μ (f ^ (l ^ s)) = 0 :=
  Formalism.BaseCaseIdentities.OrdGE.pow hf _ μ (lt_trans h (Nat.lt_pow_self hl))

theorem Sys.isT_partial {t : I → MvPowerSeries I C} (ht : S.IsT t) (x : I) (N : ℕ) (μ : I →₀ ℕ)
    (hμ : μ.degree ≤ N) :
    coeff μ (∑ s ∈ Finset.range (N + 1), ∑ c : I, S.al c s x • t c ^ (V.l ^ s)) =
      coeff μ (X x : MvPowerSeries I C) := by
  rw [coeff_X, ← ht.2 x μ, map_sum]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.2 (by omega)) ?_ ?_
  · intro s hs
    have hs' : μ.degree < s := by
      have := (Finset.mem_sdiff.1 hs).2
      simp only [Finset.mem_range, not_lt] at this
      omega
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [map_smul, coeff_pow_eq_zero_of_lt (S.ordGE_alt ht c) V.l_prime.one_lt hs', smul_zero]
  · intro s _
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul]

theorem Sys.ze_partial {t : I → MvPowerSeries I C} (ht : S.IsT t) (κ : J) (N : ℕ) (μ : I →₀ ℕ)
    (hμ : μ.degree ≤ N) :
    coeff μ (S.ze t κ) =
      coeff μ (-∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.be c s κ • t c ^ (V.l ^ s)) := by
  have h1 : coeff μ (S.ze t κ) = -(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c : I,
      S.be c s κ * coeff μ (t c ^ (V.l ^ s))) := rfl
  rw [h1, map_neg, map_sum]
  congr 1
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_right hμ) ?_ ?_
  · intro s hs
    have hs' : μ.degree < s := by
      have h2 := Finset.mem_sdiff.1 hs
      have h3 := Finset.mem_Icc.1 h2.1
      by_contra hcon
      exact h2.2 (Finset.mem_Icc.2 ⟨h3.1, not_lt.1 hcon⟩)
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [map_smul, coeff_pow_eq_zero_of_lt (S.ordGE_alt ht c) V.l_prime.one_lt hs', smul_zero]
  · intro s _
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul]

variable {τ : Type} [Fintype τ]

theorem Sys.coeff_subst_ze (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t) (κ : J)
    (A : τ →₀ ℕ) :
    coeff A (subst (linS W) (S.ze t κ)) =
      -∑ c, ∑ j ∈ Finset.Icc 1 A.degree,
        S.be c j κ * coeff A (subst (linS W) (t c) ^ (V.l ^ j)) := by
  rw [coeff_subst_linS_congr W (fun μ hμ => S.ze_partial ht κ A.degree μ hμ) A le_rfl,
    subst_linS_neg, subst_linS_sum, map_neg, map_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subst_linS_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [subst_linS_smul, subst_linS_pow, map_smul, smul_eq_mul]

theorem Sys.coeff_tD (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t)
    (al' : I → ℕ → I → C) (zc : τ → I → C)
    (hal : ∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al' c k b * S.al b 0 x)
    (hW : ∀ β x, W β x = ∑ b, zc β b * S.al b 0 x) (b : I) (A : τ →₀ ℕ) :
    coeff A (subst (linS W) (t b)) =
      coeff A (∑ β, MvPowerSeries.C (zc β b) * (X β : MvPowerSeries τ C)) -
        ∑ c, ∑ j ∈ Finset.Icc 1 A.degree,
          al' c j b * coeff A (subst (linS W) (t c) ^ (V.l ^ j)) := by
  obtain ⟨tD, htD⟩ : ∃ tD : I → MvPowerSeries τ C, tD = fun c => subst (linS W) (t c) := ⟨_, rfl⟩
  have htD' : ∀ c, subst (linS W) (t c) = tD c := fun c => by rw [htD]
  simp only [htD']
  obtain ⟨N, hN⟩ : ∃ N, N = A.degree := ⟨_, rfl⟩
  rw [← hN]

  have key : ∀ x, ∑ s ∈ Finset.range (N + 1), ∑ c : I, S.al c s x * coeff A (tD c ^ (V.l ^ s)) =
      ∑ β, W β x * coeff A (X β : MvPowerSeries τ C) := by
    intro x
    have h := coeff_subst_linS_congr W (fun μ hμ => S.isT_partial ht x N μ hμ) A (le_of_eq hN.symm)
    rw [subst_linS_X, subst_linS_sum, map_sum] at h
    have hR : coeff A (linS W x) = ∑ β, W β x * coeff A (X β : MvPowerSeries τ C) := by
      unfold linS
      rw [map_sum]
      exact Finset.sum_congr rfl fun β _ => by rw [map_smul, smul_eq_mul]
    rw [← hR, ← h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_linS_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [subst_linS_smul, subst_linS_pow, map_smul, smul_eq_mul, htD']

  have hsplit : ∀ f : ℕ → C, ∑ s ∈ Finset.range (N + 1), f s = f 0 + ∑ s ∈ Finset.Icc 1 N, f s := by
    intro f
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    refine Finset.sum_bij (fun s _ => s + 1) ?_ ?_ ?_ ?_
    · intro s hs
      have := Finset.mem_range.1 hs
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro s _ s' _ h
      omega
    · intro s hs
      have := Finset.mem_Icc.1 hs
      exact ⟨s - 1, Finset.mem_range.2 (by omega), by omega⟩
    · intro s _
      rfl
  obtain ⟨y, hy⟩ : ∃ y : I → C, y = fun b => coeff A (tD b) +
      (∑ c, ∑ j ∈ Finset.Icc 1 N, al' c j b * coeff A (tD c ^ (V.l ^ j))) -
        ∑ β, zc β b * coeff A (X β : MvPowerSeries τ C) := ⟨_, rfl⟩
  have hvec : Matrix.vecMul y (Matrix.of fun c k : I => S.al c 0 k) = 0 := by
    funext x
    show ∑ b, y b * S.al b 0 x = 0
    have k1 := key x
    rw [hsplit] at k1
    have e0 : ∑ c : I, S.al c 0 x * coeff A (tD c ^ (V.l ^ 0)) =
        ∑ b, coeff A (tD b) * S.al b 0 x := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [pow_zero, pow_one, mul_comm]
    have e1 : ∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.al c s x * coeff A (tD c ^ (V.l ^ s)) =
        ∑ b, (∑ c, ∑ j ∈ Finset.Icc 1 N, al' c j b * coeff A (tD c ^ (V.l ^ j))) * S.al b 0 x := by
      have step1 : ∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.al c s x * coeff A (tD c ^ (V.l ^ s)) =
          ∑ s ∈ Finset.Icc 1 N, ∑ c : I, ∑ b : I,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x := by
        refine Finset.sum_congr rfl fun s hs => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hal c s x (Finset.mem_Icc.1 hs).1, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [step1]
      simp only [Finset.sum_mul]
      calc ∑ s ∈ Finset.Icc 1 N, ∑ c : I, ∑ b : I,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x
          = ∑ c : I, ∑ s ∈ Finset.Icc 1 N, ∑ b : I,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x := Finset.sum_comm
        _ = ∑ c : I, ∑ b : I, ∑ s ∈ Finset.Icc 1 N,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x :=
            Finset.sum_congr rfl fun c _ => Finset.sum_comm
        _ = ∑ b : I, ∑ c : I, ∑ s ∈ Finset.Icc 1 N,
            al' c s b * coeff A (tD c ^ (V.l ^ s)) * S.al b 0 x := Finset.sum_comm
    have e2 : ∑ β, W β x * coeff A (X β : MvPowerSeries τ C) =
        ∑ b, (∑ β, zc β b * coeff A (X β : MvPowerSeries τ C)) * S.al b 0 x := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hW β x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e0, e1, e2] at k1
    rw [hy]
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [k1, sub_self]
  have hy0 : y = 0 := Matrix.eq_zero_of_vecMul_eq_zero S.det_ne_zero hvec
  have hyb : y b = 0 := by rw [hy0]; rfl
  rw [hy] at hyb
  have hz : coeff A (∑ β, MvPowerSeries.C (zc β b) * (X β : MvPowerSeries τ C)) =
      ∑ β, zc β b * coeff A (X β : MvPowerSeries τ C) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun β _ => by rw [coeff_C_mul]
  rw [hz]
  linear_combination hyb

theorem Sys.noConst_tD (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t) :
    NoConst (fun c => subst (linS W) (t c)) := fun c => ordGE_subst_linS W (S.ordGE_alt ht c)

theorem Sys.tD_fix {N1 : ℕ} (D : Formalism.BaseCaseIdentities.Data C (Fin N1) I) (hl : D.l = V.l)
    (hal : ∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x)
    {t : I → MvPowerSeries I C} (ht : S.IsT t) :
    NoConst (fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c)) ∧
      D.Psi (fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c)) =
        fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c) := by
  refine ⟨S.noConst_tD _ ht, ?_⟩
  funext b
  ext A
  rw [Formalism.BaseCaseIdentities.Data.coeff_Psi, hl,
    S.coeff_tD (fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) ht D.al
      (fun δ b => if D.ι δ = b then 1 else 0) hal (fun β x => by simp) b A]
  congr 2
  unfold Formalism.BaseCaseIdentities.Data.zvec
  refine Finset.sum_congr rfl fun δ _ => ?_
  split_ifs <;> simp

end Bridge

section Pull

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem fin_two_eq_one_sub_of_ne {g g' : Fin 2} (h : g' ≠ g) : g' = 1 - g := (finset_fin_two_eq_cases g g').resolve_left h

def rowIdx (g : Fin 2) : WV I → I g ⊕ I (1 - g) := fun w =>
  if h : w.1 = g then Sum.inl (h ▸ w.2) else Sum.inr (fin_two_eq_one_sub_of_ne h ▸ w.2)

theorem rowIdx_self (g : Fin 2) (x : I g) : rowIdx g (⟨g, x⟩ : WV I) = Sum.inl x := by
  simp [rowIdx]

theorem rowIdx_other (g : Fin 2) (x : I (1 - g)) : rowIdx g (⟨1 - g, x⟩ : WV I) = Sum.inr x := by
  simp [rowIdx, one_sub_ne]

theorem rowIdx_injective (g : Fin 2) : Function.Injective (rowIdx g : WV I → I g ⊕ I (1 - g)) := by
  rintro ⟨g1, x1⟩ ⟨g2, x2⟩ h
  rcases finset_fin_two_eq_cases g g1 with h1 | h1 <;> rcases finset_fin_two_eq_cases g g2 with h2 | h2
  · subst h1; subst h2
    rw [rowIdx_self, rowIdx_self] at h
    rw [Sum.inl.inj h]
  · subst h1; subst h2
    rw [rowIdx_self, rowIdx_other] at h
    exact absurd h (by simp)
  · subst h1; subst h2
    rw [rowIdx_other, rowIdx_self] at h
    exact absurd h (by simp)
  · subst h1; subst h2
    rw [rowIdx_other, rowIdx_other] at h
    rw [Sum.inr.inj h]

def ttPull (t : ∀ g, I g → MvPowerSeries (I g) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : I g ⊕ I (1 - g) → MvPowerSeries (ι ⊕ ι') C :=
  Sum.elim (fun c => rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (subst (linS e) (t g c)))
    (fun c => rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (subst (linS v') (t (1 - g) c)))

theorem constantCoeff_ttPull (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, constantCoeff (t g c) = 0) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (s : I g ⊕ I (1 - g)) : constantCoeff (ttPull t g e v' s) = 0 := by
  rcases s with c | c
  · show constantCoeff (rename _ (subst (linS e) (t g c))) = 0
    rw [constantCoeff_rename]
    exact (ordGE_one_iff _).1 (ordGE_subst_linS e ((ordGE_one_iff _).2 (ht0 g c)))
  · show constantCoeff (rename _ (subst (linS v') (t (1 - g) c))) = 0
    rw [constantCoeff_rename]
    exact (ordGE_one_iff _).1 (ordGE_subst_linS v' ((ordGE_one_iff _).2 (ht0 (1 - g) c)))

theorem constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : constantCoeff F = 0) :
    constantCoeff (upG g F : MvPowerSeries (WV I) C) = 0 := by
  unfold upG
  exact (ordGE_one_iff _).1 (ordGE_subst (fun x => Formalism.BaseCaseIdentities.OrdGE.X _) ((ordGE_one_iff _).2 hF))

theorem intGerm_pull (V : VF C) (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, constantCoeff (t g c) = 0) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) {K : MvPowerSeries (WV I) C} (hK : K ∈ IntGerm V t) :
    ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C, (∀ A, V.Ge 0 (coeff A Kp)) ∧
      subst (linS (rowM g e v')) K = subst (ttPull t g e v') Kp := by
  obtain ⟨γ, hγ, rfl⟩ := hK
  let f : WV I ↪ I g ⊕ I (1 - g) := ⟨rowIdx g, rowIdx_injective g⟩
  refine ⟨rename f γ, ?_, ?_⟩
  · intro A
    by_cases hA : A ∈ Set.range (Finsupp.mapDomain f)
    · obtain ⟨y, rfl⟩ := hA
      rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
      exact hγ y
    · rw [coeff_rename_eq_zero _ _ hA]
      exact VF.Ge.zero 0
  · rw [subst_linS_subst _ (fun s => constantCoeff_upG _ (ht0 _ _)), rename_eq_subst,
      subst_comp_subst_apply (HasSubst.X_comp _)
        (hasSubst_of_constantCoeff_zero (constantCoeff_ttPull t ht0 g e v'))]
    congr 1
    funext w
    rw [Function.comp_apply,
      subst_X (hasSubst_of_constantCoeff_zero (constantCoeff_ttPull t ht0 g e v'))]
    obtain ⟨g', x⟩ := w
    rcases finset_fin_two_eq_cases g g' with rfl | rfl
    · show subst _ (upG g' (t g' x)) = ttPull t g' e v' (rowIdx g' ⟨g', x⟩)
      rw [subst_row_upG_self, rowIdx_self]
      rfl
    · show subst _ (upG (1 - g) (t (1 - g) x)) = ttPull t g e v' (rowIdx g ⟨1 - g, x⟩)
      rw [subst_row_upG_other, rowIdx_other]
      rfl

theorem coeff_mul_eq_zero_of_left {σ : Type} (Q : σ → Prop) {F : MvPowerSeries σ C}
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M F = 0) (G : MvPowerSeries σ C)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [hF p.1 (fun b hb => by
    have h1 := hM b hb
    rw [← hp', Finsupp.add_apply] at h1
    omega), zero_mul]

theorem coeff_prod_eq_zero_of_mem {σ ρ : Type} (Q : σ → Prop) (s : Finset ρ)
    (F : ρ → MvPowerSeries σ C) {w : ρ} (hw : w ∈ s)
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M (F w) = 0)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (∏ i ∈ s, F i) = 0 := by
  rw [← Finset.mul_prod_erase s F hw]
  exact coeff_mul_eq_zero_of_left Q hF _ M hM

theorem coeff_pow_eq_zero_of_base {σ : Type} (Q : σ → Prop) {F : MvPowerSeries σ C}
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M F = 0) {n : ℕ} (hn : n ≠ 0)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (F ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ']
  exact coeff_mul_eq_zero_of_left Q hF _ M hM

theorem coeff_subst_linS_eq_zero {σ τ : Type} [Fintype σ] [Fintype τ] (M : τ → σ → C) (R : σ → Prop)
    (Q : τ → Prop) (hRQ : ∀ w, R w → ∀ c, ¬ Q c → M c w = 0) (H : MvPowerSeries σ C)
    (hH : ∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, ¬ R w) → coeff μ H = 0)
    (A : τ →₀ ℕ) (hA : ∀ b, Q b → A b = 0) : coeff A (subst (linS M) H) = 0 := by
  rw [coeff_subst (hasSubst_linS M)]
  refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
  by_cases hμ : ∀ w ∈ μ.support, ¬ R w
  · rw [hH μ hμ, zero_smul]
  · simp only [not_forall, not_not] at hμ
    obtain ⟨w, hw, hRw⟩ := hμ
    have hlin : ∀ B : τ →₀ ℕ, (∀ b, Q b → B b = 0) → coeff B (linS M w) = 0 := by
      intro B hB
      unfold linS
      rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [map_smul]
      by_cases hc : Q c
      · rw [coeff_X, if_neg, smul_zero]
        intro h
        have := hB c hc
        rw [h, Finsupp.single_eq_same] at this
        exact one_ne_zero this
      · rw [hRQ w hRw c hc, zero_smul]
    have : coeff A (μ.prod fun s n => linS M s ^ n) = 0 :=
      coeff_prod_eq_zero_of_mem Q μ.support (fun s => linS M s ^ μ s) hw
        (fun B hB => coeff_pow_eq_zero_of_base Q hlin (Finsupp.mem_support_iff.1 hw) B hB) A hA
    rw [this, smul_zero]

end Pull

section RowDataPull

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (Xr : RowData C V d I J) {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem RowData.hPull_axis_right (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (A : ι ⊕ ι' →₀ ℕ) (hA : ∀ b, A (Sum.inr b) = 0) :
    coeff A (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) = 0 := by
  rw [hPullW_eq]
  refine coeff_subst_linS_eq_zero _ (fun w => w.1 = 1 - g) (fun x => ∃ b, x = Sum.inr b) ?_ _ ?_ A ?_
  · rintro ⟨g', x⟩ hw c hc
    have hw' : g' = 1 - g := hw
    subst hw'
    rcases c with c | b
    · show toW g (e c) _ = 0
      rw [toW_other _ _ (one_sub_ne g)]
    · exact absurd ⟨b, rfl⟩ hc
  · intro μ hμ
    refine Xr.hL_axes g a a' μ (Or.inl fun w hw => ?_)
    exact (finset_fin_two_eq_cases g w.1).resolve_right (hμ w hw)
  · rintro _ ⟨b, rfl⟩
    exact hA b

theorem RowData.hPull_axis_left (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (A : ι ⊕ ι' →₀ ℕ) (hA : ∀ c, A (Sum.inl c) = 0) :
    coeff A (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) = 0 := by
  rw [hPullW_eq]
  refine coeff_subst_linS_eq_zero _ (fun w => w.1 = g) (fun x => ∃ c, x = Sum.inl c) ?_ _ ?_ A ?_
  · rintro ⟨g', x⟩ hw c hc
    have hw' : g' = g := hw
    subst hw'
    rcases c with c | b
    · exact absurd ⟨c, rfl⟩ hc
    · show toW (1 - g') (v' b) _ = 0
      rw [toW_other _ _ (one_sub_ne g').symm]
  · intro μ hμ
    refine Xr.hL_axes g a a' μ (Or.inr fun w hw => ?_)
    exact (finset_fin_two_eq_cases g w.1).resolve_left (hμ w hw)
  · rintro _ ⟨c, rfl⟩
    exact hA c

theorem RowData.dh_pull (hAlt : Xr.Alt) (g : Fin 2) (a a' : ZMod d) (hodd : Odd (a' - a).val)
    (S : ∀ g, Sys (Xr.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C) (hT : ∀ g, (S g).IsT (t g))
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (Xr.G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b x, (Xr.G (1 - g)).ty (Sum.inl x) ≠ a' → v' b x = 0)
    (hvint : ∀ b x, V.Ge 0 (v' b x)) (b : ι') :
    ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C, (∀ A, V.Ge 0 (coeff A Kp)) ∧
      dVar (Sum.inr b)
          (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) =
        subst (ttPull t g e v') Kp +
          rename (Function.Embedding.inl : ι ↪ ι ⊕ ι')
            (∑ k : I (1 - g), v' b k • ∑ κ : J g,
              Xr.pair g κ k • subst (linS e) ((S g).ze (t g) κ)) := by
  have ht0 : ∀ g c, constantCoeff (t g c) = 0 := fun g c => (hT g).1 c
  have hs := hasSubst_of_constantCoeff_zero (constantCoeff_ttPull t ht0 g e v')

  have hk : ∀ k : I (1 - g), ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C,
      (∀ A, V.Ge 0 (coeff A Kp)) ∧
      v' b k • subst (linS (rowM g e v')) (dVar (⟨1 - g, k⟩ : WV I) (Xr.hL g a a')) =
        v' b k • (subst (ttPull t g e v') Kp +
          rename (Function.Embedding.inl : ι ↪ ι ⊕ ι')
            (∑ κ : J g, Xr.pair g κ k • subst (linS e) ((S g).ze (t g) κ))) := by
    intro k
    by_cases hkt : (Xr.G (1 - g)).ty (Sum.inl k) = a'
    · obtain ⟨K, hK, hEq⟩ := Xr.C_eq hAlt g a a' hodd S t hT k hkt
      obtain ⟨Kp, hKp, hKpe⟩ := intGerm_pull V t ht0 g e v' hK
      refine ⟨Kp, hKp, ?_⟩
      congr 1
      have h1 : dVar (⟨1 - g, k⟩ : WV I) (Xr.hL g a a') =
          toLeaf Xr.G g a a' K +
            toLeaf Xr.G g a a' (∑ κ : J g, Xr.pair g κ k • upG g ((S g).ze (t g) κ)) := by
        rw [← hEq]; ring
      rw [h1, subst_linS_add, subst_row_toLeaf Xr.G g a a' e v' he hv,
        subst_row_toLeaf Xr.G g a a' e v' he hv, hKpe, subst_linS_sum, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [subst_linS_smul, subst_row_upG_self, map_smul]
    · exact ⟨0, fun A => by simpa using VF.Ge.zero (V := V) 0, by rw [hv b k hkt, zero_smul, zero_smul]⟩
  choose Kp hKp hKpe using hk
  refine ⟨∑ k, v' b k • Kp k, ?_, ?_⟩
  · intro A
    rw [map_sum]
    refine VF.Ge.sum fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    exact (hvint b k).mul_int (hKp k A)
  · rw [hPullW_eq, dVar_subst_linS]
    have hsig : ∑ w : WV I, rowM g e v' (Sum.inr b) w •
          subst (linS (rowM g e v')) (dVar w (Xr.hL g a a')) =
        ∑ k : I (1 - g), v' b k •
          subst (linS (rowM g e v')) (dVar (⟨1 - g, k⟩ : WV I) (Xr.hL g a a')) := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single (1 - g)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        show toW (1 - g) (v' b) _ • _ = _
        rw [toW_same]
      · intro g' _ hg'
        refine Finset.sum_eq_zero fun x _ => ?_
        show toW (1 - g) (v' b) _ • _ = _
        rw [toW_other _ _ hg', zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsig]
    simp only [hKpe, smul_add]
    rw [Finset.sum_add_distrib, map_sum]
    congr 1
    · rw [← substAlgHom_apply hs, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, substAlgHom_apply]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]

end RowDataPull

end Formalism.L2.FormalSeriesBounds
