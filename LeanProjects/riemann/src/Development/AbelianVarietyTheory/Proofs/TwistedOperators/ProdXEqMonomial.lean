import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymbolCongr

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW.Symbol

variable {p q : ℕ}

def prodU (l : List (Mat p q)) : Ug p q := (l.map (ugι p q)).prod

theorem prodU_cons (x : Mat p q) (l : List (Mat p q)) : prodU (x :: l) = ugι p q x * prodU l := by
  simp only [prodU, List.map_cons, List.prod_cons]

theorem prodU_append (l l' : List (Mat p q)) : prodU (l ++ l') = prodU l * prodU l' := by
  simp only [prodU, List.map_append, List.prod_append]

def below (p q k : ℕ) : Submodule ℂ (Ug p q) :=
  Submodule.span ℂ {u | ∃ l : List (Mat p q), l.length < k ∧ u = prodU l}

section
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem ug_bracket (x y : Mat p q) :
    ugι p q (x * y - y * x) = ugι p q x * ugι p q y - ugι p q y * ugι p q x := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q) x y
  simpa only [ugι, LieHom.coe_toLinearMap, Ring.lie_def] using h
end

theorem mul_mem_below (x : Mat p q) {k : ℕ} {u : Ug p q} (hu : u ∈ below p q k) :
    ugι p q x * u ∈ below p q (k + 1) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x :: l, ?_, (prodU_cons x l).symm⟩
    simp only [List.length_cons]
    omega
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' => rw [mul_add]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hw

theorem perm_sub_mem_below {l l' : List (Mat p q)} (h : l.Perm l') :
    prodU l - prodU l' ∈ below p q l.length := by
  induction h with
  | nil => rw [sub_self]; exact Submodule.zero_mem _
  | cons x _ ih =>
    rw [prodU_cons, prodU_cons, ← mul_sub, List.length_cons]
    exact mul_mem_below x ih
  | swap x y l =>
    have e : prodU (y :: x :: l) - prodU (x :: y :: l) = prodU ((y * x - x * y) :: l) := by
      simp only [prodU_cons, ug_bracket, sub_mul, mul_assoc]
    rw [e]
    exact Submodule.subset_span ⟨(y * x - x * y) :: l, by simp, rfl⟩
  | @trans l₁ l₂ l₃ h₁ _ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel (prodU l₁) (prodU l₂) (prodU l₃)]
    exact Submodule.add_mem _ ih₁ (h₁.length_eq ▸ ih₂)

variable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)

def cls (v : V) : Ug p q →ₗ[ℂ] Ind act :=
  (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v

theorem cls_apply (v : V) (u : Ug p q) :
    cls act v u = (indRel act).mkQ (TensorProduct.tmul ℂ u v) := rfl

private lemma indF_le_indFlt_of_lt {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂_of_le (f := fun i (_ : i < k) => indF act i) j h le_rfl

private lemma cls_prodU_mem_indF (v : V) (l : List (Mat p q)) :
    cls act v (prodU l) ∈ indF act l.length :=
  Submodule.subset_span ⟨prodU l, Submodule.subset_span ⟨l, le_rfl, rfl⟩, v, cls_apply act v _⟩

theorem cls_mem_of_below (v : V) {k : ℕ} {u : Ug p q} (hu : u ∈ below p q k) :
    cls act v u ∈ indFlt act k := by
  have hle : below p q k ≤ (indFlt act k).comap (cls act v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    exact indF_le_indFlt_of_lt act hl (cls_prodU_mem_indF act v l)
  exact hle hu

theorem cls_mul_kc (v : V) (u : Ug p q) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (u * ugι p q Y) = cls act (act Y v) u := by
  rw [cls_apply, cls_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨u, Y, v, hY, rfl⟩)

theorem cls_mem_of_kc (v : V) (l l' : List (Mat p q)) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (prodU (l ++ Y :: l')) ∈ indFlt act (l.length + (l'.length + 1)) := by
  have hperm : (l ++ Y :: l').Perm ((l ++ l') ++ [Y]) :=
    List.perm_middle.trans (List.perm_append_singleton Y (l ++ l')).symm
  have hlen : (l ++ Y :: l').length = l.length + (l'.length + 1) := by simp
  have h₁ := cls_mem_of_below act v (perm_sub_mem_below hperm)
  rw [hlen] at h₁
  have h₂ : cls act v (prodU ((l ++ l') ++ [Y])) ∈ indFlt act (l.length + (l'.length + 1)) := by
    have e : prodU ((l ++ l') ++ [Y]) = prodU (l ++ l') * ugι p q Y := by
      rw [prodU_append, prodU_cons]
      simp [prodU]
    rw [e, cls_mul_kc act v _ hY]
    refine indF_le_indFlt_of_lt act (j := (l ++ l').length) ?_ (cls_prodU_mem_indF act _ _)
    simp only [List.length_append]
    omega
  have e : cls act v (prodU (l ++ Y :: l')) =
      cls act v (prodU (l ++ Y :: l') - prodU ((l ++ l') ++ [Y])) + cls act v (prodU ((l ++ l') ++ [Y])) := by
    rw [map_sub, sub_add_cancel]
  rw [e]
  exact Submodule.add_mem _ h₁ h₂

theorem pLin_add (x y : Mat p q) : pLin (x + y) = pLin x + pLin y := by
  simp only [pLin, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem pLin_smul (c : ℂ) (x : Mat p q) : pLin (c • x) = c • pLin x := by
  simp only [pLin, Finset.smul_sum, Matrix.smul_apply, smul_eq_mul, map_mul, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem pLin_kc {Y : Mat p q} (hY : IsKC Y) : pLin Y = 0 := by
  refine Finset.sum_eq_zero fun ab _ => ?_
  rw [hY _ _ ab.2, map_zero, zero_mul]

def unitP (ab : PIx p q) : Mat p q := Eab ab.1.1 ab.1.2

theorem pLin_unitP (ab : PIx p q) : pLin (unitP ab) = MvPolynomial.X ab := by
  unfold pLin
  rw [Finset.sum_eq_single ab]
  · simp [unitP, Eab]
  · intro b _ hb
    have hne : ¬ (ab.1.1 = b.1.1 ∧ ab.1.2 = b.1.2) := fun e => hb (Subtype.ext (Prod.ext e.1.symm e.2.symm))
    simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
  · intro h
    exact absurd (Finset.mem_univ ab) h

theorem isKC_Eab {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  have hne : ¬ (a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩
    exact hcd h
  simp [Eab, Matrix.single_apply_of_ne (h := hne)]

theorem prod_X_eq_monomial (a : List (PIx p q)) :
    (a.map (MvPolynomial.X : PIx p q → MvPolynomial (PIx p q) ℂ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp (a : Multiset (PIx p q))) 1 := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.map_cons, List.prod_cons, ih, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem symProd_sub_mem (b : List (Mat p q)) {k : ℕ} (x : Fin k → Mat p q)
    (h : b.Perm (List.ofFn x)) :
    prodU b - symProd (fun i => ugι p q (x i)) ∈ below p q b.length := by
  have hk : ((k.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin k), prodU b = prodU b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]
  have e : prodU b - symProd (fun i => ugι p q (x i)) =
      ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), (prodU b - prodU (List.ofFn fun i => x (σ i))) := by
    rw [Finset.sum_sub_distrib, smul_sub, hk]
    simp only [symProd, prodU, List.map_ofFn]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => perm_sub_mem_below ?_)
  exact h.trans (Equiv.Perm.ofFn_comp_perm σ x).symm

theorem units_sub_mem (a : List (PIx p q)) :
    prodU (a.map unitP) - symU p q (a.map MvPolynomial.X).prod ∈ below p q a.length := by
  rw [prod_X_eq_monomial]
  have hb : MvPolynomial.monomial (Multiset.toFinsupp (a : Multiset (PIx p q))) (1 : ℂ) =
      MvPolynomial.basisMonomials (PIx p q) ℂ (Multiset.toFinsupp (a : Multiset (PIx p q))) := by
    rw [MvPolynomial.coe_basisMonomials]
  rw [hb, symU, Module.Basis.constr_basis, Multiset.toFinsupp_toMultiset]
  have hlen : (a.map unitP).length = a.length := List.length_map _
  rw [← hlen]
  refine symProd_sub_mem (a.map unitP) (fun i => unitP ((a : Multiset (PIx p q)).toList.get i)) ?_
  have hL : ((a : Multiset (PIx p q)).toList).Perm a :=
    Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList])
  have hf : List.ofFn (fun i => unitP ((a : Multiset (PIx p q)).toList.get i)) =
      ((a : Multiset (PIx p q)).toList).map unitP :=
    List.ext_get (by simp) (by simp)
  rw [hf]
  exact (hL.map unitP).symm

private lemma sum_unitP_apply (x : Mat p q) (c d : Ix p q) :
    (∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab) c d = if sameBlock c d then 0 else x c d := by
  rw [Matrix.sum_apply]
  split_ifs with h
  · refine Finset.sum_eq_zero fun ab _ => ?_
    have hne : ¬ (ab.1.1 = c ∧ ab.1.2 = d) := by
      rintro ⟨h₁, h₂⟩
      exact ab.2 (h₁ ▸ h₂ ▸ h)
    simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
  · rw [Finset.sum_eq_single (⟨(c, d), h⟩ : PIx p q)]
    · simp [unitP, Eab]
    · intro ab _ hab
      have hne : ¬ (ab.1.1 = c ∧ ab.1.2 = d) := fun e => hab (Subtype.ext (Prod.ext e.1 e.2))
      simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

private lemma isKC_sub_sum_unitP (x : Mat p q) : IsKC (x - ∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab) := by
  intro c d h
  rw [Matrix.sub_apply, sum_unitP_apply, if_neg h, sub_self]

theorem mixed_mem (v : V) (l : List (Mat p q)) : ∀ a : List (PIx p q),
    cls act v (prodU (a.map unitP) * prodU l) -
      cls act v (symU p q ((a.map MvPolynomial.X).prod * (l.map pLin).prod)) ∈
      indFlt act (a.length + l.length) := by
  induction l with
  | nil =>
    intro a
    have h1 : prodU ([] : List (Mat p q)) = 1 := by simp [prodU]
    simp only [h1, mul_one, List.map_nil, List.prod_nil, List.length_nil, add_zero]
    rw [← map_sub]
    exact cls_mem_of_below act v (units_sub_mem a)
  | cons x l ih =>
    intro a
    set P : Mat p q := ∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab with hP
    have hY : IsKC (x - P) := isKC_sub_sum_unitP x
    have hx : ugι p q x = ∑ ab : PIx p q, x ab.1.1 ab.1.2 • ugι p q (unitP ab) + ugι p q (x - P) := by
      rw [map_sub, hP, map_sum]
      simp only [map_smul]
      abel
    have hpl : pLin x = ∑ ab : PIx p q, x ab.1.1 ab.1.2 • MvPolynomial.X ab := by
      simp only [pLin, MvPolynomial.smul_eq_C_mul]
    have hL : prodU (a.map unitP) * prodU (x :: l) =
        ∑ ab : PIx p q, x ab.1.1 ab.1.2 • (prodU ((a ++ [ab]).map unitP) * prodU l) +
          prodU (a.map unitP ++ (x - P) :: l) := by
      rw [prodU_cons, hx, add_mul, Finset.sum_mul, mul_add, Finset.mul_sum, prodU_append, prodU_cons]
      congr 1
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [List.map_append, prodU_append, List.map_singleton, prodU_cons]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      simp [prodU]
    have hR : (a.map MvPolynomial.X).prod * ((x :: l).map pLin).prod =
        ∑ ab : PIx p q, x ab.1.1 ab.1.2 •
          (((a ++ [ab]).map MvPolynomial.X).prod * (l.map pLin).prod) := by
      rw [List.map_cons, List.prod_cons, hpl, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        smul_mul_assoc, mul_smul_comm, mul_assoc]
    rw [hL, hR, map_add, map_sum, map_sum, map_sum]
    simp only [map_smul]
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun ab _ => ?_) ?_
    · rw [← smul_sub]
      refine Submodule.smul_mem _ _ ?_
      have h := ih (a ++ [ab])
      have e : (a ++ [ab]).length + l.length = a.length + (x :: l).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rwa [e] at h
    · have h := cls_mem_of_kc act v (a.map unitP) l hY
      have e : a.length + (l.length + 1) = a.length + (x :: l).length := by simp
      rw [List.length_map, e] at h
      exact h

end GlobalTheory.InducedPBW.Symbol

namespace GlobalTheory.InducedPBW

theorem symbolCongr (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : SymbolCongr act := by
  intro l v
  have h := Symbol.mixed_mem act v l []
  simp only [Symbol.prodU, List.map_nil, List.prod_nil, one_mul, List.length_nil, zero_add,
    Symbol.cls_apply] at h
  exact h

end GlobalTheory.InducedPBW
