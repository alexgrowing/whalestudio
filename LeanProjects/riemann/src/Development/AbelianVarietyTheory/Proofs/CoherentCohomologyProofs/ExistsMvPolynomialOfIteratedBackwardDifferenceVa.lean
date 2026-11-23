import Mathlib

namespace GlobalTheory

open Finset

section Calculus

variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

def bwdDiff (g : G) (φ : G → M) : G → M := fun x ↦ φ x - φ (x - g)

def multiDiff {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) : G → M :=
  fun x ↦ ∑ S : Finset ι, (-1 : ℤ) ^ S.card • φ (x - ∑ i ∈ S, g i)

def DiffVanish (n : ℕ) (φ : G → M) : Prop := ∀ g : Fin n → G, multiDiff g φ = 0

theorem bwdDiff_apply (g : G) (φ : G → M) (x : G) : bwdDiff g φ x = φ x - φ (x - g) := rfl

theorem multiDiff_apply {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) (x : G) :
    multiDiff g φ x = ∑ S : Finset ι, (-1 : ℤ) ^ S.card • φ (x - ∑ i ∈ S, g i) := rfl

def shiftRep (G M : Type*) [AddCommGroup G] [AddCommGroup M] :
    Multiplicative G →* Module.End ℤ (G → M) where
  toFun g :=
    { toFun := fun φ x ↦ φ (x - g.toAdd)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [sub_sub]

noncomputable def shiftAct (G M : Type*) [AddCommGroup G] [AddCommGroup M] :
    AddMonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℤ (G → M) :=
  AddMonoidAlgebra.lift ℤ _ G (shiftRep G M)

noncomputable def diffElt (g : G) : AddMonoidAlgebra ℤ G := 1 - AddMonoidAlgebra.of' ℤ G g

theorem shiftAct_of (g : G) (φ : G → M) (x : G) :
    shiftAct G M (AddMonoidAlgebra.of' ℤ G g) φ x = φ (x - g) := by
  simp [shiftAct, shiftRep]

theorem shiftAct_diffElt (g : G) (φ : G → M) : shiftAct G M (diffElt g) φ = bwdDiff g φ := by
  ext x
  rw [diffElt, map_sub, map_one, LinearMap.sub_apply, Pi.sub_apply, shiftAct_of]; rfl

theorem of'_add (a b : G) : AddMonoidAlgebra.of' ℤ G (a + b) =
    AddMonoidAlgebra.of' ℤ G a * AddMonoidAlgebra.of' ℤ G b := by
  simp [AddMonoidAlgebra.single_mul_single]

theorem of'_sum {ι : Type*} (s : Finset ι) (g : ι → G) :
    AddMonoidAlgebra.of' ℤ G (∑ i ∈ s, g i) = ∏ i ∈ s, AddMonoidAlgebra.of' ℤ G (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, of'_add, ih]

theorem diffElt_zero : diffElt (0 : G) = 0 := by
  simp [diffElt, AddMonoidAlgebra.one_def]

theorem diffElt_add (a b : G) :
    diffElt (a + b) = diffElt a + diffElt b - diffElt a * diffElt b := by
  simp only [diffElt, of'_add]; ring

theorem diffElt_neg (a : G) : diffElt (-a) = -(AddMonoidAlgebra.of' ℤ G (-a)) * diffElt a := by
  have : AddMonoidAlgebra.of' ℤ G (-a) * AddMonoidAlgebra.of' ℤ G a = 1 := by
    rw [← of'_add]; simp [AddMonoidAlgebra.one_def]
  simp only [diffElt]; linear_combination (-1 : AddMonoidAlgebra ℤ G) * this

theorem multiDiff_eq_shiftAct {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) :
    multiDiff g φ = shiftAct G M (∏ i, diffElt (g i)) φ := by
  classical
  ext x
  simp only [diffElt, sub_eq_add_neg]
  rw [prod_one_add, powerset_univ, map_sum, LinearMap.sum_apply, Finset.sum_apply,
    multiDiff_apply]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [prod_neg, ← of'_sum]
  have : (-1 : AddMonoidAlgebra ℤ G) ^ S.card * AddMonoidAlgebra.of' ℤ G (∑ i ∈ S, g i) =
      ((-1 : ℤ) ^ S.card) • AddMonoidAlgebra.of' ℤ G (∑ i ∈ S, g i) := by
    rw [zsmul_eq_mul]; push_cast; rfl
  rw [this, map_smul, LinearMap.smul_apply, Pi.smul_apply, shiftAct_of]

@[simp] theorem multiDiff_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (g : ι → G)
    (φ : G → M) : multiDiff g φ = φ := by
  simp [multiDiff_eq_shiftAct]

theorem multiDiff_cons {d : ℕ} (a : G) (g : Fin d → G) (φ : G → M) :
    multiDiff (Fin.cons a g : Fin (d + 1) → G) φ = bwdDiff a (multiDiff g φ) := by
  simp [multiDiff_eq_shiftAct, Fin.prod_univ_succ, shiftAct_diffElt]

theorem multiDiff_cons' {d : ℕ} (a : G) (g : Fin d → G) (φ : G → M) :
    multiDiff (Fin.cons a g : Fin (d + 1) → G) φ = multiDiff g (bwdDiff a φ) := by
  simp only [multiDiff_eq_shiftAct, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_comm, map_mul, Module.End.mul_apply, shiftAct_diffElt]

theorem multiDiff_const {d : ℕ} (a : G) (φ : G → M) :
    multiDiff (fun _ : Fin d ↦ a) φ = (bwdDiff a)^[d] φ := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← ih, ← multiDiff_cons]
    congr 1
    ext i; cases i using Fin.cases <;> simp

theorem multiDiff_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (g : ι → G)
    (φ : G → M) : multiDiff (g ∘ e) φ = multiDiff g φ := by
  simp only [multiDiff_eq_shiftAct, Function.comp]
  rw [Equiv.prod_comp e (fun i ↦ diffElt (g i))]

theorem multiDiff_add {ι : Type*} [Fintype ι] (g : ι → G) (φ ψ : G → M) :
    multiDiff g (φ + ψ) = multiDiff g φ + multiDiff g ψ := by
  simp [multiDiff_eq_shiftAct]

theorem multiDiff_sub {ι : Type*} [Fintype ι] (g : ι → G) (φ ψ : G → M) :
    multiDiff g (φ - ψ) = multiDiff g φ - multiDiff g ψ := by
  simp [multiDiff_eq_shiftAct]

theorem multiDiff_map {ι N : Type*} [Fintype ι] [AddCommGroup N] (f : M →+ N) (g : ι → G)
    (φ : G → M) : multiDiff g (f ∘ φ) = f ∘ multiDiff g φ := by
  ext x; simp only [multiDiff, Function.comp, map_sum, map_zsmul]

theorem multiDiff_comap {ι H : Type*} [Fintype ι] [AddCommGroup H] (f : H →+ G) (g : ι → H)
    (φ : G → M) : multiDiff g (φ ∘ f) = multiDiff (f ∘ g) φ ∘ f := by
  ext x; simp only [multiDiff, Function.comp, map_sum, map_sub]

theorem multiDiff_translate {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) (a x : G) :
    multiDiff g (fun y ↦ φ (a + y)) x = multiDiff g φ (a + x) := by
  simp only [multiDiff, add_sub_assoc]

noncomputable def diffIdeal (G : Type*) [AddCommGroup G] : Ideal (AddMonoidAlgebra ℤ G) :=
  Ideal.span (Set.range (diffElt : G → _))

theorem diffElt_mem (g : G) : diffElt g ∈ diffIdeal G := Ideal.subset_span ⟨g, rfl⟩

theorem span_diffElt_image {S : Set G} (hS : AddSubgroup.closure S = ⊤) :
    Ideal.span (diffElt '' S) = diffIdeal G := by
  refine le_antisymm (Ideal.span_mono (Set.image_subset_range _ _)) (Ideal.span_le.2 ?_)
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top g
  induction hg using AddSubgroup.closure_induction with
  | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
  | zero => rw [diffElt_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    rw [diffElt_add]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hx hy) (Ideal.mul_mem_left _ _ hy)
  | neg x _ hx => rw [diffElt_neg]; exact Ideal.mul_mem_left _ _ hx

theorem prod_diffElt_mem {ι : Type*} (s : Finset ι) (g : ι → G) :
    ∏ i ∈ s, diffElt (g i) ∈ diffIdeal G ^ s.card := by
  rw [← prod_const]
  exact Ideal.prod_mem_prod fun i _ ↦ diffElt_mem _

theorem shiftAct_eq_zero_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) {n : ℕ}
    {φ : G → M} (h : ∀ g : Fin n → G, (∀ i, g i ∈ S) → multiDiff g φ = 0)
    {r : AddMonoidAlgebra ℤ G} (hr : r ∈ diffIdeal G ^ n) : shiftAct G M r φ = 0 := by
  rw [← span_diffElt_image hS, Ideal.span, Submodule.span_pow] at hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨f, rfl⟩ := Set.mem_pow.1 hr
    choose g hg hg' using fun i ↦ (f i).2
    rw [List.prod_ofFn, ← h g hg, multiDiff_eq_shiftAct]
    simp only [hg']
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

theorem diffVanish_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) {n : ℕ}
    {φ : G → M} (h : ∀ g : Fin n → G, (∀ i, g i ∈ S) → multiDiff g φ = 0) :
    DiffVanish n φ := fun g ↦ by
  rw [multiDiff_eq_shiftAct]
  exact shiftAct_eq_zero_of_generators hS h (by simpa using prod_diffElt_mem univ g)

theorem DiffVanish.shiftAct_eq_zero {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    {r : AddMonoidAlgebra ℤ G} (hr : r ∈ diffIdeal G ^ n) : shiftAct G M r φ = 0 :=
  shiftAct_eq_zero_of_generators (S := Set.univ) (by simp) (fun g _ ↦ h g) hr

theorem DiffVanish.multiDiff_eq_zero {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    {ι : Type*} [Fintype ι] (hn : n ≤ Fintype.card ι) (g : ι → G) : multiDiff g φ = 0 := by
  rw [multiDiff_eq_shiftAct]
  exact h.shiftAct_eq_zero (Ideal.pow_le_pow_right hn (prod_diffElt_mem univ g))

theorem DiffVanish.mono {m n : ℕ} {φ : G → M} (h : DiffVanish m φ) (hmn : m ≤ n) :
    DiffVanish n φ := fun g ↦ h.multiDiff_eq_zero (by simpa) g

theorem diffVanish_zero_iff {φ : G → M} : DiffVanish 0 φ ↔ φ = 0 := by
  simp [DiffVanish]

theorem diffVanish_succ_iff {n : ℕ} {φ : G → M} :
    DiffVanish (n + 1) φ ↔ ∀ a, DiffVanish n (bwdDiff a φ) := by
  refine ⟨fun h a g ↦ by rw [← multiDiff_cons', h], fun h g ↦ ?_⟩
  rw [← Fin.cons_self_tail g, multiDiff_cons', h]

theorem DiffVanish.map {N : Type*} [AddCommGroup N] {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    (f : M →+ N) : DiffVanish n (f ∘ φ) := fun g ↦ by
  rw [multiDiff_map, h]; ext; simp

theorem DiffVanish.comap {H : Type*} [AddCommGroup H] {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    (f : H →+ G) : DiffVanish n (φ ∘ f) := fun g ↦ by
  rw [multiDiff_comap, h]; rfl

theorem DiffVanish.translate {n : ℕ} {φ : G → M} (h : DiffVanish n φ) (a : G) :
    DiffVanish n (fun y ↦ φ (a + y)) := fun g ↦ by
  ext x; rw [multiDiff_translate, h]; rfl

theorem DiffVanish.multiDiff_eq {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) (g : Fin d → G)
    (x y : G) : multiDiff g φ x = multiDiff g φ y := by
  have := congrFun (h (Fin.cons (x - y) g)) x
  rw [multiDiff_cons, bwdDiff_apply, sub_sub_cancel] at this
  exact sub_eq_zero.1 this

theorem DiffVanish.multiDiff_update_add {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (i : Fin d) (a b : G) :
    multiDiff (Function.update g i (a + b)) φ =
      multiDiff (Function.update g i a) φ + multiDiff (Function.update g i b) φ := by
  have key : ∀ c : G, ∏ j, diffElt (Function.update g i c j) =
      diffElt c * ∏ j ∈ univ.erase i, diffElt (g j) := fun c ↦ by
    rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have hm : diffElt a * (diffElt b * ∏ j ∈ univ.erase i, diffElt (g j)) ∈
      diffIdeal G ^ (d + 1) := by
    rw [← key b, pow_succ']
    exact Ideal.mul_mem_mul (diffElt_mem a)
      (by simpa using prod_diffElt_mem univ (Function.update g i b))
  simp only [multiDiff_eq_shiftAct, key]
  rw [diffElt_add, sub_mul, add_mul, mul_assoc, map_sub, map_add, LinearMap.sub_apply,
    h.shiftAct_eq_zero hm, sub_zero, LinearMap.add_apply]

def DiffVanish.form {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) :
    MultilinearMap ℤ (fun _ : Fin d ↦ G) M :=
  MultilinearMap.mk' (fun g ↦ multiDiff g φ 0)
    (fun g i a b ↦ by exact congrFun (h.multiDiff_update_add g i a b) 0)
    (fun g i c a ↦ by
      exact map_zsmul (AddMonoidHom.mk' (fun a ↦ multiDiff (Function.update g i a) φ 0)
        (fun a b ↦ congrFun (h.multiDiff_update_add g i a b) 0)) c a)

theorem DiffVanish.form_apply {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) (g : Fin d → G)
    (x : G) : h.form g = multiDiff g φ x := h.multiDiff_eq g 0 x

theorem DiffVanish.form_comp_perm {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (σ : Equiv.Perm (Fin d)) : h.form (g ∘ σ) = h.form g := by
  rw [h.form_apply _ 0, h.form_apply _ 0, multiDiff_comp_equiv]

end Calculus

section Polarization

theorem multiDiff_polynomial_eval {R : Type*} [CommRing R] {d : ℕ} (z : Fin d → R)
    (p : Polynomial R) (hp : p.natDegree ≤ d) (y : R) :
    multiDiff z (fun t ↦ p.eval t) y = d.factorial * p.coeff d * ∏ i, z i := by
  induction d generalizing p with
  | zero =>
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]; simp
  | succ d ih =>
    rw [← Fin.cons_self_tail z, multiDiff_cons']
    set a := z 0
    have e : bwdDiff a (fun t ↦ p.eval t) =
        fun t ↦ (p - Polynomial.taylor (-a) p).eval t := by
      ext t; simp [bwdDiff, Polynomial.taylor_eval, sub_eq_add_neg]
    have hc : ∀ m, d + 1 ≤ m → (Polynomial.taylor (-a) p).coeff m = p.coeff m := fun m hm ↦ by
      have h0 : (Polynomial.hasseDeriv m p).natDegree ≤ 0 :=
        (Polynomial.natDegree_hasseDeriv_le p m).trans (by omega)
      rw [Polynomial.taylor_coeff, Polynomial.eq_C_of_natDegree_le_zero h0]
      simp [Polynomial.hasseDeriv_coeff]
    have hd : (Polynomial.taylor (-a) p).coeff d = p.coeff d - (d + 1) * p.coeff (d + 1) * a := by
      have h1 : (Polynomial.hasseDeriv d p).natDegree ≤ 1 :=
        (Polynomial.natDegree_hasseDeriv_le p d).trans (by omega)
      rw [Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
      simp [Polynomial.hasseDeriv_coeff, add_comm 1 d]
      ring
    rw [e, ih]
    · simp only [Polynomial.coeff_sub, hd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Nat.factorial_succ]
      push_cast; ring
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [Polynomial.coeff_sub, hc m hm, sub_self]

theorem diffVanish_polynomial_eval {R : Type*} [CommRing R] {d : ℕ} (p : Polynomial R)
    (hp : p.natDegree ≤ d) : DiffVanish (d + 1) (fun t ↦ p.eval t) := fun z ↦ by
  ext y
  rw [multiDiff_polynomial_eval z p (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  simp

theorem multiDiff_pow {R : Type*} [CommRing R] {d : ℕ} (z : Fin d → R) (y : R) :
    multiDiff z (fun t ↦ t ^ d) y = d.factorial * ∏ i, z i := by
  simpa using multiDiff_polynomial_eval z (Polynomial.X ^ d) (Polynomial.natDegree_X_pow_le d) y

theorem pow_sub_pow_mem_pow_succ {R : Type*} [CommRing R] {I : Ideal R} {a b : R} (ha : a ∈ I)
    (hb : b ∈ I) (hab : a - b ∈ I ^ 2) (d : ℕ) : a ^ d - b ^ d ∈ I ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have : a ^ (d + 1) - b ^ (d + 1) = a * (a ^ d - b ^ d) + (a - b) * b ^ d := by ring
    rw [this]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ']; exact Ideal.mul_mem_mul ha ih
    · rw [show d + 1 + 1 = 2 + d by ring, pow_add]
      exact Ideal.mul_mem_mul hab (Ideal.pow_mem_pow hb d)

variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem diffElt_sub_sum_mem {ι : Type*} (s : Finset ι) (g : ι → G) (x : G) :
    diffElt (x - ∑ i ∈ s, g i) - (diffElt x - ∑ i ∈ s, diffElt (g i)) ∈ diffIdeal G ^ 2 := by
  let f : G →+ AddMonoidAlgebra ℤ G ⧸ diffIdeal G ^ 2 :=
    AddMonoidHom.mk' (fun g ↦ Ideal.Quotient.mk _ (diffElt g)) fun a b ↦ by
      rw [← map_add, Ideal.Quotient.eq, diffElt_add, sub_sub_cancel_left, neg_mem_iff, sq]
      exact Ideal.mul_mem_mul (diffElt_mem a) (diffElt_mem b)
  have hf : ∀ g, Ideal.Quotient.mk _ (diffElt g) = f g := fun _ ↦ rfl
  rw [← Ideal.Quotient.eq]
  simp only [map_sub, map_sum, hf]

theorem DiffVanish.multiDiff_form_diag {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (x : G) :
    multiDiff g (fun y ↦ h.form fun _ ↦ y) x = d.factorial • h.form g := by
  have e : ∀ S : Finset (Fin d), (h.form fun _ ↦ x - ∑ i ∈ S, g i) =
      shiftAct G M ((diffElt x - ∑ i ∈ S, diffElt (g i)) ^ d) φ 0 := fun S ↦ by
    have := h.shiftAct_eq_zero (pow_sub_pow_mem_pow_succ (diffElt_mem _)
      (Ideal.sub_mem _ (diffElt_mem x) (Ideal.sum_mem _ fun i _ ↦ diffElt_mem (g i)))
      (diffElt_sub_sum_mem S g x) d)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [← this, h.form_apply _ 0, multiDiff_eq_shiftAct]
    simp
  have := multiDiff_pow (fun i ↦ diffElt (g i)) (diffElt x)
  rw [multiDiff_apply] at this
  rw [multiDiff_apply, h.form_apply _ 0, multiDiff_eq_shiftAct, ← Pi.smul_apply,
    ← LinearMap.smul_apply, ← map_nsmul, nsmul_eq_mul, ← this, map_sum, LinearMap.sum_apply,
    Finset.sum_apply]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [e, map_zsmul, LinearMap.smul_apply, Pi.smul_apply]

end Polarization

section Polynomial

variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]

theorem DiffVanish.sub_form_diag {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) :
    DiffVanish d (φ - fun y ↦ (d.factorial : K)⁻¹ * h.form fun _ ↦ y) := fun g ↦ by
  ext x
  have := congrFun (multiDiff_map (AddMonoidHom.mulLeft (d.factorial : K)⁻¹) g
    (fun y ↦ h.form fun _ ↦ y)) x
  simp only [Function.comp_def, AddMonoidHom.coe_mulLeft] at this
  have hd : (d.factorial : K) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  rw [multiDiff_sub, Pi.sub_apply, this, h.multiDiff_form_diag, ← h.form_apply, nsmul_eq_mul,
    inv_mul_cancel_left₀ hd, sub_self, Pi.zero_apply]

noncomputable def diffTopPoly (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G)
    (φ : G → K) (x : G) : MvPolynomial ι K :=
  ∑ a : Fin d → ι, MvPolynomial.C ((d.factorial : K)⁻¹ * multiDiff (g ∘ a) φ x) *
    ∏ j, MvPolynomial.X (a j)

omit [CharZero K] in
theorem isHomogeneous_diffTopPoly (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G)
    (φ : G → K) (x : G) : (diffTopPoly d g φ x).IsHomogeneous d := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ ↦ MvPolynomial.IsHomogeneous.C_mul ?_ _
  simpa using MvPolynomial.IsHomogeneous.prod univ (fun j : Fin d ↦ (MvPolynomial.X (a j) :
    MvPolynomial ι K)) (fun _ ↦ 1) fun j _ ↦ MvPolynomial.isHomogeneous_X K (a j)

omit [CharZero K] in
theorem DiffVanish.eval_diffTopPoly {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (g : ι → G) (x : G) (n : ι → ℤ) :
    MvPolynomial.eval (fun i ↦ (n i : K)) (diffTopPoly d g φ x) =
      (d.factorial : K)⁻¹ * h.form fun _ ↦ ∑ i, n i • g i := by
  rw [MultilinearMap.map_sum, mul_sum, diffTopPoly, map_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [MultilinearMap.map_smul_univ, ← h.form_apply]
  simp [Function.comp_def]
  ring

theorem exists_mvPolynomial_of_iteratedBackwardDifferenceVanish {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → G) (d : ℕ) : ∀ φ : G → K, DiffVanish (d + 1) φ → ∃ P : MvPolynomial ι K,
      P.totalDegree ≤ d ∧ (∀ n : ι → ℤ, P.eval (fun i ↦ (n i : K)) = φ (∑ i, n i • g i)) ∧
      MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ 0 := by
  induction d with
  | zero =>
    intro φ h
    have h0 := isHomogeneous_diffTopPoly 0 g φ 0
    refine ⟨diffTopPoly 0 g φ 0, h0.totalDegree_le, fun n ↦ ?_, ?_⟩
    · rw [h.eval_diffTopPoly, h.form_apply _ (∑ i, n i • g i)]; simp
    · rw [MvPolynomial.homogeneousComponent_of_mem h0, if_pos rfl]
  | succ d ih =>
    intro φ h
    obtain ⟨Q, hQ, hQ', -⟩ := ih _ h.sub_form_diag
    have h0 := isHomogeneous_diffTopPoly (d + 1) g φ 0
    refine ⟨Q + diffTopPoly (d + 1) g φ 0, (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by omega) h0.totalDegree_le), fun n ↦ ?_, ?_⟩
    · rw [map_add, hQ', h.eval_diffTopPoly]; simp
    · rw [map_add, MvPolynomial.homogeneousComponent_of_mem h0, if_pos rfl,
        MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), zero_add]

theorem DiffVanish.exists_mvPolynomial {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G) (x : G) : ∃ P : MvPolynomial ι K,
      P.totalDegree ≤ d ∧ (∀ n : ι → ℤ, P.eval (fun i ↦ (n i : K)) = φ (x + ∑ i, n i • g i)) ∧
      MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ x ∧
      ∀ n : ι → ℤ, (MvPolynomial.homogeneousComponent d P).eval (fun i ↦ (n i : K)) =
        (d.factorial : K)⁻¹ * h.form fun _ ↦ ∑ i, n i • g i := by
  obtain ⟨P, h1, h2, h3⟩ := exists_mvPolynomial_of_iteratedBackwardDifferenceVanish g d _ (h.translate x)
  have h4 : MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ x := by
    rw [h3]; simp only [diffTopPoly, multiDiff_translate, add_zero]
  exact ⟨P, h1, h2, h4, fun n ↦ by rw [h4, h.eval_diffTopPoly]⟩

theorem DiffVanish.exists_polynomial {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) (a x : G) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = φ (x + n • a)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * multiDiff (fun _ : Fin d ↦ a) φ x := by
  obtain ⟨P, h1, h2, -, -⟩ := h.exists_mvPolynomial (fun _ : Unit ↦ a) x
  let p : Polynomial K := MvPolynomial.aeval (fun _ ↦ Polynomial.X) P
  have hp : p.natDegree ≤ d := by
    simpa using MvPolynomial.aeval_natDegree_le P h1 (fun _ ↦ Polynomial.X) (n := 1)
      (fun _ ↦ Polynomial.natDegree_X_le)
  have he : ∀ n : ℤ, p.eval (n : K) = φ (x + n • a) := fun n ↦ by
    have := h2 fun _ ↦ n
    simp only [univ_unique, sum_singleton] at this
    rw [← this, ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp [MvPolynomial.aeval_eq_eval]
  refine ⟨p, hp, he, ?_⟩
  have hd : (d.factorial : K) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  have e1 := multiDiff_polynomial_eval (fun _ : Fin d ↦ (1 : K)) p hp 0
  have e2 := congrFun (multiDiff_comap (Int.castAddHom K) (fun _ : Fin d ↦ (1 : ℤ))
    (fun t ↦ p.eval t)) 0
  have e3 := congrFun (multiDiff_comap (zmultiplesHom G a) (fun _ : Fin d ↦ (1 : ℤ))
    (fun y ↦ φ (x + y))) 0
  simp only [Function.comp_def, Int.coe_castAddHom, Int.cast_one, Int.cast_zero, he,
    zmultiplesHom_apply, one_smul, zero_smul, multiDiff_translate, add_zero] at e2 e3
  rw [← e3, e2, e1]
  simp [hd]

theorem DiffVanish.exists_polynomial_int {d : ℕ} {φ : G → ℤ} (h : DiffVanish (d + 1) φ)
    (K : Type*) [Field K] [CharZero K] (a x : G) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = φ (x + n • a)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * multiDiff (fun _ : Fin d ↦ a) φ x := by
  obtain ⟨p, h1, h2, h3⟩ := (h.map (Int.castAddHom K)).exists_polynomial a x
  exact ⟨p, h1, h2, by rw [h3, multiDiff_map]; rfl⟩

end Polynomial

theorem diffVanish_pow_int (d : ℕ) :
    DiffVanish (d + 1) (fun t : ℤ ↦ t ^ d) ∧ ¬ DiffVanish d (fun t : ℤ ↦ t ^ d) := by
  refine ⟨by simpa using (diffVanish_polynomial_eval (Polynomial.X ^ d : Polynomial ℤ)
    (Polynomial.natDegree_X_pow_le d)), fun h ↦ ?_⟩
  have := congrFun (h fun _ ↦ 1) 0
  rw [multiDiff_pow] at this
  simp [Nat.factorial_ne_zero] at this

end GlobalTheory
