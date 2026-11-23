import Mathlib

open Polynomial Module

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

variable {C : Type} [Field C]

abbrev Int0 (v : AddValuation C (WithTop ℝ)) : Subring C :=
  (AddValuation.toValuation v).integer

theorem mem_addValuationIntegerRing_iff (v : AddValuation C (WithTop ℝ)) (x : C) : x ∈ Int0 v ↔ 0 ≤ v x := Iff.rfl

def RelLen (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M] [Module (Int0 v) M]
    (X' X : Submodule (Int0 v) M) (r : ℝ) : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
    (A : Matrix (Fin n) (Fin n) (Int0 v)),
    (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) ∧ v (A.det : C) = (r : WithTop ℝ)

section Ring

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

abbrev RS (a : S → O) : Type := AdjoinRoot (∏ s, (X - Polynomial.C (a s)) : O[X])

def lin (a : S → O) (s : S) : RS a := AdjoinRoot.root _ - algebraMap O (RS a) (a s)

def cofac (a : S → O) (τ : S) : RS a := ∏ s ∈ Finset.univ.erase τ, lin a s

def ev (a : S → O) (s : S) : RS a →ₐ[O] O :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id O O) (a s) (by
    rw [Polynomial.eval₂_finset_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp))

def comp (a : S → O) (N : ℕ) (s : S) : (Fin N → RS a) →ₗ[O] (Fin N → O) :=
  (ev a s).toLinearMap.compLeft (Fin N)

def kerMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.ker (LinearMap.lsmul (RS a) M r)).restrictScalars O

def imMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.range (LinearMap.lsmul (RS a) M r)).restrictScalars O

def eigSub (a : S → O) (τ : S) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  kerMul a (lin a τ) M

def eigQuot (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) (s : S) :
    Submodule O (Fin N → O) :=
  (X.restrictScalars O).map (comp a N s)

def incl (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) : X →ₗ[O] (Fin N → RS a) :=
  X.subtype.restrictScalars O

def proj (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) :
    (Fin N → RS a) →ₗ[O] ((Fin N → RS a) ⧸ X) :=
  X.mkQ.restrictScalars O

theorem ev_lin (a : S → O) (s t : S) : ev a s (lin a t) = a s - a t := by
  simp [ev, lin]

end Ring

variable {S : Type} [Fintype S] [DecidableEq S]

def eigRank (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (X : Submodule (RS a) (Fin N → RS a)) (s : S) : ℕ :=
  finrank C (Submodule.span C
    ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (eigQuot a X s : Set (Fin N → Int0 v))))

def vd (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) (τ : S) : WithTop ℝ :=
  v (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)))

def yExp (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : WithTop ℝ :=
  ∑ s ∈ Finset.univ.erase τ, eigRank v a Fil s • v ((a s : C) - (a τ : C))

def DetIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ p : ℕ, p + eigRank v a Fil τ = N ∧
    Nonempty (Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a))) ∧
    Nonempty (Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))) ∧
    Nonempty (Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ)) ∧
    ∀ (h : Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a)))
      (l : Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
      (x : Fin p → (Fin N → RS a))
      (_ : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
      (f : Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ))
      (e : Fin N ≃ Fin p ⊕ Fin (eigRank v a Fil τ)),
      ∃ c : C, v c = yExp v a Fil τ ∧
        (Matrix.of fun k : Fin N =>
          Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det ≠ 0 ∧
        ((Matrix.of fun k : Fin N => comp a N τ (h k : Fin N → RS a)).det : C) =
          c * ((Matrix.of fun k : Fin N =>
            Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det : C)

def KernelIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  (eigSub a τ (Fin N → RS a)).map (proj a Fil) ≤ eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧
  eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (proj a Fil) = (eigSub a τ Fil).map (incl a Fil)

def LengthIdentities (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ δ e₂ m : ℝ,
    RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ ∧
    RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ ∧
    RelLen v (imMul a (cofac a τ) Fil) (eigSub a τ Fil) e₂ ∧
    RelLen v ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) (eigQuot a Fil τ) m ∧
    ((m + e₂ : ℝ) : WithTop ℝ) = eigRank v a Fil τ • vd v a τ ∧
    ((∀ s, eigRank v a Fil s = eigRank v a Fil τ) →
      0 ≤ δ ∧ (δ : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ ∧
      0 ≤ m ∧ (m : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ)

def HerbrandDet : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a →
    ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)),
      (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) →
      ∀ τ : S, DetIdentity v a Fil τ ∧ KernelIdentity v a Fil τ ∧ LengthIdentities v a Fil τ

theorem v_unit (v : AddValuation C (WithTop ℝ)) {u : Int0 v} (hu : IsUnit u) : v (u : C) = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : v (u : C) + v (w : C) = 0 := by
    rw [← v.map_mul, ← Subring.coe_mul, hw]; simp
  have hu0 : 0 ≤ v (u : C) := u.2
  have hw0 : 0 ≤ v (w : C) := w.2
  refine le_antisymm ?_ hu0
  calc v (u : C) ≤ v (u : C) + v (w : C) := le_add_of_nonneg_right hw0
    _ = 0 := h1

theorem RelLen.unique (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
    [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r r' : ℝ}
    (h : RelLen v X' X r) (h' : RelLen v X' X r') : r = r' := by
  obtain ⟨n, b, b', A, hA, hr⟩ := h
  obtain ⟨m, c, c', B, hB, hr'⟩ := h'
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  subst hnm
  have hle : X' ≤ X := by
    intro x hx
    have : (x : M) = ∑ k, b'.repr ⟨x, hx⟩ k • (b' k : M) := by
      have := congrArg X'.subtype (b'.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      exact this.symm
    rw [this]
    refine X.sum_mem fun k _ => X.smul_mem _ ?_
    rw [hA k]
    exact X.sum_mem fun i _ => X.smul_mem _ (b i).2
  have key : ∀ (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
      (A : Matrix (Fin n) (Fin n) (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  have : v (A.det : C) = v (B.det : C) := by
    rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
      v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]
  rw [hr, hr'] at this
  exact_mod_cast this

end GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity
