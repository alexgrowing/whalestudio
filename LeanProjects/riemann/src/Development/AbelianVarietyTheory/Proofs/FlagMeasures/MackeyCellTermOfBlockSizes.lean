import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel

noncomputable section

namespace GlobalTheory.GLm.Cell

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem entN_fun {n : ℕ} (f : ℕ → ℕ → ZMod g) {u v : ℕ} (hu : u < n) (hv : v < n) :
    entN (show Mt g n from fun i j : Fin n => f i j) u v = f u v := by
  simp [entN, hu, hv]

theorem entN_fin {n : ℕ} (M : Mt g n) (u v : Fin n) : entN M u v = M u v := by
  simp [entN]

theorem mt_ext {n : ℕ} {M N : Mt g n} (h : ∀ u v, u < n → v < n → entN M u v = entN N u v) : M = N := by
  ext i j
  rw [← entN_fin M, ← entN_fin N]; exact h _ _ i.2 j.2

theorem inPar_iff {a n : ℕ} (M : Mt g n) : InPar a M ↔ ∀ u v, v < a → a ≤ u → u < n → entN M u v = 0 := by
  constructor
  · intro h u v hv hu hn
    have := h ⟨u, hn⟩ ⟨v, by omega⟩ hv hu
    rw [← entN_fin M] at this; exact this
  · intro h i j hj hi
    rw [← entN_fin M]; exact h _ _ hj hi i.2

theorem entN_tl {a n : ℕ} (M : Mt g n) {u v : ℕ} (hu : u < a) (hv : v < a) : entN (tl a M) u v = entN M u v :=
  entN_fun (fun i j => entN M i j) hu hv

theorem entN_br {a b n : ℕ} (M : Mt g n) {u v : ℕ} (hu : u < b) (hv : v < b) :
    entN (br a b M) u v = entN M (a + u) (a + v) :=
  entN_fun (fun i j => entN M (a + i) (a + j)) hu hv

theorem coe_toG {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := Units.ext (coe_toG x.isUnit)

theorem isUnit_of_blocks {a b : ℕ} (M : Mt g (a + b)) (h : InPar a M) (h₁ : IsUnit (tl a M))
    (h₂ : IsUnit (br a b M)) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det] at *
  have e : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (tl a M)
      (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 (br a b M) := by
    ext (i | i) (j | j)
    · exact (entN_fin M (Fin.castAdd b i) (Fin.castAdd b j)).symm
    · rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      exact h _ _ (by simp) (by simp)
    · exact (entN_fin M (Fin.natAdd a i) (Fin.natAdd a j)).symm
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, e, Matrix.det_fromBlocks_zero₂₁]
  exact h₁.mul h₂

def cj (a c i : ℕ) {n : ℕ} (M : Mt g n) : Mt g n := fun u v => entN M (sigI a c i u) (sigI a c i v)

theorem entN_cj (a c i : ℕ) {n : ℕ} (M : Mt g n) {u v : ℕ} (hu : u < n) (hv : v < n) :
    entN (cj a c i M) u v = entN M (sigI a c i u) (sigI a c i v) :=
  entN_fun (fun u v => entN M (sigI a c i u) (sigI a c i v)) hu hv

theorem coe_conj (a c i n : ℕ) (ha : i ≤ a) (hc : i ≤ c) (hn : a + c ≤ n + i) (x : Gn g n) :
    (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n) = cj a c i (x : Mt g n) := by
  have hlt : ∀ j : Fin n, sigI a c i j < n := by
    intro j; have := j.2; simp only [sigI]; split_ifs <;> omega
  let f : Fin n → Fin n := fun j => ⟨sigI a c i j, hlt j⟩
  have hf : Function.Injective f := by
    intro j j' h
    have h := congrArg Fin.val h
    simp only [f, sigI] at h
    apply Fin.ext
    split_ifs at h <;> omega
  let W : Mt g n := fun r j => if (r : ℕ) = sigI a c i j then 1 else 0
  have hW : ∀ r j, W r j = if r = f j then 1 else 0 := by
    intro r j; simp [W, f, Fin.ext_iff]
  have hm : ∀ M : Mt g n, W.transpose * M * W = cj a c i M := by
    intro M
    ext u v
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hW, ite_mul, mul_ite, one_mul, mul_one, zero_mul,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (entN_fin M (f u) (f v)).symm
  have h1 : W.transpose * W = 1 := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hW, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply, hf.eq_iff]
  have hu : IsUnit W := IsUnit.of_mul_eq_one_right _ h1
  have e : ((wI g a c i n : Gn g n) : Mt g n) = W := coe_toG hu
  have e' : (((wI g a c i n)⁻¹ : Gn g n) : Mt g n) = W.transpose := by
    rw [Matrix.coe_units_inv, e]; exact Matrix.inv_eq_left_inv h1
  rw [Units.val_mul, Units.val_mul, e, e', hm]

def bld {R : Type} [Zero R] (p q r : ℕ) (Z Z' T T' E : ℕ → ℕ → R) (u v : ℕ) : R :=
  if u < p + q then
    (if v < p + q then Z u v else if u < p then
      (if v < p + q + r then T u (v - q) else E u (v - (p + q + r)))
      else (if v < p + q + r then 0 else T' (u - p) (v - (p + r))))
  else (if v < p + q then 0 else Z' (u - (p + q)) (v - (p + q)))

def entR {p s : ℕ} (E : Fin p → Fin s → ZMod g) (u v : ℕ) : ZMod g :=
  if h : u < p ∧ v < s then E ⟨u, h.1⟩ ⟨v, h.2⟩ else 0

def Ov (a b : ℕ) {n : ℕ} (x : Mt g n) (h₁ : Mt g a) (h₂ : Mt g b) : Prop :=
  InPar a x ∧ tl a x = h₁ ∧ br a b x = h₂

theorem Ov.z {a b n : ℕ} {x : Mt g n} {h₁ : Mt g a} {h₂ : Mt g b} (h : Ov a b x h₁ h₂) (u v : ℕ)
    (hv : v < a) (hu : a ≤ u) (hn : u < n) : entN x u v = 0 := (inPar_iff x).1 h.1 u v hv hu hn

theorem Ov.tt {a b n b' n' : ℕ} {x : Mt g n} {h₁ : Mt g a} {h₂ : Mt g b} (h : Ov a b x h₁ h₂)
    {x' : Mt g n'} {h₂' : Mt g b'} (h' : Ov a b' x' h₁ h₂') (u v u' v' : ℕ)
    (hv : v < a) (hu : u < a) (e : u = u') (e' : v = v') : entN x u v = entN x' u' v' := by
  subst e e'
  rw [← entN_tl x hu hv, ← entN_tl x' hu hv, h.2.1, h'.2.1]

theorem Ov.bt {a b n b' n' : ℕ} {x : Mt g n} {h₁ : Mt g a} {h₂ : Mt g b} (h : Ov a b x h₁ h₂)
    {x' : Mt g n'} {h₂' : Mt g b'} (h' : Ov b b' x' h₂ h₂') (u v u' v' : ℕ)
    (hv : v' < b) (hu : u' < b) (e : u = a + u') (e' : v = a + v') : entN x u v = entN x' u' v' := by
  subst e e'
  rw [← entN_br x hu hv, ← entN_tl x' hu hv, h.2.2, h'.2.1]

theorem Ov.bb {a b n a' n' : ℕ} {x : Mt g n} {h₁ : Mt g a} {h₂ : Mt g b} (h : Ov a b x h₁ h₂)
    {x' : Mt g n'} {h₁' : Mt g a'} (h' : Ov a' b x' h₁' h₂) (u v u' v' : ℕ)
    (hv : v < a + b) (hu : u < a + b) (hv' : a ≤ v) (hu' : a ≤ u) (e : u' + a = a' + u) (e' : v' + a = a' + v) :
    entN x u v = entN x' u' v' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hu'
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hv'
  obtain rfl : u' = a' + k := by omega
  obtain rfl : v' = a' + l := by omega
  rw [← entN_br x (b := b) (by omega) (by omega), ← entN_br x' (b := b) (by omega) (by omega), h.2.2, h'.2.2]

def bM (p q r s : ℕ) (z : Mt g (p + q)) (z' : Mt g (r + s)) (t : Mt g (p + r)) (t' : Mt g (q + s))
    (E : Fin p → Fin s → ZMod g) : Mt g (p + q + (r + s)) :=
  fun u v => bld p q r (entN z) (entN z') (entN t) (entN t') (entR E) u v

def cor (p q r s : ℕ) {n : ℕ} (M : Mt g n) : Fin p → Fin s → ZMod g := fun u v => entN M u (p + q + r + v)

theorem entN_bM {p q r s : ℕ} (z : Mt g (p + q)) (z' : Mt g (r + s)) (t : Mt g (p + r)) (t' : Mt g (q + s))
    (E : Fin p → Fin s → ZMod g) {u v : ℕ} (hu : u < p + q + (r + s)) (hv : v < p + q + (r + s)) :
    entN (bM p q r s z z' t t' E) u v = bld p q r (entN z) (entN z') (entN t) (entN t') (entR E) u v :=
  entN_fun _ hu hv

theorem sig_cases (p q r j : ℕ) : ∃ k, sigI (p + r) (p + q) p j = k ∧
    ((j < p ∧ k = j) ∨ (p ≤ j ∧ j < p + r ∧ k = j + q) ∨ (p + r ≤ j ∧ j < p + r + q ∧ k + r = j) ∨
      (p + r + q ≤ j ∧ k = j)) := by
  refine ⟨_, rfl, ?_⟩
  simp only [sigI]; split_ifs <;> omega

theorem bM_spec {p q r s : ℕ} {z : Mt g (p + q)} {z' : Mt g (r + s)} {t : Mt g (p + r)} {t' : Mt g (q + s)}
    (E : Fin p → Fin s → ZMod g) {y₁ : Mt g p} {y₂ : Mt g r} {y₃ : Mt g q} {y₄ : Mt g s}
    (hz : Ov p q z y₁ y₃) (hz' : Ov r s z' y₂ y₄) (ht : Ov p r t y₁ y₂) (ht' : Ov q s t' y₃ y₄) :
    Ov (p + q) (r + s) (bM p q r s z z' t t' E) z z' ∧
    Ov (p + r) (q + s) (cj (p + r) (p + q) p (bM p q r s z z' t t' E)) t t' ∧
    cor p q r s (bM p q r s z z' t t' E) = E := by
  have hs : ∀ j, j < p + q + (r + s) → sigI (p + r) (p + q) p j < p + q + (r + s) := by
    intro j hj; simp only [sigI]; split_ifs <;> omega
  refine ⟨⟨(inPar_iff _).2 ?_, mt_ext ?_, mt_ext ?_⟩, ⟨(inPar_iff _).2 ?_, mt_ext ?_, mt_ext ?_⟩, ?_⟩
  · intro u v hv hu hn
    rw [entN_bM _ _ _ _ _ hn (by omega), bld, if_neg (by omega), if_pos hv]
  · intro u v hu hv
    rw [entN_tl _ hu hv, entN_bM _ _ _ _ _ (by omega) (by omega), bld, if_pos hu, if_pos hv]
  · intro u v hu hv
    rw [entN_br _ hu hv, entN_bM _ _ _ _ _ (by omega) (by omega), bld, if_neg (by omega), if_neg (by omega)]
    congr 1 <;> omega
  · intro u v hv hu hn
    rw [entN_cj _ _ _ _ hn (by omega), entN_bM _ _ _ _ _ (hs _ hn) (hs _ (by omega))]
    obtain ⟨u', hu', cu⟩ := sig_cases p q r u
    obtain ⟨v', hv', cv⟩ := sig_cases p q r v
    rw [hu', hv', bld]
    split_ifs <;> first | rfl | omega | (apply hz.z <;> omega) | (apply hz'.z <;> omega)
  · intro u v hu hv
    rw [entN_tl _ hu hv, entN_cj _ _ _ _ (by omega) (by omega),
      entN_bM _ _ _ _ _ (hs _ (by omega)) (hs _ (by omega))]
    obtain ⟨u', hu', cu⟩ := sig_cases p q r u
    obtain ⟨v', hv', cv⟩ := sig_cases p q r v
    rw [hu', hv', bld]
    split_ifs <;> first | omega | (apply hz.tt ht <;> omega) | (symm; apply ht.z <;> omega) | (symm; apply ht.bt hz' <;> omega) | (congr 1 <;> omega)
  · intro u v hu hv
    rw [entN_br _ hu hv, entN_cj _ _ _ _ (by omega) (by omega),
      entN_bM _ _ _ _ _ (hs _ (by omega)) (hs _ (by omega))]
    obtain ⟨u', hu', cu⟩ := sig_cases p q r (p + r + u)
    obtain ⟨v', hv', cv⟩ := sig_cases p q r (p + r + v)
    rw [hu', hv', bld]
    split_ifs <;> first | omega | (apply hz.bt ht' <;> omega) | (symm; apply ht'.z <;> omega) | (apply hz'.bb ht' <;> omega) | (congr 1 <;> omega)
  · funext u v
    have := u.2
    have := v.2
    rw [cor, entN_bM _ _ _ _ _ (by omega) (by omega), bld, if_pos (by omega), if_neg (by omega), if_pos u.2,
      if_neg (by omega)]
    simp [entR]

theorem blocks_spec {p q r s : ℕ} {M : Mt g (p + q + (r + s))} (h : InPar (p + q) M)
    (h' : InPar (p + r) (cj (p + r) (p + q) p M)) :
    Ov p q (tl (p + q) M) (tl p M) (br p q M) ∧
    Ov r s (br (p + q) (r + s) M) (br (p + q) r M) (br (p + q + r) s M) ∧
    Ov p r (tl (p + r) (cj (p + r) (p + q) p M)) (tl p M) (br (p + q) r M) ∧
    Ov q s (br (p + r) (q + s) (cj (p + r) (p + q) p M)) (br p q M) (br (p + q + r) s M) ∧
    bM p q r s (tl (p + q) M) (br (p + q) (r + s) M) (tl (p + r) (cj (p + r) (p + q) p M))
      (br (p + r) (q + s) (cj (p + r) (p + q) p M)) (cor p q r s M) = M := by
  have hc : ∀ u v u' v', u < p + q + (r + s) → v < p + q + (r + s) →
      ((u < p ∧ u' = u) ∨ (p ≤ u ∧ u < p + r ∧ u' = u + q) ∨ (p + r ≤ u ∧ u < p + r + q ∧ u' + r = u) ∨
        (p + r + q ≤ u ∧ u' = u)) →
      ((v < p ∧ v' = v) ∨ (p ≤ v ∧ v < p + r ∧ v' = v + q) ∨ (p + r ≤ v ∧ v < p + r + q ∧ v' + r = v) ∨
        (p + r + q ≤ v ∧ v' = v)) → entN (cj (p + r) (p + q) p M) u v = entN M u' v' := by
    intro u v u' v' hu hv cu cv
    obtain ⟨u'', hu', cu'⟩ := sig_cases p q r u
    obtain ⟨v'', hv', cv'⟩ := sig_cases p q r v
    rw [entN_cj _ _ _ _ hu hv, hu', hv']
    congr 1 <;> omega
  rw [inPar_iff] at h h'
  have z₁ : ∀ u v, v < p → p ≤ u → u < p + q → entN M u v = 0 := fun u v _ _ _ => by
    rw [← hc (u + r) v u v (by omega) (by omega) (by omega) (by omega)]; apply h' <;> omega
  have z₂ : ∀ u v, p + q ≤ v → v < p + q + r → p ≤ u → u < p + q → entN M u v = 0 := fun u v _ _ _ _ => by
    rw [← hc (u + r) (v - q) u v (by omega) (by omega) (by omega) (by omega)]; apply h' <;> omega
  have z₃ : ∀ u v, p + q ≤ v → v < p + q + r → p + q + r ≤ u → u < p + q + (r + s) → entN M u v = 0 :=
    fun u v _ _ _ _ => by
    rw [← hc u (v - q) u v (by omega) (by omega) (by omega) (by omega)]; apply h' <;> omega
  refine ⟨⟨(inPar_iff _).2 ?_, mt_ext ?_, mt_ext ?_⟩, ⟨(inPar_iff _).2 ?_, mt_ext ?_, mt_ext ?_⟩,
    ⟨(inPar_iff _).2 ?_, mt_ext ?_, mt_ext ?_⟩, ⟨(inPar_iff _).2 ?_, mt_ext ?_, mt_ext ?_⟩, mt_ext ?_⟩
  · intro u v _ _ _
    rw [entN_tl _ (by omega) (by omega)]; apply z₁ <;> omega
  · intro u v hu hv
    rw [entN_tl _ hu hv, entN_tl _ hu hv, entN_tl _ (by omega) (by omega)]
  · intro u v hu hv
    rw [entN_br _ hu hv, entN_br _ hu hv, entN_tl _ (by omega) (by omega)]
  · intro u v _ _ _
    rw [entN_br _ (by omega) (by omega)]; apply z₃ <;> omega
  · intro u v hu hv
    rw [entN_tl _ hu hv, entN_br _ hu hv, entN_br _ (by omega) (by omega)]
  · intro u v hu hv
    rw [entN_br _ hu hv, entN_br _ hu hv, entN_br _ (by omega) (by omega)]
    congr 1 <;> omega
  · intro u v _ _ _
    rw [entN_tl _ (by omega) (by omega), hc u v (u + q) v (by omega) (by omega) (by omega) (by omega)]
    apply h <;> omega
  · intro u v hu hv
    rw [entN_tl _ hu hv, entN_tl _ hu hv, entN_tl _ (by omega) (by omega)]
    apply hc <;> omega
  · intro u v hu hv
    rw [entN_br _ hu hv, entN_br _ hu hv, entN_tl _ (by omega) (by omega)]
    apply hc <;> omega
  · intro u v _ _ _
    rw [entN_br _ (by omega) (by omega),
      hc _ _ (p + r + u) (p + v) (by omega) (by omega) (by omega) (by omega)]
    apply h <;> omega
  · intro u v hu hv
    rw [entN_tl _ hu hv, entN_br _ hu hv, entN_br _ (by omega) (by omega)]
    apply hc <;> omega
  · intro u v hu hv
    rw [entN_br _ hu hv, entN_br _ hu hv, entN_br _ (by omega) (by omega)]
    apply hc <;> omega
  · intro u v hu hv
    rw [entN_bM _ _ _ _ _ hu hv, bld]
    split_ifs
    · rw [entN_tl _ (by omega) (by omega)]
    · rw [entN_tl _ (by omega) (by omega)]; apply hc <;> omega
    · rw [entR, dif_pos ⟨by omega, by omega⟩, cor]; congr 1; simp only; omega
    · symm; apply z₂ <;> omega
    · rw [entN_br _ (by omega) (by omega)]; apply hc <;> omega
    · symm; apply h <;> omega
    · rw [entN_br _ (by omega) (by omega)]; congr 1 <;> omega

abbrev Tup (g p q r s : ℕ) : Type :=
  (Fin p → Fin s → ZMod g) × ((Gn g p × Gn g r) × (Gn g q × Gn g s)) ×
    Gn g (p + q) × Gn g (r + s) × Gn g (p + r) × Gn g (q + s)

def Good {p q r s : ℕ} (τ : Tup g p q r s) : Prop :=
  Ov p q (τ.2.2.1 : Mt g (p + q)) τ.2.1.1.1 τ.2.1.2.1 ∧ Ov r s (τ.2.2.2.1 : Mt g (r + s)) τ.2.1.1.2 τ.2.1.2.2 ∧
    Ov p r (τ.2.2.2.2.1 : Mt g (p + r)) τ.2.1.1.1 τ.2.1.1.2 ∧ Ov q s (τ.2.2.2.2.2 : Mt g (q + s)) τ.2.1.2.1 τ.2.1.2.2

def asm {p q r s : ℕ} (τ : Tup g p q r s) : Mt g (p + q + (r + s)) :=
  bM p q r s τ.2.2.1 τ.2.2.2.1 τ.2.2.2.2.1 τ.2.2.2.2.2 τ.1

set_option synthInstance.maxSize 2000 in
theorem sum_cell (p q r s : ℕ) (Λ : Gn g (p + q) → Gn g (r + s) → ℂ) (Φ : Gn g (p + r) → Gn g (q + s) → ℂ) :
    (∑ τ : Tup g p q r s, if Good τ then Λ τ.2.2.1 τ.2.2.2.1 * Φ τ.2.2.2.2.1 τ.2.2.2.2.2 else 0) =
    ∑ x : Gn g (p + q + (r + s)), if InPar (p + q) (x : Mt g (p + q + (r + s))) ∧
        InPar (p + r) (cj (p + r) (p + q) p (x : Mt g (p + q + (r + s)))) then
      Λ (toG (tl (p + q) (x : Mt g (p + q + (r + s))))) (toG (br (p + q) (r + s) (x : Mt g (p + q + (r + s))))) *
      Φ (toG (tl (p + r) (cj (p + r) (p + q) p (x : Mt g (p + q + (r + s))))))
        (toG (br (p + r) (q + s) (cj (p + r) (p + q) p (x : Mt g (p + q + (r + s)))))) else 0 := by
  have key : ∀ τ : Tup g p q r s, Good τ → ((toG (asm τ) : Gn g _) : Mt g _) = asm τ ∧
      Ov (p + q) (r + s) (asm τ) τ.2.2.1 τ.2.2.2.1 ∧
      Ov (p + r) (q + s) (cj (p + r) (p + q) p (asm τ)) τ.2.2.2.2.1 τ.2.2.2.2.2 ∧ cor p q r s (asm τ) = τ.1 := by
    intro τ h
    have k := bM_spec τ.1 h.1 h.2.1 h.2.2.1 h.2.2.2
    refine ⟨coe_toG (isUnit_of_blocks _ k.1.1 ?_ ?_), k⟩
    · rw [asm, k.1.2.1]; exact Units.isUnit _
    · rw [asm, k.1.2.2]; exact Units.isUnit _
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun τ _ => toG (asm τ)) ?_ ?_ ?_ ?_
  · intro τ hτ
    have k := key τ (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [k.1]; exact ⟨k.2.1.1, k.2.2.1.1⟩
  · intro τ hτ τ' hτ' e
    have h := (Finset.mem_filter.1 hτ).2
    have h' := (Finset.mem_filter.1 hτ').2
    have k := key τ h
    have k' := key τ' h'
    have e' : asm τ = asm τ' := by rw [← k.1, ← k'.1]; exact congrArg Units.val e
    rw [e'] at k
    obtain ⟨E, ⟨⟨y₁, y₂⟩, y₃, y₄⟩, z, z', t, t'⟩ := τ
    obtain ⟨E', ⟨⟨w₁, w₂⟩, w₃, w₄⟩, Z, Z', T, T'⟩ := τ'
    obtain rfl : E = E' := k.2.2.2.symm.trans k'.2.2.2
    obtain rfl : z = Z := Units.ext (k.2.1.2.1.symm.trans k'.2.1.2.1)
    obtain rfl : z' = Z' := Units.ext (k.2.1.2.2.symm.trans k'.2.1.2.2)
    obtain rfl : t = T := Units.ext (k.2.2.1.2.1.symm.trans k'.2.2.1.2.1)
    obtain rfl : t' = T' := Units.ext (k.2.2.1.2.2.symm.trans k'.2.2.1.2.2)
    obtain rfl : y₁ = w₁ := Units.ext (h.1.2.1.symm.trans h'.1.2.1)
    obtain rfl : y₃ = w₃ := Units.ext (h.1.2.2.symm.trans h'.1.2.2)
    obtain rfl : y₂ = w₂ := Units.ext (h.2.1.2.1.symm.trans h'.2.1.2.1)
    obtain rfl : y₄ = w₄ := Units.ext (h.2.1.2.2.symm.trans h'.2.1.2.2)
    rfl
  · intro x hx
    obtain ⟨h, h'⟩ := (Finset.mem_filter.1 hx).2
    obtain ⟨b₁, b₂, b₃, b₄, b₅⟩ := blocks_spec h h'
    obtain ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ := (GlobalTheory.GLm.ParBasic.par_basic g (p + q) (r + s) _ rfl).2.2.1 x h
    have ec := coe_conj (p + r) (p + q) p (p + q + (r + s)) (by omega) (by omega) (by omega) x
    obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ := (GlobalTheory.GLm.ParBasic.par_basic g (p + r) (q + s) _ (by omega)).2.2.1 _ (ec ▸ h')
    rw [ec] at ht ht'
    rw [← hz] at b₁ b₅
    rw [← hz'] at b₂ b₅
    rw [← ht] at b₃ b₅
    rw [← ht'] at b₄ b₅
    obtain ⟨⟨y₁, hy₁⟩, ⟨y₃, hy₃⟩⟩ := (GlobalTheory.GLm.ParBasic.par_basic g p q _ rfl).2.2.1 z b₁.1
    obtain ⟨⟨y₂, hy₂⟩, ⟨y₄, hy₄⟩⟩ := (GlobalTheory.GLm.ParBasic.par_basic g r s _ rfl).2.2.1 z' b₂.1
    rw [b₁.2.1] at hy₁
    rw [b₁.2.2] at hy₃
    rw [b₂.2.1] at hy₂
    rw [b₂.2.2] at hy₄
    rw [← hy₁, ← hy₃] at b₁
    rw [← hy₂, ← hy₄] at b₂
    rw [← hy₁, ← hy₂] at b₃
    rw [← hy₃, ← hy₄] at b₄
    refine ⟨(cor p q r s x.val, ((y₁, y₂), (y₃, y₄)), z, z', t, t'),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, b₁, b₂, b₃, b₄⟩, ?_⟩
    show toG (bM p q r s _ _ _ _ _) = x
    rw [b₅, toG_coe]
  · intro τ hτ
    have k := key τ (Finset.mem_filter.1 hτ).2
    rw [k.1, k.2.1.2.1, k.2.1.2.2, k.2.2.1.2.1, k.2.2.1.2.2]
    simp only [toG_coe]

set_option synthInstance.maxSize 2000 in
theorem sum_tup (p q r s : ℕ) (Λ : Gn g (p + q) → Gn g (r + s) → ℂ) (Φ : Gn g (p + r) → Gn g (q + s) → ℂ) :
    (∑ τ : Tup g p q r s, if Good τ then Λ τ.2.2.1 τ.2.2.2.1 * Φ τ.2.2.2.2.1 τ.2.2.2.2.2 else 0) =
    (Fintype.card (Fin p → Fin s → ZMod g) * ((g : ℂ) ^ (p * q) * g ^ (r * s) * g ^ (p * r) * g ^ (q * s))) *
      ∑ y : (Gn g p × Gn g r) × (Gn g q × Gn g s),
        res p q (fun z => res r s (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
          res p r (fun x => res q s (Φ x) y.2.1 y.2.2) y.1.1 y.1.2 := by
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hres : ∀ (a b n : ℕ) (χ : Gn g n → ℂ) h₁ h₂, (g : ℂ) ^ (a * b) * res a b χ h₁ h₂ =
      ∑ x : Gn g n, if Ov a b (x : Mt g n) (h₁ : Gn g a) (h₂ : Gn g b) then χ x else 0 := by
    intro a b n χ h₁ h₂
    rw [res, mul_inv_cancel_left₀ (pow_ne_zero _ hg)]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  have hres2 : ∀ (a b n a' b' n' : ℕ) (χ : Gn g n → Gn g n' → ℂ) h₁ h₂ h₁' h₂',
      (g : ℂ) ^ (a * b) * g ^ (a' * b') * res a b (fun z => res a' b' (χ z) h₁' h₂') h₁ h₂ =
      ∑ x : Gn g n, ∑ x' : Gn g n', if Ov a b (x : Mt g n) (h₁ : Gn g a) (h₂ : Gn g b) ∧
        Ov a' b' (x' : Mt g n') (h₁' : Gn g a') (h₂' : Gn g b') then χ x x' else 0 := by
    intro a b n a' b' n' χ h₁ h₂ h₁' h₂'
    rw [mul_comm ((g : ℂ) ^ (a * b)), mul_assoc, hres, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [hres]; simp only [h, true_and]
    · simp [h]
  rw [Fintype.sum_prod_type, mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_assoc ((g : ℂ) ^ (p * q) * g ^ (r * s)), mul_mul_mul_comm, hres2, hres2, Fintype.sum_prod_type,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [ite_zero_mul_ite_zero]
  exact if_congr (by simp only [Good, and_assoc]) rfl rfl

theorem res_one (a b : ℕ) (h₁ : Gn g a) (h₂ : Gn g b) : res a b (fun _ : Gn g (a + b) => (1 : ℂ)) h₁ h₂ = 1 := by
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  rw [res, Finset.sum_boole, (GlobalTheory.GLm.ParBasic.par_basic g a b _ rfl).2.2.2.2.1 h₁ h₂, Nat.cast_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hg)]

set_option synthInstance.maxSize 2000 in
theorem mackey_cell_term_of_block_sizes (a b c d n i q r s : ℕ) (ha : a = i + r) (hb : b = q + s) (hc : c = i + q) (hd : d = r + s)
    (hn : n = c + d) (Λ : Gn g c → Gn g d → ℂ) (Φ : Gn g a → Gn g b → ℂ) :
    ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n) ∧ InPar a (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n)).card : ℂ)⁻¹ * (∑ x : Gn g n, if InPar c (x : Mt g n) ∧ InPar a (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * Φ (toG (tl a (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n))) (toG (br a b (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n))) else 0) = mean (fun y : (Gn g i × Gn g r) × (Gn g q × Gn g s) => res i q (fun z => res r s (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 * res i r (fun x => res q s (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  subst ha hb hc hd
  subst hn
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  simp only [coe_conj (i + r) (i + q) i (i + q + (r + s)) (by omega) (by omega) (by omega)]
  have h1 := (sum_cell (g := g) i q r s (fun _ _ => 1) (fun _ _ => 1)).symm.trans
    (sum_tup (g := g) i q r s (fun _ _ => 1) (fun _ _ => 1))
  simp only [res_one, mul_one, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h1
  rw [h1, ← sum_cell, sum_tup, mean]
  have hk : (Fintype.card (Fin i → Fin s → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

end GlobalTheory.GLm.Cell

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem mackey_cell_term : ∀ (g : ℕ) [Fact g.Prime] (a b c d n i : ℕ), n = a + b → n = c + d → i ≤ a → i ≤ c → c - i ≤ b → ∀ (Λ : Gn g c → Gn g d → ℂ) (Φ : Gn g a → Gn g b → ℂ), ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n) ∧ InPar a (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n)).card : ℂ)⁻¹ * (∑ x : Gn g n, if InPar c (x : Mt g n) ∧ InPar a (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * Φ (toG (tl a (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n))) (toG (br a b (((wI g a c i n)⁻¹ * x * wI g a c i n : Gn g n) : Mt g n))) else 0) = mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) => res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 * res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  intro g _ a b c d n i h₁ h₂ h₃ h₄ h₅ Λ Φ
  exact Cell.mackey_cell_term_of_block_sizes a b c d n i (c - i) (a - i) (b - (c - i)) (by omega) (by omega) (by omega) (by omega) h₂ Λ Φ

end GlobalTheory.GLm
