import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial

namespace PositivityTheory.CW

namespace GradedNormalNilpotent

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

structure Hyp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop where
  mono : ∀ j k, j ≤ k → U E j ≤ U E k
  one : (1 : Module.End ℂ V) ∈ U E 0
  e1 : ∀ a b, E a b ∈ U E 1
  mul : ∀ j k, ∀ x ∈ U E j, ∀ y ∈ U E k, x * y ∈ U E (j + k)
  comm : ∀ j k, ∀ x ∈ U E j, ∀ y ∈ U E k, x * y - y * x ∈ U E (j + k - 1)
  zmem : ∀ a b, Z ε E a b ∈ U E 2

variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)

def Jk : ℕ → Submodule ℂ (Module.End ℂ V)
  | 0 => ⊥
  | 1 => U E 0
  | k + 2 => {
      carrier := {x | ∃ u ∈ U E (k + 1), ∃ w : Fin n → Fin n → Module.End ℂ V,
        (∀ c d, w c d ∈ U E k) ∧ x = u + ∑ c, ∑ d, w c d * Z ε E c d}
      add_mem' := by
        rintro _ _ ⟨u, hu, w, hw, rfl⟩ ⟨u', hu', w', hw', rfl⟩
        refine ⟨u + u', add_mem hu hu', w + w', fun c d => add_mem (hw c d) (hw' c d), ?_⟩
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; abel
      zero_mem' := ⟨0, zero_mem _, 0, fun _ _ => zero_mem _, by simp⟩
      smul_mem' := by
        rintro r _ ⟨u, hu, w, hw, rfl⟩
        refine ⟨r • u, Submodule.smul_mem _ r hu, r • w, fun c d => Submodule.smul_mem _ r (hw c d), ?_⟩
        simp [smul_add, Finset.smul_sum] }

lemma mem_Jk_succ_succ (k : ℕ) (x : Module.End ℂ V) : x ∈ Jk ε E (k + 2) ↔ ∃ u ∈ U E (k + 1),
    ∃ w : Fin n → Fin n → Module.End ℂ V, (∀ c d, w c d ∈ U E k) ∧ x = u + ∑ c, ∑ d, w c d * Z ε E c d :=
  Iff.rfl

lemma U_le_Jk (k : ℕ) : U E k ≤ Jk ε E (k + 1) := by
  rcases k with _ | k
  · exact le_rfl
  · intro x hx
    exact (mem_Jk_succ_succ ε E k x).2 ⟨x, hx, 0, fun _ _ => zero_mem _, by simp⟩

lemma U0 {x : Module.End ℂ V} (hx : x ∈ U E 0) : ∃ c : ℂ, x = c • (1 : Module.End ℂ V) := by
  have : U E 0 ≤ Submodule.span ℂ {(1 : Module.End ℂ V)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact Submodule.subset_span rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (this hx)
  exact ⟨c, hc.symm⟩

variable {ε E}

lemma memJ_left (h : Hyp ε E) (i j : ℕ) {x y : Module.End ℂ V} (hx : x ∈ U E i) (hy : y ∈ Jk ε E j) :
    x * y ∈ Jk ε E (i + j) := by
  rcases j with _ | _ | j
  · have : y = 0 := (Submodule.mem_bot ℂ).mp hy
    simp [this]
  · exact U_le_Jk ε E i (by simpa using h.mul i 0 x hx y hy)
  · obtain ⟨u, hu, w, hw, rfl⟩ := (mem_Jk_succ_succ ε E j y).1 hy
    rw [show i + (j + 2) = (i + j) + 2 by omega, mem_Jk_succ_succ]
    refine ⟨x * u, ?_, fun c d => x * w c d, fun c d => h.mul i j x hx _ (hw c d), ?_⟩
    · have := h.mul i (j + 1) x hx u hu; rwa [← add_assoc] at this
    · simp [mul_add, Finset.mul_sum, mul_assoc]

lemma memJ_right (h : Hyp ε E) (i j : ℕ) {x y : Module.End ℂ V} (hy : y ∈ Jk ε E j) (hx : x ∈ U E i) :
    y * x ∈ Jk ε E (j + i) := by
  rcases j with _ | _ | j
  · have : y = 0 := (Submodule.mem_bot ℂ).mp hy
    simp [this]
  · rw [add_comm]; exact U_le_Jk ε E i (by simpa using h.mul 0 i y hy x hx)
  · obtain ⟨u, hu, w, hw, rfl⟩ := (mem_Jk_succ_succ ε E j y).1 hy
    rw [show j + 2 + i = (j + i) + 2 by omega, mem_Jk_succ_succ]
    refine ⟨u * x + ∑ c, ∑ d, w c d * (Z ε E c d * x - x * Z ε E c d), ?_, fun c d => w c d * x,
      fun c d => h.mul j i _ (hw c d) x hx, ?_⟩
    · refine add_mem ?_ (Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_)
      · have := h.mul (j + 1) i u hu x hx; rwa [show j + 1 + i = j + i + 1 by omega] at this
      · have := h.mul j (2 + i - 1) _ (hw c d) _ (h.comm 2 i _ (h.zmem c d) x hx)
        rwa [show j + (2 + i - 1) = j + i + 1 by omega] at this
    · simp only [add_mul, Finset.sum_mul, mul_sub, mul_assoc, Finset.sum_sub_distrib]; abel

variable (ε E) in

def Rr (h : Hyp ε E) : Subalgebra ℂ (Module.End ℂ V)[X] where
  carrier := {f | ∀ k, f.coeff k ∈ U E k}
  mul_mem' {f g} hf hg k := by
    rw [coeff_mul]
    exact Submodule.sum_mem _ fun x hx => by
      have := h.mul _ _ _ (hf x.1) _ (hg x.2); rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hx] at this
  add_mem' {f g} hf hg k := by rw [coeff_add]; exact add_mem (hf k) (hg k)
  algebraMap_mem' r k := by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with hk
    · subst hk; rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ r h.one
    · exact zero_mem _

variable (ε E) in

def inJ (f : (Module.End ℂ V)[X]) : Prop := ∀ k, f.coeff k ∈ Jk ε E k

lemma inJ_mul_right (h : Hyp ε E) {x g : (Module.End ℂ V)[X]} (hx : inJ ε E x) (hg : g ∈ Rr ε E h) :
    inJ ε E (x * g) := fun k => by
  rw [coeff_mul]
  exact Submodule.sum_mem _ fun p hp => by
    have := memJ_right h _ _ (hx p.1) (hg p.2); rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at this

lemma inJ_mul_left (h : Hyp ε E) {x g : (Module.End ℂ V)[X]} (hx : inJ ε E x) (hg : g ∈ Rr ε E h) :
    inJ ε E (g * x) := fun k => by
  rw [coeff_mul]
  exact Submodule.sum_mem _ fun p hp => by
    have := memJ_left h _ _ (hg p.1) (hx p.2); rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at this

lemma inJ_comm (h : Hyp ε E) {f g : (Module.End ℂ V)[X]} (hf : f ∈ Rr ε E h) (hg : g ∈ Rr ε E h) :
    inJ ε E (f * g - g * f) := fun k => by
  have e : (g * f).coeff k = ∑ x ∈ antidiagonal k, g.coeff x.2 * f.coeff x.1 := by
    rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]; rfl
  rw [coeff_sub, e, coeff_mul, ← Finset.sum_sub_distrib]
  rcases k with _ | k
  · obtain ⟨a, ha⟩ := U0 E (hf 0)
    obtain ⟨b, hb⟩ := U0 E (hg 0)
    simp [ha, hb, smul_smul, mul_comm]
  · refine U_le_Jk ε E k (Submodule.sum_mem _ fun x hx => ?_)
    have := h.comm _ _ _ (hf x.1) _ (hg x.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hx, Nat.add_sub_cancel] at this

variable (ε E) in

def con (h : Hyp ε E) : RingCon (Rr ε E h) where
  r f g := inJ ε E ((f : (Module.End ℂ V)[X]) - g)
  iseqv := ⟨fun f k => by simp,
    fun {f g} hfg k => by rw [← neg_sub, coeff_neg]; exact neg_mem (hfg k),
    fun {f g l} h1 h2 k => by
      have := add_mem (h1 k) (h2 k); rwa [← coeff_add, sub_add_sub_cancel] at this⟩
  add' {a b c d} h1 h2 k := by
    have := add_mem (h1 k) (h2 k)
    simp only [Subalgebra.coe_add, coeff_sub, coeff_add] at *
    convert this using 1; abel
  mul' {a b c d} h1 h2 k := by
    have e : ((a * c : Rr ε E h) : (Module.End ℂ V)[X]) - (b * d : Rr ε E h) =
        ((a : (Module.End ℂ V)[X]) - b) * c + (b : (Module.End ℂ V)[X]) * ((c : (Module.End ℂ V)[X]) - d) := by
      simp only [Subalgebra.coe_mul, sub_mul, mul_sub]; abel
    rw [e, coeff_add]
    exact add_mem (inJ_mul_right h h1 c.2 k) (inJ_mul_left h h2 b.2 k)

variable (ε E) in

abbrev Q (h : Hyp ε E) := (con ε E h).Quotient

instance instCR (h : Hyp ε E) : CommRing (Q ε E h) :=
  { (inferInstance : Ring (Q ε E h)) with
    mul_comm := by
      intro x y
      refine Quotient.inductionOn₂' x y fun f g => ?_
      change ((f : Q ε E h) * g) = g * f
      rw [← RingCon.coe_mul, ← RingCon.coe_mul, RingCon.eq]
      show inJ ε E (((f * g : Rr ε E h) : (Module.End ℂ V)[X]) - (g * f : Rr ε E h))
      simp only [Subalgebra.coe_mul]
      exact inJ_comm h f.2 g.2 }

instance instQA (h : Hyp ε E) : Algebra ℚ (Q ε E h) := Algebra.compHom _ (algebraMap ℚ ℂ)

example (h : Hyp ε E) (A4' : A4) (N : Matrix (Fin n) (Fin n) (Q ε E h)) (hN : ∀ k, (N ^ (k + 1)).trace = 0) :
    N ^ n = 0 := A4' (Q ε E h) n N hN

variable (h : Hyp ε E)

def L (j : ℕ) (x : Module.End ℂ V) (hx : x ∈ U E j) : Rr ε E h :=
  ⟨C x * X ^ j, fun k => by
    rw [coeff_C_mul_X_pow]; split_ifs with hk
    · subst hk; exact hx
    · exact zero_mem _⟩

@[simp] lemma coe_L (j : ℕ) (x : Module.End ℂ V) (hx : x ∈ U E j) :
    ((L h j x hx : Rr ε E h) : (Module.End ℂ V)[X]) = C x * X ^ j := rfl

def MR (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j) :
    Matrix (Fin n) (Fin n) (Rr ε E h) := fun a b => L h j (M a b) (hM a b)

lemma CX_mul (x y : Module.End ℂ V) (i j : ℕ) :
    (C x * X ^ i) * (C y * X ^ j) = C (x * y) * X ^ (i + j) := by
  calc (C x * X ^ i) * (C y * X ^ j) = C x * (X ^ i * C y) * X ^ j := by simp only [mul_assoc]
    _ = C x * (C y * X ^ i) * X ^ j := by rw [(Polynomial.commute_X_pow (C y) i).eq]
    _ = C (x * y) * X ^ (i + j) := by simp only [mul_assoc, C_mul, pow_add]

lemma MR_mul (M M' : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (i j : ℕ) (hM : ∀ a b, M a b ∈ U E i)
    (hM' : ∀ a b, M' a b ∈ U E j) :
    ∃ h'' : ∀ a b, (M * M') a b ∈ U E (i + j), MR h M i hM * MR h M' j hM' = MR h (M * M') (i + j) h'' := by
  refine ⟨fun a b => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun c _ => h.mul _ _ _ (hM a c) _ (hM' c b)
  · refine Matrix.ext fun a b => Subtype.ext ?_
    simp only [Matrix.mul_apply, MR, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, coe_L, CX_mul, map_sum,
      Finset.sum_mul]

lemma MR_pow (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j) (k : ℕ) :
    ∃ hk : ∀ a b, (M ^ (k + 1)) a b ∈ U E (j * (k + 1)), MR h M j hM ^ (k + 1) = MR h (M ^ (k + 1)) (j * (k + 1)) hk := by
  induction k with
  | zero =>
    refine ⟨fun a b => by simpa using hM a b, ?_⟩
    refine Matrix.ext fun a b => Subtype.ext ?_; simp [MR]
  | succ k ih =>
    obtain ⟨hk, e⟩ := ih
    obtain ⟨h'', e'⟩ := MR_mul h _ M _ j hk hM
    refine ⟨fun a b => ?_, ?_⟩
    · have := h'' a b; rwa [← pow_succ, show j * (k + 1) + j = j * (k + 1 + 1) by ring] at this
    · rw [pow_succ, e, e']
      refine Matrix.ext fun a b => Subtype.ext ?_
      simp only [MR, coe_L, ← pow_succ, show j * (k + 1) + j = j * (k + 1 + 1) by ring]

abbrev psi : Rr ε E h →+* Q ε E h := RingCon.mk' (con ε E h)

lemma psiL_iff (j : ℕ) (x : Module.End ℂ V) (hx : x ∈ U E j) : psi h (L h j x hx) = 0 ↔ x ∈ Jk ε E j := by
  rw [← map_zero (psi h)]
  change ((L h j x hx : Rr ε E h) : Q ε E h) = ((0 : Rr ε E h) : Q ε E h) ↔ _
  rw [RingCon.eq]
  change inJ ε E (C x * X ^ j - 0) ↔ _
  simp only [sub_zero, inJ, coeff_C_mul_X_pow]
  constructor
  · intro H; simpa using H j
  · intro H k; split_ifs with hk
    · subst hk; exact H
    · exact zero_mem _

lemma L_sub (j : ℕ) (x y : Module.End ℂ V) (hx : x ∈ U E j) (hy : y ∈ U E j) :
    L h j x hx - L h j y hy = L h j (x - y) (sub_mem hx hy) := by
  apply Subtype.ext; simp [sub_mul]

lemma trace_MR (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j)
    (hT : M.trace ∈ U E j) : ((psi h).mapMatrix (MR h M j hM)).trace = psi h (L h j M.trace hT) := by
  have : L h j M.trace hT = ∑ i, MR h M j hM i i := by
    apply Subtype.ext
    simp [MR, Matrix.trace, Finset.sum_mul]
  rw [this, map_sum]
  rfl

include h in
theorem main (h2 : ∀ (k : ℕ) c d, E c d * (Mm E ^ k).trace = (Mm E ^ k).trace * E c d)
    (h3 : ∀ T : Module.End ℂ V, (∀ a b, E a b * T = T * E a b) → ∃ c : ℂ, ∀ v, T v = c • v)
    (h4 : A4) (h5 : ∀ a b, (Mm E * Md ε E - Md ε E * Mm E) a b + Z ε E a b ∈ U E 1) :
    ∀ m : ℕ, 1 ≤ m → n ≤ m → ∀ a b, ∃ u ∈ U E (2 * m - 1), ∃ w : Fin n → Fin n → Module.End ℂ V,
      (∀ c d, w c d ∈ U E (2 * m - 2)) ∧ ((Md ε E * Mm E) ^ m) a b = u + ∑ c, ∑ d, w c d * Z ε E c d := by
  intro m hm hnm a b
  have hM : ∀ a b, Mm E a b ∈ U E 1 := fun a b => h.e1 a b
  have hD : ∀ a b, Md ε E a b ∈ U E 1 := fun a b => Submodule.smul_mem _ _ (h.e1 a b)
  set N := (psi h).mapMatrix (MR h (Mm E) 1 hM) with hNdef
  set N' := (psi h).mapMatrix (MR h (Md ε E) 1 hD) with hN'def
  have htr : ∀ k, (N ^ (k + 1)).trace = 0 := by
    intro k
    obtain ⟨hk, e⟩ := MR_pow h (Mm E) 1 hM k
    obtain ⟨c, hc⟩ := h3 _ (fun a b => h2 (k + 1) a b)
    have hT : (Mm E ^ (k + 1)).trace = c • 1 := LinearMap.ext fun v => by simp [hc]
    have hT' : (Mm E ^ (k + 1)).trace ∈ U E (1 * (k + 1)) := by
      rw [hT]; exact h.mono 0 _ (Nat.zero_le _) (Submodule.smul_mem _ c h.one)
    rw [hNdef, ← map_pow, e, trace_MR h _ _ _ hT', psiL_iff, hT, one_mul]
    exact U_le_Jk ε E k (h.mono 0 k (Nat.zero_le _) (Submodule.smul_mem _ c h.one))
  have hN : N ^ n = 0 := h4 (Q ε E h) n N htr
  obtain ⟨h1, e1⟩ := MR_mul h (Mm E) (Md ε E) 1 1 hM hD
  obtain ⟨h1', e1'⟩ := MR_mul h (Md ε E) (Mm E) 1 1 hD hM
  have hcomm : Commute N N' := by
    show N * N' = N' * N
    rw [hNdef, hN'def, ← map_mul, ← map_mul, e1, e1']
    refine Matrix.ext fun a b => ?_
    rw [← sub_eq_zero]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MR]
    rw [← map_sub, L_sub, psiL_iff]
    show _ ∈ Jk ε E (0 + 2)
    rw [mem_Jk_succ_succ]
    refine ⟨(Mm E * Md ε E - Md ε E * Mm E) a b + Z ε E a b, h5 a b,
      fun c d => if c = a then (if d = b then -1 else 0) else 0, fun c d => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact neg_mem h.one
      · exact zero_mem _
      · exact zero_mem _
    · simp [ite_mul, Finset.sum_ite_eq', Matrix.sub_apply]
  have hNm : N ^ m = 0 := by rw [← Nat.sub_add_cancel hnm, pow_add, hN, mul_zero]
  have hprod : (N' * N) ^ m = 0 := by rw [hcomm.symm.mul_pow, hNm, mul_zero]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hk, ek⟩ := MR_pow h (Md ε E * Mm E) (1 + 1) h1' k
  have hx : ((Md ε E * Mm E) ^ (k + 1)) a b ∈ Jk ε E ((1 + 1) * (k + 1)) := by
    rw [← psiL_iff h _ _ (hk a b)]
    have := congrFun (congrFun hprod a) b
    rw [hNdef, hN'def, ← map_mul, e1', ← map_pow, ek] at this
    simpa [MR] using this
  rw [show (1 + 1) * (k + 1) = (2 * (k + 1) - 2) + 2 by omega, mem_Jk_succ_succ] at hx
  obtain ⟨u, hu, w, hw, e⟩ := hx
  exact ⟨u, by rwa [show 2 * (k + 1) - 2 + 1 = 2 * (k + 1) - 1 by omega] at hu, w, hw, e⟩

end GradedNormalNilpotent

theorem normal_nilpotent_of_commutator : A1 → A2 → A3 → A4 → CommutatorAdjointModLower → A5 := by
  intro h1 h2 h3 h4 h5 n ε V _ _ E hE
  obtain ⟨hm, ho, he, hmu, hc, -, hz⟩ := h1 n ε V E hE
  exact GradedNormalNilpotent.main ⟨hm, ho, he, hmu, hc, hz⟩ (h2 n ε V E hE) (h3 n ε V E hE) h4 (h5 n ε V E hE)

end PositivityTheory.CW

end
