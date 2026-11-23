import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.HermDiag

variable {R : Type} [CommRing R]

def ct (σ : R →+* R) {a b : Type} (x : Matrix a b R) : Matrix b a R := (x.map σ).transpose

theorem ct_apply (σ : R →+* R) {a b : Type} (x : Matrix a b R) (i : b) (j : a) :
    ct σ x i j = σ (x j i) := rfl

theorem ct_mul (σ : R →+* R) {a b c : Type} [Fintype b] (x : Matrix a b R) (y : Matrix b c R) :
    ct σ (x * y) = ct σ y * ct σ x := by
  unfold ct
  rw [Matrix.map_mul, Matrix.transpose_mul]

def Hm (σ : R →+* R) {ι : Type} (h : Matrix ι ι R) : Prop := ∀ i j, σ (h i j) = h j i

def Diagble (σ : R →+* R) {ι : Type} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι R) : Prop :=
  ∃ (g g' : Matrix ι ι R) (d : ι → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧
    ct σ g * h * g = Matrix.diagonal d

section basic
variable {σ : R →+* R} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem hm_congr (hinv : ∀ a, σ (σ a) = a) {h : Matrix ι ι R} (hh : Hm σ h) (p : Matrix ι ι R) :
    Hm σ (ct σ p * h * p) := by
  have hc : ct σ (ct σ p * h * p) = ct σ p * h * p := by
    have h1 : ct σ h = h := by ext i j; exact hh j i
    have h2 : ct σ (ct σ p) = p := by ext i j; exact hinv _
    rw [ct_mul, ct_mul, h1, h2, Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun hc j) i

theorem diagble_zero : Diagble σ (0 : Matrix ι ι R) :=
  ⟨1, 1, 0, by simp, by simp, by simp, by simp⟩

theorem diagble_of_congr {h p p' : Matrix ι ι R} (h1 : p * p' = 1) (h2 : p' * p = 1)
    (hd : Diagble σ (ct σ p * h * p)) : Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨p * g, g' * p', d, ?_, ?_, hfix, ?_⟩
  · calc p * g * (g' * p') = p * (g * g') * p' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Matrix.mul_one, h1]
  · calc g' * p' * (p * g) = g' * (p' * p) * g := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hg']
  · rw [ct_mul, ← hdiag]
    simp only [Matrix.mul_assoc]

theorem diagble_smul {h : Matrix ι ι R} {c : R} (hc : σ c = c) (hd : Diagble σ h) :
    Diagble σ (c • h) := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨g, g', fun i => c * d i, hg, hg', fun i => by simp [hc, hfix], ?_⟩
  have : Matrix.diagonal (fun i => c * d i) = c • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  rw [this, ← hdiag]
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem diagble_reindex (e : κ ≃ ι) {h : Matrix ι ι R} (hd : Diagble σ (h.submatrix e e)) :
    Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨g.submatrix e.symm e.symm, g'.submatrix e.symm e.symm, fun i => d (e.symm i),
    ?_, ?_, fun i => hfix _, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hg]; simp
  · rw [Matrix.submatrix_mul_equiv, hg']; simp
  · have hct : ct σ (g.submatrix e.symm e.symm) = (ct σ g).submatrix e.symm e.symm := rfl
    have hh : h = (h.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
    rw [hct, hh, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hdiag]
    ext i j
    simp [Matrix.diagonal_apply]

theorem diagble_block {a : R} (ha : σ a = a) {D : Matrix ι ι R} (hd : Diagble σ D) :
    Diagble σ (Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 D) := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨Matrix.fromBlocks 1 0 0 g, Matrix.fromBlocks 1 0 0 g', Sum.elim (fun _ => a) d,
    ?_, ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]; simp [hg]
  · rw [Matrix.fromBlocks_multiply]; simp [hg']
  · rintro (i | i)
    · simpa using ha
    · simpa using hfix i
  · have hct : ct σ (Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 g) =
        Matrix.fromBlocks 1 0 0 (ct σ g) := by
      ext (i | i) (j | j) <;> simp [ct_apply, Matrix.one_apply]
    rw [hct, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_diagonal]
    simp [hdiag]

theorem diagble_schur (hinv : ∀ a, σ (σ a) = a) (ih : ∀ h : Matrix ι ι R, Hm σ h → Diagble σ h)
    {h : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R} (hh : Hm σ h)
    (hu : IsUnit (h (Sum.inl ()) (Sum.inl ()))) : Diagble σ h := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  set a := h (Sum.inl ()) (Sum.inl ()) with ha
  have hfa : σ a = a := hh _ _
  have hfv : σ v = v := by
    have h1 : a * σ v = 1 := by
      have := congrArg σ hv
      rwa [map_mul, map_one, hfa] at this
    calc σ v = (a * v) * σ v := by rw [hv, one_mul]
      _ = (a * σ v) * v := by ring
      _ = v := by rw [h1, one_mul]
  let B : Matrix Unit ι R := h.toBlocks₁₂
  let C : Matrix ι Unit R := h.toBlocks₂₁
  let D : Matrix ι ι R := h.toBlocks₂₂
  have hA : h.toBlocks₁₁ = Matrix.diagonal fun _ : Unit => a := by
    ext i j
    cases i; cases j
    simp [Matrix.toBlocks₁₁, ha]
  have hblocks : h = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) B C D := by
    rw [← hA]; exact (Matrix.fromBlocks_toBlocks h).symm
  have hCB : ∀ i, σ (B () i) = C i () := fun i => hh _ _
  have hCB' : ∀ i, σ (C i ()) = B () i := fun i => hh _ _
  have hD : ∀ i j, σ (D i j) = D j i := fun i j => hh _ _
  let p : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := Matrix.fromBlocks 1 (-(v • B)) 0 1
  let p' : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R := Matrix.fromBlocks 1 (v • B) 0 1
  have hpp : p * p' = 1 := by
    simp only [p, p']
    rw [Matrix.fromBlocks_multiply]; simp
  have hpp' : p' * p = 1 := by
    simp only [p, p']
    rw [Matrix.fromBlocks_multiply]; simp
  let E : Matrix ι ι R := D - v • (C * B)
  have hE : Hm σ E := by
    intro i j
    simp only [E, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.univ_unique,
      Finset.sum_singleton, smul_eq_mul, map_sub, map_mul, hfv, hD, hCB, hCB']
    simp only [PUnit.default_eq_unit]
    ring
  have hct : ct σ p = Matrix.fromBlocks 1 0 (-(v • C)) 1 := by
    ext (i | i) (j | j)
    · simp [p, ct_apply, Matrix.one_apply]
    · simp [p, ct_apply]
    · cases j; simp [p, ct_apply, hfv, hCB]
    · by_cases hij : i = j
      · subst hij; simp [p, ct_apply]
      · simp [p, ct_apply, Matrix.one_apply, hij, Ne.symm hij]
  have hcongr : ct σ p * h * p = Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 E := by
    have hav : ∀ {c : Type} (X : Matrix Unit c R), (Matrix.diagonal fun _ : Unit => a) * (v • X) = X := by
      intro c X
      ext i j
      cases i
      rw [Matrix.diagonal_mul]
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (X () j) * hv
    have hva : ∀ {c : Type} (X : Matrix c Unit R), (v • X) * (Matrix.diagonal fun _ : Unit => a) = X := by
      intro c X
      ext i j
      cases j
      rw [Matrix.mul_diagonal]
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (X i ()) * hv
    rw [hct, hblocks]
    simp only [p]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hva, hav, E, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, sub_eq_add_neg, add_comm]
  apply diagble_of_congr hpp hpp'
  rw [hcongr]
  exact diagble_block hfa (ih E hE)

end basic

section local_ring
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}

theorem exists_trace (hR : IsUnrQuad R σ ϖ q ε) {y : R} (hy : y ∉ lev ϖ 1) :
    ∃ s, s * y + σ (s * y) ∉ lev ϖ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hR.basis
  apply hy
  have h3 : (u - σ u) * y ∈ lev ϖ 1 := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ (hcon u) (Ideal.mul_mem_left _ _ (hcon 1))
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ct_one : ct σ (1 : Matrix ι ι R) = 1 := by
  unfold ct
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem ct_transvection (i j : ι) (s : R) :
    ct σ (Matrix.transvection j i s) = Matrix.transvection i j (σ s) := by
  unfold ct Matrix.transvection
  ext a b
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h1 : j = a ∧ i = a
    · obtain ⟨rfl, rfl⟩ := h1; simp
    · have h2 : ¬ (i = a ∧ j = a) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2]
  · have hba : ¬ b = a := fun h => hab h.symm
    by_cases h1 : j = b ∧ i = a
    · have h2 : i = a ∧ j = b := ⟨h1.2, h1.1⟩
      simp [hab, hba, h1, h2]
    · have h2 : ¬ (i = a ∧ j = b) := fun h => h1 ⟨h.2, h.1⟩
      simp [hab, hba, h1, h2]

theorem pivot_offdiag (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) {i j : ι}
    (hij : i ≠ j) (hi : h i i ∈ lev ϖ 1) (hj : h j j ∈ lev ϖ 1) (hy : h i j ∉ lev ϖ 1) :
    ∃ p p' : Matrix ι ι R, p * p' = 1 ∧ p' * p = 1 ∧ (ct σ p * h * p) i i ∉ lev ϖ 1 := by
  obtain ⟨s, hs⟩ := exists_trace hR hy
  refine ⟨Matrix.transvection j i s, Matrix.transvection j i (-s), ?_, ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same _ _ hij.symm]; simp
  · rw [Matrix.transvection_mul_transvection_same _ _ hij.symm]; simp
  · rw [ct_transvection, Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_same]
    intro hmem
    apply hs
    have : s * h i j + σ (s * h i j) =
        (h i i + σ s * h j i + s * (h i j + σ s * h j j)) - h i i - s * σ s * h j j := by
      rw [map_mul, hh i j]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hmem hi) (Ideal.mul_mem_left _ _ hj)

theorem exists_pivot (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) {i j : ι}
    (hy : h i j ∉ lev ϖ 1) :
    ∃ (k : ι) (p p' : Matrix ι ι R), p * p' = 1 ∧ p' * p = 1 ∧
      (ct σ p * h * p) k k ∉ lev ϖ 1 := by
  by_cases h1 : ∃ k, h k k ∉ lev ϖ 1
  · obtain ⟨k, hk⟩ := h1
    exact ⟨k, 1, 1, by simp, by simp, by simpa [ct_one] using hk⟩
  · push_neg at h1
    have hij : i ≠ j := by
      rintro rfl
      exact hy (h1 i)
    obtain ⟨p, p', a, b, c⟩ := pivot_offdiag hR hh hij (h1 i) (h1 j) hy
    exact ⟨i, p, p', a, b, c⟩

theorem exists_prim (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) (h0 : h ≠ 0) :
    ∃ (a : ℕ) (h' : Matrix ι ι R), Hm σ h' ∧ h = (ϖ ^ a) • h' ∧ ∃ i j, h' i j ∉ lev ϖ 1 := by
  classical
  have hex : ∃ k, ∃ i j, h i j ∉ lev ϖ k := by
    by_contra hcon
    push_neg at hcon
    apply h0
    ext i j
    exact hR.sep _ (fun k => hcon k i j)
  have hk0 : Nat.find hex ≠ 0 := by
    intro h00
    obtain ⟨i, j, hij⟩ := Nat.find_spec hex
    rw [h00] at hij
    exact hij (by simp [lev])
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨i, j, hij⟩ := Nat.find_spec hex
  rw [ha] at hij
  have hall : ∀ i j, h i j ∈ lev ϖ a := by
    have := Nat.find_min hex (m := a) (by omega)
    push_neg at this
    exact this
  choose c hc using fun i j => mem_lev_iff.1 (hall i j)
  refine ⟨a, Matrix.of c, ?_, ?_, i, j, ?_⟩
  · intro x y
    apply hR.reg.pow a
    have := hh x y
    rw [hc x y, hc y x, map_mul, map_pow, hR.fix_ϖ] at this
    simpa using this
  · ext x y
    exact hc x y
  · intro hm
    obtain ⟨d, hd⟩ := mem_lev_iff.1 hm
    apply hij
    refine mem_lev_iff.2 ⟨d, ?_⟩
    have hd' : c i j = ϖ ^ 1 * d := hd
    rw [hc i j, hd', Nat.succ_eq_add_one]
    ring

theorem diagble_prim (hR : IsUnrQuad R σ ϖ q ε) {n : ℕ}
    (ih : ∀ h : Matrix (Fin n) (Fin n) R, Hm σ h → Diagble σ h)
    {h : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hh : Hm σ h) {i j : Fin (n + 1)}
    (hy : h i j ∉ lev ϖ 1) : Diagble σ h := by
  obtain ⟨k, p, p', h1, h2, hp⟩ := exists_pivot hR hh hy
  apply diagble_of_congr h1 h2
  have hh2 := hm_congr hR.inv hh p
  have hcard : Fintype.card (Unit ⊕ Fin n) = n + 1 := by simp; omega
  let e0 := Fintype.equivFinOfCardEq hcard
  let e := e0.trans (Equiv.swap (e0 (Sum.inl ())) k)
  have he : e (Sum.inl ()) = k := by simp [e]
  apply diagble_reindex e
  refine diagble_schur hR.inv ih (fun a b => hh2 _ _) ?_
  simp only [Matrix.submatrix_apply, he]
  exact hR.fixLocal _ (hh2 _ _) hp

theorem diagble_fin (hR : IsUnrQuad R σ ϖ q ε) :
    ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), Hm σ h → Diagble σ h := by
  intro n
  induction n with
  | zero =>
    intro h _
    rw [Subsingleton.elim h 0]
    exact diagble_zero
  | succ n ih =>
    intro h hh
    by_cases h0 : h = 0
    · rw [h0]; exact diagble_zero
    · obtain ⟨a, h', hh', rfl, i, j, hy⟩ := exists_prim hR hh h0
      exact diagble_smul (by simp [hR.fix_ϖ]) (diagble_prim hR ih hh' hy)

end local_ring

theorem herm_diag : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), cT σ h = h →
    ∃ (g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧
      (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = Matrix.diagonal d := by
  intro R _ σ ϖ q ε hR n h hh
  obtain ⟨g, g', d, h1, h2, h3, h4⟩ :=
    diagble_fin hR n h (fun i j => congrFun (congrFun hh j) i)
  exact ⟨g, g', d, h1, h2, h3, h4⟩

end GlobalTheory.CompanionTheory.HermDiag
end
