import Formalism.PeriodIntegrals.FockDegreeTwoParts

noncomputable section

open Matrix FockH1Action

namespace PI.FJM

def JH (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Submodule ℂ (Pol p q r s) :=
  hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (Jset p q r s)

def Exist : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  JointShape p q r s μ μ' → ∃ P ∈ JH p q r s μ μ', P ≠ 0

def ShapeOf : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  ∀ P ∈ JH p q r s μ μ', P ≠ 0 → JointShape p q r s μ μ'

def RankLe : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  JointShape p q r s μ μ' → ∃ v : Pol p q r s, JH p q r s μ μ' ≤ Submodule.span ℂ {v}

private theorem finrank_eq_one_of_ne_zero_mem_of_le_span_singleton {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V}
    {P v : V} (hP : P ∈ S) (hP0 : P ≠ 0) (hv : S ≤ Submodule.span ℂ {v}) : Module.finrank ℂ S = 1 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv hP)
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hP0
    rw [← ha, smul_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hP0
    rw [← ha, zero_smul]
  have heq : S = Submodule.span ℂ {v} := by
    apply le_antisymm hv
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have hva : v = a⁻¹ • P := by
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [hva]
    exact S.smul_mem _ hP
  rw [heq]
  exact finrank_span_singleton hv0

theorem jointMult_of (he : Exist) (hs : ShapeOf) (hr : RankLe) : PI.FockDegreeTwoParts.JointMult := by
  intro p q r s μ μ'
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · change Module.finrank ℂ (JH p q r s μ μ') = 1
    obtain ⟨P, hP, hP0⟩ := he p q r s μ μ' hc
    obtain ⟨v, hv⟩ := hr p q r s μ μ' hc
    exact finrank_eq_one_of_ne_zero_mem_of_le_span_singleton hP hP0 hv
  · change JH p q r s μ μ' = ⊥
    rw [Submodule.eq_bot_iff]
    intro P hP
    by_contra hP0
    exact hc (hs p q r s μ μ' P hP hP0)

def dd {p q r s : ℕ} (l l' : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  (MvPolynomial.pderiv l).toLinearMap * (MvPolynomial.pderiv l').toLinearMap

def lapA {p q r s : ℕ} (i : Fin p) (j : Fin q) : Module.End ℂ (Pol p q r s) :=
  ∑ l : Fin s, dd (Sum.inl i, Sum.inr l) (Sum.inr j, Sum.inr l)

def lapB {p q r s : ℕ} (i : Fin p) (j : Fin q) : Module.End ℂ (Pol p q r s) :=
  ∑ k : Fin r, dd (Sum.inl i, Sum.inl k) (Sum.inr j, Sum.inl k)

def lapC {p q r s : ℕ} (k : Fin r) (l : Fin s) : Module.End ℂ (Pol p q r s) :=
  ∑ i : Fin p, dd (Sum.inl i, Sum.inl k) (Sum.inl i, Sum.inr l)

def lapD {p q r s : ℕ} (k : Fin r) (l : Fin s) : Module.End ℂ (Pol p q r s) :=
  ∑ j : Fin q, dd (Sum.inr j, Sum.inl k) (Sum.inr j, Sum.inr l)

def FormJ : Prop := ∀ (p q r s : ℕ) (P : Pol p q r s),
  P ∈ Jset p q r s ↔ (∀ i j, lapA (r := r) (s := s) i j P = 0) ∧ (∀ i j, lapB (r := r) (s := s) i j P = 0) ∧
    (∀ k l, lapC (p := p) (q := q) k l P = 0) ∧ (∀ k l, lapD (p := p) (q := q) k l P = 0)

def wt1 {p q r s : ℕ} (m : Ln p q r s →₀ ℕ) (a : Ix p q) : ℤ :=
  ∑ c : Ix r s, if linePos (a, c) then (m (a, c) : ℤ) else -(m (a, c) : ℤ)

def wt2 {p q r s : ℕ} (m : Ln p q r s →₀ ℕ) (c : Ix r s) : ℤ :=
  ∑ a : Ix p q, if linePos (a, c) then (m (a, c) : ℤ) else -(m (a, c) : ℤ)

def sh1 (p q r s : ℕ) : Ix p q → ℚ := Sum.elim (fun _ => cPair r s) (fun _ => -cPair r s)

def sh2 (p q r s : ℕ) : Ix r s → ℚ := Sum.elim (fun _ => cPair p q) (fun _ => -cPair p q)

def FormWt1 : Prop := ∀ (p q r s : ℕ) (a : Ix p q) (m : Ln p q r s →₀ ℕ),
  fockAct1 p q r s (Eab a a) (MvPolynomial.monomial m 1) =
    (((wt1 m a : ℚ) + sh1 p q r s a : ℚ) : ℂ) • MvPolynomial.monomial m 1

def FormWt2 : Prop := ∀ (p q r s : ℕ) (c : Ix r s) (m : Ln p q r s →₀ ℕ),
  fockAct2 p q r s (Eab c c) (MvPolynomial.monomial m 1) =
    (((wt2 m c : ℚ) + sh2 p q r s c : ℚ) : ℂ) • MvPolynomial.monomial m 1

def rai1 {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, raiB (a, c) * lowB (b, c)

def rai2 {p q r s : ℕ} (c d : Ix r s) : Module.End ℂ (Pol p q r s) :=
  ∑ a : Ix p q, raiB (a, c) * lowB (a, d)

def FormRaise1 : Prop := ∀ (p q r s : ℕ) (a b : Ix p q), a ≠ b →
  fockAct1 p q r s (Eab a b) = rai1 (r := r) (s := s) a b

def FormRaise2 : Prop := ∀ (p q r s : ℕ) (c d : Ix r s), c ≠ d →
  fockAct2 p q r s (Eab c d) = rai2 (p := p) (q := q) c d

def varMat {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) :
    Matrix (Fin m) (Fin k) (Pol p q r s) :=
  Matrix.of fun i j => MvPolynomial.X (ρ i, κ j)

def leadT {R : Type*} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin k) R) (t : ℕ) : R :=
  if h : t ≤ m ∧ t ≤ k then (M.submatrix (Fin.castLE h.1) (Fin.castLE h.2)).det else 0

def shapeProd {R : Type*} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin k) R) (α : List ℕ) : R :=
  ∏ t ∈ Finset.range α.length, leadT M (t + 1) ^ (α.getD t 0 - α.getD (t + 1) 0)

def ShapeData (p q r s : ℕ) (a b c d : List ℤ) : Prop :=
  (∀ v ∈ a, 0 < v) ∧ (∀ v ∈ c, 0 < v) ∧ (∀ v ∈ b, v < 0) ∧ (∀ v ∈ d, v < 0) ∧
    a.Pairwise (· ≥ ·) ∧ b.Pairwise (· ≥ ·) ∧ c.Pairwise (· ≥ ·) ∧ d.Pairwise (· ≥ ·) ∧
    a.length + b.length ≤ p ∧ c.length + d.length ≤ q ∧
    a.length + d.length ≤ r ∧ c.length + b.length ≤ s

def posPart (a : List ℤ) : List ℕ := a.map Int.toNat

def negPart (b : List ℤ) : List ℕ := (b.map fun v => (-v).toNat).reverse

def hwVec (p q r s : ℕ) (a b c d : List ℤ) : Pol p q r s :=
  shapeProd (varMat (fun i : Fin p => (Sum.inl i : Ix p q)) (fun k : Fin r => (Sum.inl k : Ix r s))) (posPart a) *
  shapeProd (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
    (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) (negPart b) *
  shapeProd (varMat (fun j : Fin q => (Sum.inr j : Ix p q)) (fun l : Fin s => (Sum.inr l : Ix r s))) (posPart c) *
  shapeProd (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
    (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) (negPart d)

def wtOf1 (p q r s : ℕ) (a b c d : List ℤ) : Ix p q → ℚ := fun i =>
  ofBlocks (pad a (p - a.length - b.length) b) (pad c (q - c.length - d.length) d) i + sh1 p q r s i

def wtOf2 (p q r s : ℕ) (a b c d : List ℤ) : Ix r s → ℚ := fun i =>
  ofBlocks (pad a (r - a.length - d.length) d) (pad c (s - c.length - b.length) b) i + sh2 p q r s i

def VecNe : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d → hwVec p q r s a b c d ≠ 0

def VecJ : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d →
  hwVec p q r s a b c d ∈ Jset p q r s

def VecHW1 : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d →
  hwVec p q r s a b c d ∈ hwSub (fockAct1 p q r s) (wtOf1 p q r s a b c d)

def VecHW2 : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d →
  hwVec p q r s a b c d ∈ hwSub (fockAct2 p q r s) (wtOf2 p q r s a b c d)

theorem exist_of (hN : VecNe) (hJ : VecJ) (h1 : VecHW1) (h2 : VecHW2) : Exist := by
  intro p q r s μ μ' hcorr
  obtain ⟨a, b, c, d, ha, hc, hb, hd, hpa, hpb, hpc, hpd, hl1, hl2, hl3, hl4, hμ, hμ'⟩ := hcorr
  have hS : ShapeData p q r s a b c d := ⟨ha, hc, hb, hd, hpa, hpb, hpc, hpd, hl1, hl2, hl3, hl4⟩
  have hL : wtOf1 p q r s a b c d = μ := by
    funext x
    have h := congrFun hμ x
    cases x <;> simp only [wtOf1, sh1, FockH1Action.shiftNu, Sum.elim_inl, Sum.elim_inr] at h ⊢ <;> linarith
  have hR : wtOf2 p q r s a b c d = μ' := by
    funext x
    have h := congrFun hμ' x
    cases x <;> simp only [wtOf2, sh2, FockH1Action.shiftNu, Sum.elim_inl, Sum.elim_inr] at h ⊢ <;> linarith
  have hA := h1 p q r s a b c d hS
  have hB := h2 p q r s a b c d hS
  rw [hL] at hA
  rw [hR] at hB
  refine ⟨hwVec p q r s a b c d, ?_, hN p q r s a b c d hS⟩
  unfold JH
  exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hA, hB⟩, Submodule.subset_span (hJ p q r s a b c d hS)⟩

end PI.FJM
