import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.Tr

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem isInt_mul {r s t : Type} [Fintype s] {M : Matrix r s (w.adicCompletion E)}
    {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun k _ => (Ov E w).mul_mem (hM i k) (hN k j)

theorem isInt_of_GLint {n : ℕ} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLint (Fin n) (Ov E w)) :
    IsInt w g.val := by
  obtain ⟨f, rfl⟩ := hg
  intro i j
  exact (f.val i j).2

theorem isInt_sandwich {r s : ℕ} {u : GL (Fin r) (w.adicCompletion E)} {v : GL (Fin s) (w.adicCompletion E)}
    (hu : u ∈ GLint (Fin r) (Ov E w)) (hv : v ∈ GLint (Fin s) (Ov E w))
    (M : Matrix (Fin r) (Fin s) (w.adicCompletion E)) : IsInt w (u.val * M * v.val) ↔ IsInt w M := by
  constructor
  · intro h
    have key := isInt_mul (isInt_mul (isInt_of_GLint (inv_mem hu)) h) (isInt_of_GLint (inv_mem hv))
    have h1 : (u⁻¹).val * u.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : v.val * (v⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : (u⁻¹).val * (u.val * M * v.val) * (v⁻¹).val = M := by
      calc (u⁻¹).val * (u.val * M * v.val) * (v⁻¹).val
          = ((u⁻¹).val * u.val) * M * (v.val * (v⁻¹).val) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at key
  · intro h
    exact isInt_mul (isInt_mul (isInt_of_GLint hu) h) (isInt_of_GLint hv)

def phi {a b : ℕ} {L : Type} [Field L] (p : GL (Fin a) L) (q : GL (Fin b) L) :
    Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := p.val * X * (q⁻¹).val
  invFun Y := (p⁻¹).val * Y * q.val
  left_inv X := by
    have h1 : (p⁻¹).val * p.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (q⁻¹).val * q.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (p⁻¹).val * (p.val * X * (q⁻¹).val) * q.val
        = ((p⁻¹).val * p.val) * X * ((q⁻¹).val * q.val) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv Y := by
    have h1 : p.val * (p⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : q.val * (q⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc p.val * ((p⁻¹).val * Y * q.val) * (q⁻¹).val
        = (p.val * (p⁻¹).val) * Y * (q.val * (q⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

theorem relIndex_of_equiv {A B : Type} [AddGroup A] [AddGroup B] (φ : A ≃+ B) (H K : AddSubgroup A)
    (H' K' : AddSubgroup B) (hH : ∀ X, X ∈ H ↔ φ X ∈ H') (hK : ∀ X, X ∈ K ↔ φ X ∈ K') :
    H.relIndex K = H'.relIndex K' := by
  have key : ∀ (P : AddSubgroup A) (P' : AddSubgroup B), (∀ X, X ∈ P ↔ φ X ∈ P') →
      P.map φ.toAddMonoidHom = P' := by
    intro P P' h
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (h X).1 hX
    · intro hY
      exact ⟨φ.symm Y, (h _).2 (by simpa using hY), by simp⟩
  rw [← key H H' hH, ← key K K' hK]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective).symm

theorem mem_latD {ϖ : w.adicCompletion E} {a b i j : ℕ} {W : Matrix (Fin a) (Fin b) (w.adicCompletion E)} :
    W ∈ latD ϖ a b i j ↔
      ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w := Iff.rfl

theorem unif_mem {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ∈ Ov E w := by
  have : Valued.v ϖ ≤ 1 := by
    rw [h]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this

theorem unif_ne {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h0
  rw [IsUnifV, h0, map_zero] at h
  exact WithZero.zero_ne_coe h

theorem diag_iff_latD {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {a b : ℕ} (i j : ℕ)
    (W : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (IsInt w (diagJ a ϖ i * W) ∧ IsInt w (ϖ • (W * diagJ b ϖ⁻¹ j))) ↔ W ∈ latD ϖ a b i j := by
  have hm := unif_mem hϖ
  have h0 := unif_ne hϖ
  have hc : ∀ x : w.adicCompletion E, ϖ * (x * ϖ⁻¹) = x := fun x => by field_simp
  rw [mem_latD]
  constructor
  · rintro ⟨h1, h2⟩ r s
    have a1 := h1 r s
    have a2 := h2 r s
    simp only [diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at a1 a2
    by_cases hr : (r : ℕ) < i <;> by_cases hs : (s : ℕ) < j
    · rw [if_neg (by omega)]
      rw [if_pos hs, hc] at a2
      exact a2
    · rw [if_pos ⟨hr, by omega⟩]
      rw [if_pos hr] at a1
      exact a1
    · rw [if_neg (by omega)]
      rw [if_neg hr, one_mul] at a1
      exact a1
    · rw [if_neg (by omega)]
      rw [if_neg hr, one_mul] at a1
      exact a1
  · intro h
    refine ⟨fun r s => ?_, fun r s => ?_⟩
    · have a := h r s
      simp only [diagJ, Matrix.diagonal_mul]
      by_cases hr : (r : ℕ) < i
      · rw [if_pos hr]
        by_cases hs : j ≤ (s : ℕ)
        · rwa [if_pos ⟨hr, hs⟩] at a
        · rw [if_neg (by omega)] at a
          exact (Ov E w).mul_mem hm a
      · rw [if_neg hr, one_mul]
        rwa [if_neg (by omega)] at a
    · have a := h r s
      simp only [diagJ, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
      by_cases hs : (s : ℕ) < j
      · rw [if_pos hs, hc]
        rwa [if_neg (by omega)] at a
      · rw [if_neg hs, mul_one]
        by_cases hr : (r : ℕ) < i
        · rwa [if_pos ⟨hr, by omega⟩] at a
        · rw [if_neg (by omega)] at a
          exact (Ov E w).mul_mem hm a

theorem diagJ_mul_inv {L : Type} [Field L] {ϖ : L} (h0 : ϖ ≠ 0) (n j : ℕ) :
    diagJ n ϖ j * diagJ n ϖ⁻¹ j = 1 := by
  rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext r
  split_ifs <;> simp [h0]

theorem mem_latM_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {a b i j : ℕ}
    {m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)}
    {k₁ p : GL (Fin a) (w.adicCompletion E)} {k₂ q : GL (Fin b) (w.adicCompletion E)}
    (hk₁ : k₁ ∈ GLint (Fin a) (Ov E w)) (hp : p ∈ GLint (Fin a) (Ov E w))
    (hk₂ : k₂ ∈ GLint (Fin b) (Ov E w)) (hq : q ∈ GLint (Fin b) (Ov E w))
    (e₁ : m.1.val = k₁.val * diagJ a ϖ i * p.val) (e₂ : m.2.val = k₂.val * diagJ b ϖ j * q.val)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    X ∈ latM ϖ m ↔ phi p q X ∈ latD ϖ a b i j := by
  set W := phi p q X with hW
  have hX : X = (p⁻¹).val * W * q.val := ((phi p q).symm_apply_apply X).symm
  have hpp : p.val * (p⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqq : q.val * (q⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hkk : k₂.val * (k₂⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD := diagJ_mul_inv (unif_ne hϖ) b j
  have f₁ : m.1.val * X = k₁.val * (diagJ a ϖ i * W) * q.val := by
    calc m.1.val * X = k₁.val * diagJ a ϖ i * (p.val * (p⁻¹).val) * W * q.val := by
          rw [e₁, hX]; simp only [Matrix.mul_assoc]
      _ = k₁.val * (diagJ a ϖ i * W) * q.val := by
          rw [hpp, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hx : m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val) = 1 := by
    calc m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val)
        = k₂.val * diagJ b ϖ j * (q.val * (q⁻¹).val) * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
          rw [e₂]; simp only [Matrix.mul_assoc]
      _ = k₂.val * (diagJ b ϖ j * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
          rw [hqq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD, Matrix.mul_one, hkk]
  have hinv : (m.2⁻¹).val = (q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
    calc (m.2⁻¹).val = (m.2⁻¹).val * (m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val)) := by
          rw [hx, Matrix.mul_one]
      _ = ((m.2⁻¹).val * m.2.val) * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val) := by
          simp only [Matrix.mul_assoc]
      _ = (q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have f₂ : ϖ • (X * (m.2⁻¹).val) = (p⁻¹).val * (ϖ • (W * diagJ b ϖ⁻¹ j)) * (k₂⁻¹).val := by
    have : X * (m.2⁻¹).val = (p⁻¹).val * (W * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
      calc X * (m.2⁻¹).val
          = (p⁻¹).val * W * (q.val * (q⁻¹).val) * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
            rw [hinv, hX]; simp only [Matrix.mul_assoc]
        _ = (p⁻¹).val * (W * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
            rw [hqq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have s₁ := isInt_sandwich hk₁ hq (diagJ a ϖ i * W)
  have s₂ := isInt_sandwich (inv_mem hp) (inv_mem hk₂) (ϖ • (W * diagJ b ϖ⁻¹ j))
  rw [← diag_iff_latD hϖ i j W, ← s₁, ← s₂, ← f₁, ← f₂]
  exact Iff.rfl

theorem latM_relIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → ∀ m : GLw a w × GLw b w, Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 → Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 → (intSub a b w).relIndex (latM ϖ m) = (intSub a b w).relIndex (latD ϖ a b i j) := by
  intro E _ _ _ a b w ϖ hϖ i j _ _ m h₁ h₂
  obtain ⟨k₁, hk₁, p, hp, e₁⟩ := Set.mem_of_indicator_ne_zero h₁
  obtain ⟨k₂, hk₂, q, hq, e₂⟩ := Set.mem_of_indicator_ne_zero h₂
  refine relIndex_of_equiv (phi p q) _ _ _ _ (fun X => ?_) (mem_latM_iff hϖ hk₁ hp hk₂ hq e₁ e₂)
  constructor
  · intro h
    exact (isInt_sandwich hp (inv_mem hq) X).2 h
  · intro h
    exact (isInt_sandwich hp (inv_mem hq) X).1 h

end GlobalTheory.CompanionTheory.CtS.Tr
