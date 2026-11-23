import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Subgroup (GL (Fin n) k) where
  carrier := Gz Z
  mul_mem' {a b} ha hb c hc := by
    simp only [Units.val_mul]
    rw [← mul_assoc, ha c hc, mul_assoc, hb c hc, mul_assoc]
  one_mem' c _ := by simp
  inv_mem' {a} ha c hc := by
    have h := ha c hc
    calc c * (a⁻¹ : GL (Fin n) k).val = (a⁻¹ : GL (Fin n) k).val * (a.val * c) * (a⁻¹ : GL (Fin n) k).val := by
          simp [← mul_assoc]
      _ = (a⁻¹ : GL (Fin n) k).val * (c * a.val) * (a⁻¹ : GL (Fin n) k).val := by rw [h]
      _ = (a⁻¹ : GL (Fin n) k).val * c := by simp [mul_assoc]

def SuppU (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (C : Set (Sp k n)) : Prop :=
  ∀ f ∈ supportedIn (UU : Set (Sp k n)), (∀ p ∈ C, f p = 0) → ξ f = 0

def orb (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n) : Set (Sp k n) := {q | ∃ g ∈ Gz Z, act g p = q}

theorem act_mul (g h : GL (Fin n) k) (p : Sp k n) : act (g * h) p = act g (act h p) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Prod.mk.injEq, Matrix.mulVec_mulVec]
  exact ⟨by simp [mul_assoc], trivial⟩

theorem act_one (p : Sp k n) : act (1 : GL (Fin n) k) p = p := by
  simp [act]

def stab (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n) : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ Gz Z ∧ act g p = p}
  mul_mem' {a b} ha hb := ⟨(GzS Z).mul_mem ha.1 hb.1, by rw [act_mul, hb.2, ha.2]⟩
  one_mem' := ⟨(GzS Z).one_mem, act_one p⟩
  inv_mem' {a} ha := ⟨(GzS Z).inv_mem ha.1, by
    conv_lhs => rw [← ha.2]
    rw [← act_mul, inv_mul_cancel, act_one]⟩

def modul (S K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k) : ℝ :=
  ((L.relIndex (K.map (MulAut.conj g).toMonoidHom) : ℝ) / ((L ⊓ S).relIndex (K.map (MulAut.conj g).toMonoidHom ⊓ S) : ℝ)) /
    ((L.relIndex K : ℝ) / ((L ⊓ S).relIndex (K ⊓ S) : ℝ))

def _root_.Subgroup.Normal' (L K : Subgroup (GL (Fin n) k)) : Prop := ∀ a ∈ K, ∀ b ∈ L, a * b * a⁻¹ ∈ L

def ZNClosed : Prop := ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → IsClosed (ZN Z)

def FibZN : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ y, ∃ c ∈ Z, qZ Z c = y ∧
    ∀ x ∈ Bz Z, (qZ Z x = y ∧ x ∈ ZN Z ↔ IsNilpotent (x - c))

def Reps : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ c ∈ Z, ∃ s : Finset (Sp k n),
    (∀ p ∈ s, p.1 ∈ Bz Z ∧ IsNilpotent (p.1 - c) ∧ p.2 ≠ 0 ∧
      ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * (p.1 - c) = (t : k) • ((p.1 - c) * g) ∧ g *ᵥ p.2 = p.2) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) ∧
    ∀ x ∈ Bz Z, IsNilpotent (x - c) → ∀ v : Fin n → k, v ≠ 0 → ∃ p ∈ s, (x, v) ∈ orb Z p

def StepMod : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ (t : kˣ) (p : Sp k n) (g : GL (Fin n) k),
    g ∈ Gz Z → act g p = sig Z t p → p.2 ≠ 0 → ∀ (K : Subgroup (GL (Fin n) k)), K ≤ GzS Z → IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) →
    IsCompact (K : Set (GL (Fin n) k)) → ∀ L : Subgroup (GL (Fin n) k), IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) →
    L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom → L.Normal' K → L.Normal' (K.map (MulAut.conj g).toMonoidHom) →
    ∀ (C U : Set (Sp k n)), IsClosed C → IsOpen U → U ∩ C = orb Z p →
    (∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C) → (∀ q ∈ C, sig Z t q ∈ C) → ∀ ξ, Inv Z ξ → SuppU ξ C →
      SuppU (pull Z t ξ - ((modul (stab Z p) K L g : ℝ) : ℂ) • ξ) (C \ U)

def ModBound : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → 0 < dB0 Z → ∀ c ∈ Z, ∀ (p : Sp k n) (P : GL (Fin n) k)
    (w : Fin n → ℤ), p.1 ∈ Bz Z → IsNilpotent (p.1 - c) → p.2 ≠ 0 →
    (∀ t : kˣ, let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * (p.1 - c) = (t : k) • ((p.1 - c) * g) ∧ g *ᵥ p.2 = p.2) →
    (∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) →
    ∃ a : ℝ, 2 * a < dB0 Z ∧ ∀ t : kˣ, nabs k t < 1 → ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧ L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧
      L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      g.val = P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a

end PositivityTheory.RgUd.T.Nil.Orb
