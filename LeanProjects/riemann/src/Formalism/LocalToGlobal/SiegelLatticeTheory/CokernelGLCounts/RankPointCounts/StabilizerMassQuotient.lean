import Mathlib

noncomputable section

open scoped ENNReal Classical

namespace Formalism.L2.SG.Pf.StabilizerMassQuotient

variable (Γ : Type*) [Group Γ]

def mass (A : Type*) [MulAction Γ A] : ℝ≥0∞ :=
  ∑' o : Quotient (MulAction.orbitRel Γ A), ((Nat.card (MulAction.stabilizer Γ o.out) : ℝ≥0∞))⁻¹

variable {Γ}

theorem card_stab_smul {A : Type*} [MulAction Γ A] (g : Γ) (a : A) :
    Nat.card (MulAction.stabilizer Γ (g • a)) = Nat.card (MulAction.stabilizer Γ a) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨g⁻¹ * (s : Γ) * g, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 s.2,
          inv_smul_smul]⟩
      invFun := fun t => ⟨g * (t : Γ) * g⁻¹, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
          MulAction.mem_stabilizer_iff.1 t.2]⟩
      left_inv := fun s => Subtype.ext (by first | simp [mul_assoc] | group)
      right_inv := fun t => Subtype.ext (by first | simp [mul_assoc] | group) }

theorem card_stab_of_orbitRel {A : Type*} [MulAction Γ A] {a a' : A} (h : MulAction.orbitRel Γ A a' a) :
    Nat.card (MulAction.stabilizer Γ a') = Nat.card (MulAction.stabilizer Γ a) := by
  first
  | (obtain ⟨g, rfl⟩ := h; exact card_stab_smul g a)
  | (obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h);
      exact card_stab_smul g a)

section Fibre

variable {A B : Type*} [MulAction Γ A] [MulAction Γ B] (f : A → B)
  (hf : ∀ (g : Γ) (a : A), f (g • a) = g • f a)

include hf in

@[reducible] def fibAct (b : B) : MulAction (MulAction.stabilizer Γ b) {a : A // f a = b} where
  smul s a := ⟨(s : Γ) • a.1, by rw [hf, a.2]; exact s.2⟩
  one_smul a := Subtype.ext (one_smul Γ a.1)
  mul_smul s t a := Subtype.ext (mul_smul (s : Γ) (t : Γ) a.1)

include hf in

def qmap : Quotient (MulAction.orbitRel Γ A) → Quotient (MulAction.orbitRel Γ B) :=
  Quotient.map' f fun a a' ⟨g, hg⟩ => ⟨g, by
    have hg' : g • a' = a := hg
    show g • f a' = f a
    rw [← hf, hg']⟩

theorem qmap_mk (a : A) : qmap f hf (Quotient.mk _ a) = Quotient.mk (MulAction.orbitRel Γ B) (f a) := rfl

include hf in

def stabEquiv (b : B) (x : {a : A // f a = b}) :
    (letI := fibAct f hf b; MulAction.stabilizer (MulAction.stabilizer Γ b) x) ≃ MulAction.stabilizer Γ x.1 := by
  letI := fibAct f hf b
  exact
    { toFun := fun s => ⟨(s.1 : Γ), by
        have h := s.2
        rw [MulAction.mem_stabilizer_iff] at h ⊢
        exact congrArg Subtype.val h⟩
      invFun := fun g => ⟨⟨g.1, by
        rw [MulAction.mem_stabilizer_iff]
        have h := MulAction.mem_stabilizer_iff.1 g.2
        have h2 := congrArg f h
        rw [hf, x.2] at h2
        exact h2⟩, by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          exact (MulAction.mem_stabilizer_iff.1 g.2)⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }

include hf in

def orbEquiv (oB : Quotient (MulAction.orbitRel Γ B)) :
    (letI := fibAct f hf oB.out; Quotient (MulAction.orbitRel (MulAction.stabilizer Γ oB.out) {a : A // f a = oB.out})) ≃
      ↥(qmap f hf ⁻¹' {oB}) := by
  letI := fibAct f hf oB.out
  refine Equiv.ofBijective (Quotient.lift (fun x => ⟨Quotient.mk _ x.1, ?_⟩) ?_) ⟨?_, ?_⟩
  · show Quotient.mk _ (f x.1) = oB
    rw [x.2]; exact Quotient.out_eq oB
  · rintro x y ⟨s, hs⟩
    apply Subtype.ext
    exact Quotient.sound ⟨(s : Γ), congrArg Subtype.val hs⟩
  · intro X Y hXY
    induction X using Quotient.inductionOn with | h x => ?_
    induction Y using Quotient.inductionOn with | h y => ?_
    have h := congrArg Subtype.val hXY
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg' : g • y.1 = x.1 := hg
    have hgb : g • oB.out = oB.out := by
      have h2 := congrArg f hg'
      rw [hf, y.2, x.2] at h2
      exact h2
    exact Quotient.sound ⟨⟨g, hgb⟩, Subtype.ext hg'⟩
  · rintro ⟨oA, hoA⟩
    have hoA' : qmap f hf oA = oB := hoA
    have h1 : Quotient.mk (MulAction.orbitRel Γ B) (f oA.out) = Quotient.mk _ oB.out := by
      rw [← qmap_mk f hf, Quotient.out_eq, hoA', Quotient.out_eq]
    obtain ⟨g, hg⟩ := Quotient.exact h1
    have hg' : g • oB.out = f oA.out := hg
    refine ⟨Quotient.mk _ ⟨g⁻¹ • oA.out, by rw [hf, ← hg', inv_smul_smul]⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (g⁻¹ • oA.out) = oA
    exact (Quotient.sound ⟨g⁻¹, rfl⟩ : Quotient.mk (MulAction.orbitRel Γ A) (g⁻¹ • oA.out) =
      Quotient.mk _ oA.out).trans (Quotient.out_eq oA)

end Fibre

section Sub

variable {Y : Type*} [MulAction Γ Y]

@[reducible] def subAct (X : Set Y) (hX : ∀ (g : Γ) y, y ∈ X → g • y ∈ X) : MulAction Γ X where
  smul g y := ⟨g • y.1, hX g y.1 y.2⟩
  one_smul y := Subtype.ext (one_smul Γ y.1)
  mul_smul g h y := Subtype.ext (mul_smul g h y.1)

def subStab (X : Set Y) (hX : ∀ (g : Γ) y, y ∈ X → g • y ∈ X) (y : X) :
    (letI := subAct X hX; MulAction.stabilizer Γ y) ≃ MulAction.stabilizer Γ y.1 := by
  letI := subAct X hX
  exact
    { toFun := fun g => ⟨g.1, by
        have h := MulAction.mem_stabilizer_iff.1 g.2
        exact MulAction.mem_stabilizer_iff.2 (congrArg Subtype.val h)⟩
      invFun := fun g => ⟨g.1, by
        rw [MulAction.mem_stabilizer_iff]
        exact Subtype.ext (MulAction.mem_stabilizer_iff.1 g.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Sub

section Pair

variable {Y : Type*} [MulAction Γ Y]

end Pair

section Local

variable {T : Type*} [MulAction Γ T]

end Local

end Formalism.L2.SG.Pf.StabilizerMassQuotient
