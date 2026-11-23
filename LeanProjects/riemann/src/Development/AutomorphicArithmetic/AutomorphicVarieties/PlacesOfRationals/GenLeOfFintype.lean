import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum

namespace UpperTheory.V.B3

section Grp

variable {Γ : Type} [Group Γ]

def GenLe (H : Subgroup Γ) (r : ℕ) : Prop := ∃ x : Fin r → Γ, Subgroup.closure (Set.range x) = H

theorem genLe_of_fintype {κ : Type} [Fintype κ] (x : κ → Γ) {r : ℕ} (h : Fintype.card κ ≤ r) :
    GenLe (Subgroup.closure (Set.range x)) r := by
  classical
  obtain ⟨f⟩ : Nonempty (κ ↪ Fin r) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  refine ⟨Function.extend f x 1, le_antisymm ((Subgroup.closure_le _).2 ?_) (Subgroup.closure_mono ?_)⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hi : ∃ k, f k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [f.injective.extend_apply]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    · rw [Function.extend_apply' _ _ _ hi]
      exact one_mem _
  · rintro _ ⟨k, rfl⟩
    exact ⟨f k, f.injective.extend_apply _ _ _⟩

theorem GenLe.mono {H : Subgroup Γ} {r s : ℕ} (h : GenLe H r) (hrs : r ≤ s) : GenLe H s := by
  obtain ⟨x, rfl⟩ := h
  exact genLe_of_fintype x (by simpa using hrs)

theorem GenLe.map {Γ' : Type} [Group Γ'] {H : Subgroup Γ} {r : ℕ} (h : GenLe H r) (f : Γ →* Γ') : GenLe (H.map f) r := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨f ∘ x, by rw [MonoidHom.map_closure, Set.range_comp]⟩

def pairSum {ι : Type} [LinearOrder ι] (S : Finset ι) (r : ι → ℕ) : ℕ := ∑ i ∈ S, ∑ j ∈ S with i < j, r i * r j

variable {C : Type} [CommGroup C]

def orbSpan {κ : Type} (ρ : Γ →* Monoid.End C) (a : κ → C) : Subgroup C :=
  Subgroup.closure {c | ∃ σ i, c = ρ σ (a i)}

def OrbGen (ρ : Γ →* Monoid.End C) (A : Subgroup C) (g : ℕ) : Prop := ∃ a : Fin g → C, orbSpan ρ a = A

def coinv (l : ℕ) (ρ : Γ →* Monoid.End C) : Subgroup C :=
  Subgroup.closure ({c | ∃ a, c = a ^ l} ∪ {c | ∃ σ a, c = ρ σ a * a⁻¹})

theorem OrbGen.mono {ρ : Γ →* Monoid.End C} {A : Subgroup C} {g g' : ℕ} (h : OrbGen ρ A g) (hg : g ≤ g') :
    OrbGen ρ A g' := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨fun i => if h : i.1 < g then a ⟨i.1, h⟩ else 1, le_antisymm ((Subgroup.closure_le _).2 ?_)
    (Subgroup.closure_mono ?_)⟩
  · rintro _ ⟨σ, i, rfl⟩
    by_cases h : i.1 < g
    · simp only [dif_pos h]
      exact Subgroup.subset_closure ⟨σ, _, rfl⟩
    · simp only [dif_neg h, map_one]
      exact one_mem _
  · rintro _ ⟨σ, i, rfl⟩
    exact ⟨σ, Fin.castLE hg i, by simp⟩

end Grp

section Fld

variable (k L : Type) [Field k] [Field L] [NumberField L] [Algebra k L]

def clAct : (L ≃ₐ[k] L) →* Monoid.End (ClassGroup (𝓞 L)) where
  toFun σ := clMap σ.toRingEquiv
  map_one' := MonoidHom.ext fun c => Stick.clMap_refl L c
  map_mul' σ τ := MonoidHom.ext fun c => Stick.clMap_trans τ.toRingEquiv σ.toRingEquiv c

def ClGen (l g : ℕ) [Fact l.Prime] : Prop :=
  OrbGen (clAct k L) (CommGroup.primaryComponent (ClassGroup (𝓞 L)) l) g

variable (Ω : Type) [Field Ω] [Algebra k Ω]

abbrev resL [Algebra L Ω] [IsScalarTower k L Ω] [Normal k L] : G k Ω →* (L ≃ₐ[k] L) := AlgEquiv.restrictNormalHom L

def NoUnram [NumberField k] (l : ℕ) : Prop :=
  ∀ (N : Subgroup (G k Ω)) [N.Normal], IsOpen (N : Set (G k Ω)) → IsPGroup l (G k Ω ⧸ N) →
    (∀ B : ValuationSubring Ω, Ine (F := k) B ≤ N) → N = ⊤

end Fld

def pPart (m p : ℕ) : Subgroup (ZMod m)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd m p)).ker

def IsRecip (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra ℚ Ω] [Algebra L Ω] [IsScalarTower ℚ L Ω] [Normal ℚ L]
    {m : ℕ} (π : (ZMod m)ˣ →* (L ≃ₐ[ℚ] L)) : Prop :=
  ∀ g : G ℚ Ω, ∃ u : (ZMod m)ˣ, (∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ (u : ZMod m).val) ∧ resL ℚ L Ω g = π u

def rk (p : ℕ) : ℕ := if p = 2 then 2 else 1

theorem jacobi_val_mul {N q : ℕ} [NeZero N] (h : q ∣ N) (a b : ZMod N) :
    jacobiSym (((a * b).val : ℕ) : ℤ) q = jacobiSym ((a.val : ℕ) : ℤ) q * jacobiSym ((b.val : ℕ) : ℤ) q := by
  rw [← jacobiSym.mul_left, ZMod.val_mul]
  apply jacobiSym.mod_left'
  exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.mod_mod_of_dvd _ h)

theorem jacobi_val_one {N q : ℕ} [NeZero N] (h : q ∣ N) : jacobiSym ((((1 : ZMod N)).val : ℕ) : ℤ) q = 1 := by
  rw [← jacobiSym.one_left q, ZMod.val_one_eq_one_mod]
  apply jacobiSym.mod_left'
  exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.mod_mod_of_dvd _ h)

def jacKer {N q : ℕ} [NeZero N] (h : q ∣ N) : Subgroup (ZMod N)ˣ where
  carrier := {u | jacobiSym (((u : ZMod N).val : ℕ) : ℤ) q = 1}
  one_mem' := jacobi_val_one h
  mul_mem' {a b} ha hb := by
    show jacobiSym ((((a : ZMod N) * b).val : ℕ) : ℤ) q = 1
    rw [jacobi_val_mul h, ha, hb, one_mul]
  inv_mem' {a} ha := by
    have := jacobi_val_mul h (a : ZMod N) (a⁻¹ : (ZMod N)ˣ)
    rw [Units.mul_inv, jacobi_val_one h, ha, one_mul] at this
    exact this.symm

def Lm (m q d : ℕ) [NeZero q] [NeZero d] : AbF where
  m := 2 ^ (m + 2) * q * d
  pos := Nat.pos_of_ne_zero (NeZero.ne _)
  H := (ZMod.unitsMap (((dvd_refl (2 ^ (m + 2))).mul_right q).mul_right d)).ker ⊓
    jacKer ((dvd_mul_left q (2 ^ (m + 2))).mul_right d) ⊓ jacKer (dvd_mul_left d (2 ^ (m + 2) * q))

end UpperTheory.V.B3

end
