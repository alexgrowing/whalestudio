import Mathlib

noncomputable section

namespace UpperTheory.V.AlgebraTools

section Irr

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def StableOn (ρ : Representation k G V) (H : Subgroup G) (W : Submodule k V) : Prop :=
  ∀ h ∈ H, ∀ v ∈ W, ρ h v ∈ W

def IrrOn (ρ : Representation k G V) (H : Subgroup G) : Prop :=
  ∀ W : Submodule k V, StableOn ρ H W → W = ⊥ ∨ W = ⊤

theorem IrrOn.mono {ρ : Representation k G V} {H H' : Subgroup G} (h : IrrOn ρ H) (hle : H ≤ H') : IrrOn ρ H' :=
  fun W hW => h W fun g hg => hW g (hle hg)

theorem irrOn_iff_comp (ρ : Representation k G V) (H : Subgroup G) :
    IrrOn ρ H ↔ IrrOn (ρ.comp H.subtype : Representation k H V) ⊤ :=
  ⟨fun h W hW => h W fun g hg => hW ⟨g, hg⟩ trivial, fun h W hW => h W fun g _ => hW g g.2⟩

theorem isIrreducible_iff (ρ : Representation k G V) : ρ.IsIrreducible ↔ Nontrivial V ∧ IrrOn ρ ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      exact bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g trivial v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hV, h⟩
    haveI : Nontrivial (Subrepresentation ρ) :=
      ⟨⊥, ⊤, fun e => bot_ne_top (α := Submodule k V) (congrArg Subrepresentation.toSubmodule e)⟩
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun g _ v hv => W.apply_mem_toSubmodule g hv) with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective e)
    · exact Or.inr (Subrepresentation.toSubmodule_injective e)

theorem irrOn_line (ρ : Representation k G k) (H : Subgroup G) : IrrOn ρ H :=
  fun W _ => Ideal.eq_bot_or_top W

def matRep {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n k) : Representation k G (n → k) where
  toFun g := Matrix.toLin' (r g : Matrix n n k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

@[simp] theorem matRep_apply {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n k) (g : G) (v : n → k) :
    matRep r g v = (r g : Matrix n n k).mulVec v := by
  simp [matRep]

end Irr

def subst {k n : Type} [CommRing k] [Fintype n] (A : Matrix n n k) : MvPolynomial n k →ₐ[k] MvPolynomial n k :=
  MvPolynomial.aeval fun i => ∑ j, A j i • MvPolynomial.X j

theorem subst_X {k n : Type} [CommRing k] [Fintype n] (A : Matrix n n k) (i : n) :
    subst A (MvPolynomial.X i) = ∑ j, A j i • MvPolynomial.X j := by
  simp [subst]

theorem subst_one {k n : Type} [CommRing k] [Fintype n] [DecidableEq n] :
    subst (1 : Matrix n n k) = AlgHom.id k _ := by
  ext1 i
  simp [subst, Matrix.one_apply]

theorem subst_mul {k n : Type} [CommRing k] [Fintype n] (A B : Matrix n n k) :
    subst (A * B) = (subst A).comp (subst B) := by
  ext1 i
  simp only [AlgHom.comp_apply, subst_X, map_sum, map_smul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

end UpperTheory.V.AlgebraTools
