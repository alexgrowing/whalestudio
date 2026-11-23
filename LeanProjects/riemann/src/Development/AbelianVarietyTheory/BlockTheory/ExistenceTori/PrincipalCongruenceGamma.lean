import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsPrinc (X : Data E r) (M : ℕ) (γ : GL (Fin r) E) : Prop :=
  IsUStab X.Gm X.Λ γ ∧
    ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = M • y

def princ (X : Data E r) (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | IsPrinc X M γ}
  one_mem' := by
    refine ⟨⟨fun x y => by simp, fun x => by simp⟩, fun x _ => ⟨0, X.Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨ha1, ha2⟩, ha3⟩ ⟨⟨hb1, hb2⟩, hb3⟩
    refine ⟨⟨fun x y => ?_, fun x => ?_⟩, fun x hx => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha1, hb1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha2, ← hb2]
    · obtain ⟨y, hy, e⟩ := hb3 x hx
      obtain ⟨z, hz, e'⟩ := ha3 _ ((hb2 x).1 hx)
      refine ⟨z + y, X.Λ.add_mem hz hy, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, smul_add, ← e, ← e']
      abel
  inv_mem' := by
    rintro a ⟨⟨ha1, ha2⟩, ha3⟩
    have hc : ∀ x : Fin r → E, Matrix.mulVec (a : Matrix (Fin r) (Fin r) E)
        (Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hm : ∀ x, x ∈ X.Λ ↔ Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x ∈ X.Λ := by
      intro x
      rw [ha2 (Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x), hc]
    refine ⟨⟨fun x y => ?_, hm⟩, fun x hx => ?_⟩
    · rw [← ha1, hc, hc]
    · obtain ⟨y, hy, e⟩ := ha3 _ ((hm x).1 hx)
      refine ⟨-y, X.Λ.neg_mem hy, ?_⟩
      rw [hc] at e
      rw [smul_neg, ← e]
      abel

end Model

variable {D : D7}

def GamAt (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Prop :=
  ∀ k : (T.U j σ).Comp, princ ((T.U j σ).X k) T.Q.l.M ≤ ((T.U j σ).X k).Γ

def GamEqAt (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Prop :=
  ∀ k : (T.U j σ).Comp, ((T.U j σ).X k).Γ = princ ((T.U j σ).X k) T.Q.l.M

def Gam (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → GamAt T j σ

def GamEq (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → GamEqAt T j σ

theorem GamEqAt.gamAt {T : Core D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (h : GamEqAt T j σ) : GamAt T j σ :=
  fun k => (h k).ge

theorem GamEq.gam {T : Core D} (h : GamEq T) : Gam T := fun j hj σ hσ => (h j hj σ hσ).gamAt

end GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma
