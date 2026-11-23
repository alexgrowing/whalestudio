import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Coord

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) (q qi : E) {r : ℕ}

def cor (r : ℕ) (a b : Fin (r + 1)) (c : E) : E := if a = Fin.last r ∧ b = Fin.last r then c else 0

def gramG (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Matrix (Ix r) (Ix r) E :=
  Matrix.fromBlocks (Matrix.of fun a b => cor r a b (-T))
    (Matrix.of fun a b => qi * (cj (Z a b) + cor r a b T))
    (Matrix.of fun a b => qi * (Z b a + cor r a b T))
    (Matrix.of fun a b => qi * qi * (-(Z b a) - cj (Z a b) - cor r a b (T + T')))

def relG (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Submodule O (Ix r → O) where
  carrier := {y | ∃ c : Ix r → O, ∀ j, (y j : E) = ∑ i, (c i : E) * gramG cj qi Z T T' i j}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun j => ?_⟩
    simp only [Pi.add_apply, Subring.coe_add, hc j, hd j, add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, fun j => by simp⟩
  smul_mem' := by
    rintro a y ⟨c, hc⟩
    refine ⟨a • c, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hc j, Finset.mul_sum, mul_assoc]

abbrev DDg (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : Type :=
  (Ix r → O) ⧸ relG O cj qi Z T T'

def formG (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W : Ix r → O) : E :=
  ∑ i, ∑ j, (Y i : E) * (gramG cj qi Z T T')⁻¹ i j * cj (W j)

def GamRC (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) :
    Set (DDg O cj qi Z T T' × DDg O cj qi Z T T' × (E × E) × (E × E)) :=
  {p | ∃ Y Y' Y'' : Ix r → O, (∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) ∧
    (∀ a : Fin r, (Y' (Sum.inl a.castSucc) : E) + q * Y' (Sum.inr a.castSucc) = 0) ∧
    (∀ i, (Y i : E) - Y' i = q * Y'' i) ∧
    p = (Submodule.Quotient.mk Y, Submodule.Quotient.mk Y'',
      ((Y (Sum.inl (Fin.last r)) : E), lamStarC cj Z (fun b => (Y (Sum.inl b) : E) + q * Y (Sum.inr b))),
      (lamC Z (fun a => (Y' (Sum.inl a) : E)),
        (Y' (Sum.inl (Fin.last r)) : E) + q * Y' (Sum.inr (Fin.last r))))}

def ThetaGC (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) :
    Set (DDg O cj qi Z₁ T T' ≃ₗ[O] DDg O cj qi Z₂ T T') :=
  {θ | (∀ Y W Y₂ W₂ : Ix r → O, θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ →
      θ (Submodule.Quotient.mk W) = Submodule.Quotient.mk W₂ →
      formG O cj qi Z₂ T T' Y₂ W₂ - formG O cj qi Z₁ T T' Y W ∈ O) ∧
    (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) '' GamRC O cj q qi Z₁ T T' = GamRC O cj q qi Z₂ T T'}

end Coord

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
