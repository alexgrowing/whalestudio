import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
open UpperTheory.Gal.Int.Geo
open CategoryTheory AlgebraicGeometry

private theorem powMap_congr {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f f' : S' ⟶ S} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ h k = GlobalTheory.KS.powMap f' φ' h' k := by
  subst hf hφ
  rfl

theorem UpperTheory.tower_invariant_of_base_invariant_powerCartesian :
    BaseInv → PowCart → PiInv := by
  intro hB hP p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu x y
  obtain ⟨π, o, ψ, φ, hw, ov, tr, e⟩ := T.tr_eq N' N u x y
  obtain ⟨h1, h2⟩ := hB p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu
    ⟨π, o, ψ, φ, ov, tr⟩
  have h1' : π ≫ C.j = C'.j := h1
  have h2' : (ψ.left ≫ φ.φ) ≫ C.m.φ = C'.m.φ := by
    rw [Category.assoc]; exact h2
  have hv := C.m.cart.1.w
  have hw' : ((ψ.left ≫ φ.φ) ≫ C.m.φ) ≫ S.Y.univ.A.hom = (T.M N').univ.A.hom ≫ π ≫ C.j := by
    rw [Category.assoc, hv, ← Category.assoc, hw, Category.assoc]
  have hc := (hP _ _ _ (T.M N').univ.A (T.M N).univ.A S.Y.univ.A π C.j (ψ.left ≫ φ.φ) C.m.φ hw hv k).2.2 hw'
  simp only [Site.pi, Cls.pw]
  rw [← Category.assoc, e, Category.assoc, hc]
  exact congrArg _ (powMap_congr h1' h2' _ _ k)
