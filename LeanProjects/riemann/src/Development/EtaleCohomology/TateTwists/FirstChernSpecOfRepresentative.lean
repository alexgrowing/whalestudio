import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.EtaleCohomology.TateTwists.FirstChernClassSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleFirstChernKummerCocycleRep (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def first_chern_class_exists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsEtaleFirstChernKummerCocycleRep q L γ

def first_chern_class_unique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernKummerCocycleRep q L γ → IsEtaleFirstChernKummerCocycleRep q L γ' → CohomologyClass.mk γ = CohomologyClass.mk γ'

def firstChernClassTateTwist_pullback : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
  ∀ γ, IsEtaleFirstChernKummerCocycleRep q L γ → ∃ γ', IsEtaleFirstChernKummerCocycleRep q (f ≫ L) γ' ∧ CohomologyClass.mk γ' = pull _ f _ _ (CohomologyClass.mk γ)

def isOneCochain_add : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
  (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
  ∀ γL γM, IsEtaleFirstChernKummerCocycleRep q L γL → IsEtaleFirstChernKummerCocycleRep q M γM →
    ∃ γN, IsEtaleFirstChernKummerCocycleRep q N γN ∧ CohomologyClass.mk γN = CohomologyClass.mk γL + CohomologyClass.mk γM

end LateralTheory.EtaleFoundations
