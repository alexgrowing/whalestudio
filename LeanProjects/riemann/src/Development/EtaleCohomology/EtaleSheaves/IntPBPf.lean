import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntPBPf

def IntHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] (φ : A →+* B), φ.IsIntegral →
  HenselianRing B ((IsLocalRing.maximalIdeal A).map φ)

def IntFib : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p →
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B), φ.IsIntegral ∧ ∀ (q : ℕ) (i : ℤ),
    Eqv _ (spMap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ))) (tw q i) →
    Eqv _ (sch.map (pullback.fst p (LateralTheory.E.t_E2Cut.cpt A))) (tw q i)

theorem IntPB_of (hH : IntHens) (hF : IntFib) : LateralTheory.E.t_E2Cut.IntPB := by
  intro hyp q i A _ _ hSH hq X p hp
  obtain ⟨hA, -⟩ := hSH
  obtain ⟨B, _, φ, hφ, hE⟩ := hF A p hp
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map φ) := hH A B φ hφ
  have hqB : IsUnit ((q : ℕ) : B) := by simpa using hq.map φ
  exact hE q i (hyp.e1 q B _ hqB i)

end LateralTheory.E.IntPBPf
