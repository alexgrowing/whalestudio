import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairGPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf LateralTheory.E.LeafUnitPairPf

def IsAct (q : ℕ) (i : ℤ) (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) : Prop :=
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.res g (L U t a b) = L V t (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.map ((res _ (tw q i)).d t (t + 1)) (L U t a b) = L U (t + 1) a (Sec.map ((res _ (tw q i)).d t (t + 1)) b)

def LeafUnitAct : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ L, IsAct q i L ∧
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U), L U t (twGen 0 ζ) b = b

def LeafPairExt : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map (resι _ (tw q 0)) a) b = L U t a b

theorem LeafUnitPairG_of (hact : LeafUnitAct) (hext : LeafPairExt) : LeafUnitPairG := by
  intro q _ i
  obtain ⟨L, hL, hLζ⟩ := hact q i
  obtain ⟨ν, hν⟩ := hext q i L hL
  refine ⟨ν, fun U t ζ b => ?_⟩
  exact (hν U t (twGen 0 ζ) b).trans (hLζ U t ζ b)

end LateralTheory.E.LeafUnitPairGPf
