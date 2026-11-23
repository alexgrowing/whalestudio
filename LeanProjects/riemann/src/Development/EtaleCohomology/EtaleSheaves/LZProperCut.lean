import Development.EtaleCohomology.EtaleSheaves.LineZeroCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.LineZeroCut

namespace LateralTheory.E.LZProperCut

def LZReduce : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r → ConnectedSpace X → ¬ PreconnectedSpace ↑(pullback r (cpt A)) →
  ∃ (A' : Type) (_ : CommRing A') (_ : IsLocalRing A') (_ : HenselianLocalRing A') (_ : IsNoetherianRing A')
    (X' : Scheme.{0}) (r' : X' ⟶ Spec (CommRingCat.of A')),
    IsProper r' ∧ ConnectedSpace X' ∧ ¬ PreconnectedSpace ↑(pullback r' (cpt A'))

def LZStein : Prop := ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r →
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B) (s : X ⟶ Spec (CommRingCat.of B)),
    s ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = r ∧
    (ConnectedSpace X → ConnectedSpace ↑(Spec (CommRingCat.of B))) ∧
    ∀ y : ↑(Spec (CommRingCat.of B)), _root_.IsPreconnected (s.base ⁻¹' {y})

def LZHensFinite : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B],
  ConnectedSpace ↑(Spec (CommRingCat.of B)) → IsLocalRing B

def LZPreimage : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Type) [CommRing B] [Algebra A B]
  [Module.Finite A B] [IsLocalRing B],
  (Spec.map (CommRingCat.ofHom (algebraMap A B))).base ⁻¹' {IsLocalRing.closedPoint A} = {IsLocalRing.closedPoint B}

def LZFibre : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (r : X ⟶ Spec (CommRingCat.of A)),
  _root_.IsPreconnected (r.base ⁻¹' {IsLocalRing.closedPoint A}) → PreconnectedSpace ↑(pullback r (cpt A))

theorem noeth_of (hS : LZStein) (hH : LZHensFinite) (hP : LZPreimage) (hF : LZFibre)
    (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (r : X ⟶ Spec (CommRingCat.of A)) (hr : IsProper r) (hX : ConnectedSpace X) :
    PreconnectedSpace ↑(pullback r (cpt A)) := by
  apply hF A r
  obtain ⟨B, _, _, _, s, hs, hconn, hfib⟩ := hS A r hr
  have hB := hconn hX
  have : IsLocalRing B := hH A B hB
  have key : r.base ⁻¹' {IsLocalRing.closedPoint A} = s.base ⁻¹' {IsLocalRing.closedPoint B} := by
    rw [← hP A B, ← hs]
    rfl
  rw [key]
  exact hfib _

theorem goal_of (hR : LZReduce) (hS : LZStein) (hH : LZHensFinite) (hP : LZPreimage) (hF : LZFibre) :
    LateralTheory.E.LineZeroCut.LZProper := by
  intro A _ _ _ X r hr hX
  by_contra hn
  obtain ⟨A', _, _, _, _, X', r', hr', hX', hn'⟩ := hR A r hr hX hn
  exact hn' (noeth_of hS hH hP hF A' r' hr' hX')

end LateralTheory.E.LZProperCut
