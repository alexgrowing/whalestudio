import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineZeroCut

def LZNonempty : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)),
  UniversallyClosed p → Nonempty X → Nonempty ↑(pullback p (cpt A))

def LZDescend : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)),
  IsIntegralHom u → IsProper l → ¬ PreconnectedSpace ↑(pullback (u ≫ l) (cpt A)) →
  ∃ (Y : Scheme.{0}) (v : Z ⟶ Y) (r : Y ⟶ Spec (CommRingCat.of A)),
    IsProper r ∧ Surjective v ∧ v ≫ r = u ≫ l ∧ ¬ PreconnectedSpace ↑(pullback r (cpt A))

def LZProper : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r → ConnectedSpace X → PreconnectedSpace ↑(pullback r (cpt A))

theorem lzNonempty : LZNonempty := by
  intro A _ _ X p hp hX
  obtain ⟨x⟩ := hX
  have hc : IsClosed (Set.range p.base) := p.isClosedMap.isClosed_range
  have h1 : IsLocalRing.closedPoint A ∈ Set.range p.base := by
    have : IsLocalRing.closedPoint A ∈ closure {p.base x} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).1 (IsLocalRing.le_maximalIdeal (p.base x).isPrime.ne_top)
    exact closure_minimal (by simp) hc this
  obtain ⟨z, hz⟩ := h1
  have h2 : (cpt A) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) = IsLocalRing.closedPoint A :=
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) :=
      (inferInstance : IsLocalHom (IsLocalRing.residue A))
    Spec_closedPoint
  obtain ⟨w, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := cpt A) z
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) (by rw [hz, h2])
  exact ⟨w⟩

theorem goal_of (h2 : LZDescend) (h3 : LZProper) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have := hl.1
  have := hZ.1
  have hne : Nonempty ↑(pullback (u ≫ l) (cpt A)) := lzNonempty A (u ≫ l) inferInstance inferInstance
  have hpre : PreconnectedSpace ↑(pullback (u ≫ l) (cpt A)) := by
    by_contra hn
    obtain ⟨Y, v, r, hr, hv, -, hY⟩ := h2 A u l hu hl.1 hn
    have hZc : ConnectedSpace Z := inferInstance
    have hYc : ConnectedSpace Y := hv.surj.connectedSpace v.continuous
    exact hY (h3 A r hr hYc)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.LineZeroCut
