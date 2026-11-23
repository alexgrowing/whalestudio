import Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFiniteness

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutLocallyQuasiFinite

def LeafQFAtBaseChange : Prop := ∀ {EA EB A B : Scheme.{0}} (h : EA ⟶ EB) (g : A ⟶ B) (rA : EA ⟶ A) (rB : EB ⟶ B),
    IsPullback rA h g rB → LocallyOfFiniteType g → ∀ x : EA, g.QuasiFiniteAt (rA x) → h.QuasiFiniteAt x

def LeafQFAtDescend : Prop := ∀ {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B),
    IsPullback vA γ g vB → LocallyOfFiniteType g → ∀ x : CA, γ.QuasiFiniteAt x → g.QuasiFiniteAt (vA x)

def LeafOpenSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C A : Scheme.{0}} (c : C ⟶ Sp Ω) (p : A ⟶ Sp R) (v : C ⟶ A) (U : A.Opens),
    (LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p) → IsPullback v c p (toR R) →
    (∀ x : C, v x ∈ U) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ A), IsPullback r q' p (incl hR) → ∀ z : E, r z ∈ U

theorem quasi_finite_at_base_change_of_finite_type : LeafQFAtBaseChange := by
  intro EA EB A B h g rA rB sq hg x hx
  let U := g.quasiFiniteLocus
  have sq2 : IsPullback (rA ∣_ U) ((rA ⁻¹ᵁ U).ι ≫ h) (U.ι ≫ g) rB :=
    (isPullback_morphismRestrict rA U).paste_vert sq
  have : LocallyQuasiFinite ((rA ⁻¹ᵁ U).ι ≫ h) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq2 inferInstance
  have hxV : x ∈ rA ⁻¹ᵁ U := hx
  have := ((rA ⁻¹ᵁ U).ι ≫ h).quasiFiniteAt ⟨x, hxV⟩
  have h2 := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (rA ⁻¹ᵁ U).ι) (g := h)
    (x := ⟨x, hxV⟩)).mp this
  simpa using h2

theorem LeafSpreadLQFMap_of (hBC : LeafQFAtBaseChange) (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := by
  intro k _ Ω _ _ R hR CA CB A B cB γ qB g vA vB hB hA pB pA hw hγ
  have : LocallyOfFinitePresentation (g ≫ qB) := hA.1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g qB
  have sqC : IsPullback vA γ g vB := IsPullback.of_bot pA hw.symm pB
  have hU : ∀ x : CA, vA x ∈ g.quasiFiniteLocus := fun x =>
    hD γ g vA vB sqC inferInstance x (γ.quasiFiniteAt x)
  obtain ⟨S, hRS, hS, H⟩ := hO k Ω R hR (γ ≫ cB) (g ≫ qB) vA g.quasiFiniteLocus hA pA hU
  refine ⟨S, hRS, hS, ?_⟩
  intro R' hSR' hRR' EA EB qB' h rA rB QB QA hc
  have sqE : IsPullback rA h g rB := IsPullback.of_bot QA hc.symm QB
  have : LocallyOfFiniteType h :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqE inferInstance
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.mp fun z _ => ?_
  exact hBC h g rA rB sqE inferInstance z (H R' hSR' hRR' EA (h ≫ qB') rA QA z)

end LateralTheory.E.SpreadingOutLocallyQuasiFinite

end
