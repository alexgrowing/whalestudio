import Development.EtaleCohomology.EtaleSheaves.LeafObjGluePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf

namespace LateralTheory.E.LeafInclDescendPf

def bcLift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Y ⟶ pullback q (incl h) :=
  pullback.lift v (g ≫ toR R'') (by rw [Category.assoc, toR_eq, w])

theorem bcLift_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (hp : IsPullback v g q (toR R)) :
    IsPullback (bcLift h hp.w) g (pullback.snd q (incl h)) (toR R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  simp only [bcLift]
  rw [pullback.lift_fst, toR_eq]
  exact hp

def LeafInclPiece : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R''), R' ≤ R'' →
      ∃ φ : pullback qW (incl h) ⟶ pullback qU (incl h), IsOpenImmersion φ ∧
        φ ≫ pullback.snd qU (incl h) = pullback.snd qW (incl h) ∧
        bcLift h hW.w ≫ φ = X.homOfLE hWU ≫ bcLift h hU.w

theorem LeafInclDescend_of (hP : LeafInclPiece) : LeafInclDescend := by
  intro k _ Ω _ _ X f hf U V R hR ⟨DU, qU, vU, hqU, pU⟩ ⟨DV, qV, vV, hqV, pV⟩ ⟨DW, qW, vW, hqW, pW⟩
  obtain ⟨R1, h1, hR1, H1⟩ := hP k Ω f hf U (U ⊓ V) inf_le_left R hR DU DW qU qW vU vW hqU hqW pU pW
  obtain ⟨R2, h2, hR2, H2⟩ := hP k Ω f hf V (U ⊓ V) inf_le_right R hR DV DW qV qW vV vW hqV hqW pV pW
  have hle : R ≤ R1 ⊔ R2 := h1.trans le_sup_left
  obtain ⟨φU, oU, sU, cU⟩ := H1 (R1 ⊔ R2) hle le_sup_left
  obtain ⟨φV, oV, sV, cV⟩ := H2 (R1 ⊔ R2) hle le_sup_right
  exact ⟨R1 ⊔ R2, hle, hR1.sup hR2, _, _, _, pullback.snd qU (incl hle), pullback.snd qV (incl hle),
    pullback.snd qW (incl hle), bcLift hle pU.w, bcLift hle pV.w, bcLift hle pW.w, φU, φV,
    fp_snd _ _ hqU, fp_snd _ _ hqV, fp_snd _ _ hqW, oU, oV, sU, sV,
    bcLift_isPullback hle pU, bcLift_isPullback hle pV, bcLift_isPullback hle pW, cU, cV⟩

end LateralTheory.E.LeafInclDescendPf
end
