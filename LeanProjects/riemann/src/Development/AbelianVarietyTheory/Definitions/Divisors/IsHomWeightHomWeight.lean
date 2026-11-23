import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts
open GlobalTheory.AllWt (secZ exOf wtOf lieFacZ modelWt homN)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag kap)
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {r : ℕ}

section Flag

variable (X : FlagCover Y) {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

def FrameAt (z : Sp (CAt σ) ⟶ X.YY) (j : X.F.J) (k : U.Comp) (w : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ) : Prop :=
  ∃ (hj : ⊤ ≤ z ⁻¹ᵁ X.F.U j) (Q : FrPt Xo c (CAt σ)), X.F.ChartFr j z hj Q ∧ FrBor t Q (U.un k w)

variable {X U} {z : Sp (CAt σ) ⟶ X.YY} {j j' : X.F.J} {k k' : U.Comp} {w : (U.X k).dom} {w' : (U.X k').dom}
  {t t' : Ix Dw → (CAt σ)ˣ}

theorem FrameAt.eq_ptY (h : FrameAt X U z j k w t) : z = X.ptY (U.un k w) :=
  let ⟨_, _, hQ, ht⟩ := h
  FlagCover.eq_ptY (hQ.lies.frBor ht)

theorem exists_frameAt_of_eq (h : z = X.ptY (U.un k w)) (hj : ⊤ ≤ z ⁻¹ᵁ X.F.U j) : ∃ t, FrameAt X U z j k w t := by
  obtain rfl := h.trans (X.pt_inc _).symm
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor _ j hj
  exact ⟨t, hj, Q, hQ, ht⟩

theorem exists_eq_ptY (hU : IsUnf U) (hz : z ≫ flagStr X = spMap σ) (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen X) :
    ∃ k w, z = X.ptY (U.un k w) := by
  have hr : Set.range z ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc X).ge (hO (Set.mem_univ s))
  obtain ⟨v, rfl⟩ : ∃ v, v ≫ X.inc = z := ⟨_, IsOpenImmersion.lift_fac X.inc z hr⟩
  have e : Y.j ≫ Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨P, rfl⟩ := (X.points.1 v).1 (by
    rw [← e, ← pullback.condition_assoc]; exact (Category.assoc _ _ _).symm.trans hz)
  obtain ⟨k, w, t, ht⟩ := hU.2.2.1 P
  exact ⟨k, w, (X.pt_inc P).trans (X.ptY_frBor ht).symm⟩

variable (X U)

open Classical in

def flagLog (la : AllWt.Weight Dw) (j : X.F.J) (y : CxPts (flagStr X) σ) : ℝ :=
  if h : ∃ q : (Σ k, (U.X k).dom) × (Ix Dw → (CAt σ)ˣ), FrameAt X U y.1 j q.1.1 q.1.2 q.2 then
    -Real.log (genNorm U x la h.choose.1.1 h.choose.1.2 h.choose.2 ^ 2) else 0

def flagWeight (la : AllWt.Weight Dw) : Weight (flagStr X) σ (X.LL (exOf Dw la 0)) :=
  Weight.ofPick (X.F.isLB_LL _) (flagLog X U x la)

variable {X U}

end Flag

variable {X : FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

abbrev Lmod (la : AllWt.Weight Dw) : LB M.X := (L₀ X Z la).pull M.σ

def flagPt {σ : c.F →+* ℂ} (y : CxPts M.str σ) : Sp (CAt (goodOf c σ)) ⟶ X.YY := (goodPt y).1 ≫ toFlag M

def IsHomWeight (la : AllWt.Weight Dw) {σ : c.F →+* ℂ} (φ : Weight M.str σ (Lmod M la)) : Prop :=
  ∀ y ∈ ptsIn M.str σ M.off, ∀ j k w t, FrameAt X (U (goodOf c σ)) (flagPt M y) j k w t →
    Real.exp (-φ.φ (flagIdx M la j) y) = genNorm (U (goodOf c σ)) x la k w t ^ 2

def homWeight (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) : Weight M.str σ (Lmod M la) :=
  ((atGood (flagWeight X (U (goodOf c σ)) x la)).pull (inc₀ X Z) rfl).pull M.σ rfl

theorem homWeight_φ (la : AllWt.Weight Dw) {σ : c.F →+* ℂ} (j : X.F.J) (y : CxPts M.str σ)
    (z : CxPts (flagStr X) (goodOf c σ)) (hz : z.1 = flagPt M y) :
    (homWeight M U x la σ).φ (flagIdx M la j) y = (flagWeight X (U (goodOf c σ)) x la).φ j z :=
  (Weight.pull_φ _ _ _ _ _).trans ((Weight.pull_φ _ _ _ _ _).trans (congrArg ((flagWeight X _ x la).φ j)
    (Subtype.ext ((goodPt_map (f := toFlag M) (z := y) (Category.assoc _ _ _)).trans hz.symm))))

theorem flagPt_str {σ : c.F →+* ℂ} (y : CxPts M.str σ) : flagPt M y ≫ flagStr X = spMap (goodOf c σ) :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (goodPt y).2)

variable {U} {σ : c.F →+* ℂ} {la a b : AllWt.Weight Dw}

variable {M x} {y : CxPts M.str σ}

theorem mem_flagIdx {j : X.F.J} :
    y ∈ ptsIn M.str σ ((Lmod M la).U (flagIdx M la j)) ↔ ⊤ ≤ (y.1 ≫ toFlag M) ⁻¹ᵁ X.F.U j :=
  mem_ptsIn.trans ((((common₀ X Z).pull M.σ).mem la j _).trans
    (mem_ptsIn (y := y) (U := toFlag M ⁻¹ᵁ X.F.U j)).symm)

theorem exists_eq_flagIdx (i : (Lmod M la).ι) : ∃ j, i = flagIdx M la j := ⟨i PUnit.unit PUnit.unit, rfl⟩

theorem exists_flagPt_eq (hU : IsUnf (U (goodOf c σ))) (hy : y ∈ ptsIn M.str σ M.off) :
    ∃ k w, flagPt M y = X.ptY ((U (goodOf c σ)).un k w) :=
  exists_eq_ptY hU (flagPt_str M y) (ptsIn_mono M.off_eq.le (goodPt_mem hy))

theorem exists_frameAt (hU : IsUnf (U (goodOf c σ))) (hy : y ∈ ptsIn M.str σ M.off) {j : X.F.J}
    (hj : y ∈ ptsIn M.str σ ((Lmod M la).U (flagIdx M la j))) :
    ∃ k w t, FrameAt X (U (goodOf c σ)) (flagPt M y) j k w t :=
  let ⟨k, w, h⟩ := exists_flagPt_eq hU hy
  ⟨k, w, exists_frameAt_of_eq h (mem_flagIdx.1 (goodPt_mem hj))⟩

namespace IsHomWeight

variable {φ φ' : Weight M.str σ (Lmod M la)}

theorem unique (hU : IsUnf (U (goodOf c σ))) (h : IsHomWeight M U x la φ) (h' : IsHomWeight M U x la φ')
    (i : (Lmod M la).ι) (hy : y ∈ ptsIn M.str σ M.off) (hi : y ∈ ptsIn M.str σ ((Lmod M la).U i)) :
    φ.φ i y = φ'.φ i y := by
  obtain ⟨j, rfl⟩ := exists_eq_flagIdx i
  obtain ⟨k, w, t, ht⟩ := exists_frameAt hU hy hi
  exact neg_injective (Real.exp_injective ((h y hy j k w t ht).trans (h' y hy j k w t ht).symm))

theorem add (hU : IsUnf (U (goodOf c σ))) {s : AllWt.Weight Dw} (e : a + b = s) {φa : Weight M.str σ (Lmod M a)}
    {φb : Weight M.str σ (Lmod M b)} {φs : Weight M.str σ (Lmod M s)} (ha : IsHomWeight M U x a φa)
    (hb : IsHomWeight M U x b φb) (hs : IsHomWeight M U x s φs) (hy : y ∈ ptsIn M.str σ M.off) {j : X.F.J}
    (hj : ⊤ ≤ (y.1 ≫ toFlag M) ⁻¹ᵁ X.F.U j) :
    φs.φ (flagIdx M s j) y = φa.φ (flagIdx M a j) y + φb.φ (flagIdx M b j) y := by
  subst e
  obtain ⟨k, w, t, ht⟩ := exists_frameAt (la := a) hU hy (mem_flagIdx.2 hj)
  refine neg_injective (Real.exp_injective ?_)
  rw [neg_add, Real.exp_add, ha y hy j k w t ht, hb y hy j k w t ht, hs y hy j k w t ht, genNorm_add, mul_pow]

theorem zero (hU : IsUnf (U (goodOf c σ))) {φ : Weight M.str σ (Lmod M 0)} (h : IsHomWeight M U x 0 φ)
    (hy : y ∈ ptsIn M.str σ M.off) {j : X.F.J} (hj : ⊤ ≤ (y.1 ≫ toFlag M) ⁻¹ᵁ X.F.U j) : φ.φ (flagIdx M 0 j) y = 0 :=
  left_eq_add.1 (add hU (add_zero 0) h h h hy hj)

example (h : IsHomWeight M U x la φ) (hy : y ∈ ptsIn M.str σ M.off) {j k w}
    (hw : FrameAt X (U (goodOf c σ)) (flagPt M y) j k w 1) (hu : ∀ τ i, ‖FD.dmin (((U (goodOf c σ)).X k).Gm) w.1 τ i‖ = 1) :
    Real.exp (-φ.φ (flagIdx M la j) y) = lieFacZ Dw x (wtOf Dw la 0) ^ 2 := by
  rw [h y hy j k w 1 hw, genNorm, diagChar_one, homFac, FD.Data.nfac]
  simp [hu]

end IsHomWeight

variable (U x) (ω : CanId M)

def nuHom (σ : c.F →+* ℂ) : Measure (CxPts M.str σ) := volMeasure M.K (homWeight M U x (kap Dw) σ) ω.ω

def volHom (σ : c.F →+* ℂ) : ℝ≥0∞ := nuHom U x ω σ Set.univ

def VolGood : Prop := ∀ σ, 0 < volHom U x ω σ ∧ volHom U x ω σ < ⊤

def volLogMax : ℝ := ⨆ σ : c.F →+* ℂ, |Real.log (volHom U x ω σ).toReal|

instance secondCountable_modif (σ : c.F →+* ℂ) : SecondCountableTopology (CxPts M.str σ) :=
  secondCountableTopology_of_isProjOver σ M.proj

variable {U x}

def topForm {s : AllWt.Weight Dw} (e : kap Dw + b = s) :
    H0 M.str (Lmod M s) M.off →ₗ[c.F] H0 M.str (tens M.K.bundle (Lmod M b)) M.off :=
  (((common₀ X Z).pull M.σ).canChart M.K.isLB e).mul ω.ω

variable {ω}

namespace VolGood

theorem exists_eq (_ : VolGood U x ω) : ∃ σ, volLogMax U x ω = |Real.log (volHom U x ω σ).toReal| :=
  (exists_eq_ciSup_of_finite (f := fun σ : c.F →+* ℂ => |Real.log (volHom U x ω σ).toReal|)).imp fun _ => Eq.symm

theorem nonneg (h : VolGood U x ω) : 0 ≤ volLogMax U x ω :=
  let ⟨_, e⟩ := h.exists_eq
  e ▸ abs_nonneg _

end VolGood

example {s : ℝ} (h : ∀ σ, volHom U x ω σ = ENNReal.ofReal (Real.exp (-s))) : volLogMax U x ω = |s| := by
  simp [volLogMax, h, (Real.exp_pos _).le]

end GlobalTheory.CompHS
