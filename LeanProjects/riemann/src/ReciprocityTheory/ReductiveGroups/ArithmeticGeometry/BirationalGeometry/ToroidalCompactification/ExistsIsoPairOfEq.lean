import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WitMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
    (x : Γ(X, U)ˣ) : res h (res h' x) = res (h.trans h') x := by
  have e : X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (h.trans h')).op := by
    rw [← Functor.map_comp]
    rfl
  apply Units.ext
  exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

private theorem res_g_mul_res_g_eq_res_g_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  have key := congrArg (⇑(res hW)) (hL.cocycle i j k)
  simp only [map_mul, res_res_lemma] at key
  exact key

private theorem gm_res_toroidal_compactification {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U)
    (hy : f y ∈ V) (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  have hU : f y ∈ U := h hy
  have e : X.presheaf.map (homOfLE h).op ≫ f.app V ≫ Y.presheaf.germ (f ⁻¹ᵁ V) y hy =
      f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hU := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm
  rw [dif_pos hy, dif_pos hU]
  apply Units.ext
  exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

private theorem isGen_g_iso_self_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    (⟨fun p : L.ι × L.ι => L.g p.1 p.2⟩ : LB.Iso L L).IsGen := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  have h₀ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ := inf_le_left
  have h₁ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₂ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂ := inf_le_right
  have h₃ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  have h₄ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂ :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have c₁ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ q₁ q₂ h₁ h₂ h₃
  have c₂ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ p₂ q₂ h₀ h₄ h₃
  have key : res h₀ (L.g p₁ p₂) =
      res h₁ (L.g p₁ q₁) * (res h₄ (L.g p₂ q₂))⁻¹ * res h₂ (L.g q₁ q₂) := by
    rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]
  exact key

private theorem gm_g_mul_gm_g_swap_eq_one_of_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y)
    {i j : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j) :
    gm f y (L.U j ⊓ L.U i) (L.g j i) * gm f y (L.U i ⊓ L.U j) (L.g i j) = 1 := by
  have hW : f y ∈ L.U j ⊓ L.U i := ⟨hj, hi⟩
  have h₂ : L.U j ⊓ L.U i ≤ L.U i ⊓ L.U j := le_of_eq (inf_comm _ _)
  have h₃ : L.U j ⊓ L.U i ≤ L.U j ⊓ L.U j := le_inf inf_le_left inf_le_left
  rw [← gm_res_toroidal_compactification f y h₂ hW (L.g i j), ← gm_res_toroidal_compactification f y (le_refl (L.U j ⊓ L.U i)) hW (L.g j i),
    ← map_mul (gm f y (L.U j ⊓ L.U i)), res_g_mul_res_g_eq_res_g_of_isLB hL j i j (le_refl _) h₂ h₃,
    ← res_res_lemma (inf_le_left : L.U j ⊓ L.U i ≤ L.U j) (le_inf le_rfl le_rfl : L.U j ≤ L.U j ⊓ L.U j),
    hL.g_self]
  simp only [map_one]

theorem exists_iso_pair_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}
    (h : L₁ = L₂) :
    ∃ (w : LB.Iso L₁.L L₂.L) (w' : LB.Iso L₂.L L₁.L), w.IsGen ∧ w'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig ∧
      LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig L₁.rig ∧
      ∀ {Y : Scheme.{0}} (f : Y ⟶ G.left) (y : Y) (i : L₁.L.ι) (j : L₂.L.ι), f y ∈ L₁.L.U i → f y ∈ L₂.L.U j →
        gv w f y j i * gv w' f y i j = 1 := by
  cases h
  refine ⟨⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩, ⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩,
    isGen_g_iso_self_of_isLB L₁.isLB, isGen_g_iso_self_of_isLB L₁.isLB, ?_, ?_, ?_⟩
  · intro p
    exact L₁.rigGen p.1 p.2
  · intro p
    exact L₁.rigGen p.1 p.2
  · intro Y f y i j hi hj
    exact gm_g_mul_gm_g_swap_eq_one_of_isLB L₁.isLB f y hi hj

section Lev

open ReciprocityTheory.ChartRestriction.G.Out

def UniqLev {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (U' : Unif I D' A' G) (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (wL : LB.Iso U'.LG.L U.LG.L) : Prop :=
  ∀ n : ℕ,
    (U'.gt n).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
      (U.gt n).pG.left ∧
    (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
        D'.toPre.Oφ ((U'.gt n).pG) x k ≫ hD.e.hom.left ≫
            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
          𝟙 _ ≫ D.toPre.Oφ ((U.gt n).pG) (hD.xe x) k,
      LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt n).t x)
        (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫
                          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (𝟙 _) _
          Oinvε _ hψ ((U.gt n).t (hD.xe x)))) ∧
    ∀ (jM : PUnit → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jL : U.LG.L.ι),
      res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_left) :
          (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
              pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM') ⊓
            (LB.div (D'.toPre.P.L.pull (U'.gt n).pG.left) (U'.LG.L.pull (fstG I n G).left)).U
              (fun _ => jM', fun _ => jL') ⊓
            (LB.div (D.toPre.P.L.pull (U.gt n).pG.left) (U.LG.L.pull (fstG I n G).left)).U
              (jM, fun _ => jL) ⊓
            (fstG I n G).left ⁻¹ᵁ (LB.div U.LG.L U'.LG.L).U (jL, jL') ≤
          (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
              pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM'))
        (pullU (U'.gt n).pG.left _ (hD.w.s (jM, jM'))) *
      res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_right))
        ((U'.w n).s (fun _ => jM', fun _ => jL')) =
      res (X := (thickObj R I n G).left) (inf_le_left.trans inf_le_right)
        ((U.w n).s (jM, fun _ => jL)) *
      res (X := (thickObj R I n G).left) inf_le_right
        (pullU (fstG I n G).left _ (wL.s (jL, jL')))

end Lev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

abbrev ArcWit.CoreOut {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF} {Y : Model Xo c β}
    {χ : Sp (PowerSeries k) ⟶ Y.X}
    (W W' : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (ψ : W.t.G ≅ W'.t.G) : Prop :=
    ∃ (bc : W.t.G ≅ (Over.pullback (Out.specOf (RingHom.id (PowerSeries k)))).obj W'.t.G)
      (D'' : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X}))
      (hD₁ : Out.IsPullDeg (RingHom.id _) W.P.D.toPre D''.toPre)
      (hD₂ : Out.IsPullDeg (RingHom.id _) W'.P.D.toPre D''.toPre)
      (U'' : Out.Unif (Ideal.span {PowerSeries.X}) D'' W'.P.A W.t.G) (wL₀ : LB.Iso U''.LG.L W.P.U.LG.L)
      (wI : LB.Iso W.P.U.LG.L U''.LG.L)
      (w₁ : LB.Iso D''.toPre.P.L (a.D₀.P.L.pull ((hD₁.e.hom.left ≫
        pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id _))) ≫ W.φ)))
      (w₂ : LB.Iso D''.toPre.P.L (a.D₀.P.L.pull ((hD₂.e.hom.left ≫
        pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id _))) ≫ W'.φ))),
      bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id _)) = ψ.hom.left ∧
      UniqLev W.P.U U'' hD₁ wL₀ ∧ Out.IsPullUnif (RingHom.id _) hD₂ bc W'.P.U U'' ∧ wI.IsGen ∧
      LB.Gen.Maps (LB.linCombIso wI (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig U''.LG.rig ∧
      (∀ {Z : Scheme.{0}} (f : Z ⟶ W.t.G.left) (z : Z) (i : W.P.U.LG.L.ι) (j : U''.LG.L.ι), f z ∈ W.P.U.LG.L.U i →
        f z ∈ U''.LG.L.U j → gv wL₀ f z i j * gv wI f z j i = 1) ∧
      (hD₁.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id _))) ≫ W.φ =
        (hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id _))) ≫ W'.φ ∧
      (∀ x, hD₁.xe.symm (W.e x) = hD₂.xe.symm (W'.e x)) ∧ Tri W.w hD₁.w w₁ ∧ Tri W'.w hD₂.w w₂ ∧ HEq w₁ w₂

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
