import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def idIso {Y : Scheme.{0}} (M : LB Y) : LB.Iso M M := ⟨fun p => M.g p.1 p.2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

section Gx

variable {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X)

def gxLift {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    Z ⟶ Gx x :=
  (lift (Over.homMk a rfl : Over.mk (a ≫ x) ⟶ Over.mk x) (Over.homMk b w : Over.mk (a ≫ x) ⟶ Xo.univ.t.G)).left

theorem gxLift_fst {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    gxLift x a b w ≫ (fst (Over.mk x) Xo.univ.t.G).left = a := by
  rw [gxLift, ← Over.comp_left, lift_fst] <;> rfl

theorem gxLift_snd {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    gxLift x a b w ≫ (snd (Over.mk x) Xo.univ.t.G).left = b := by
  rw [gxLift, ← Over.comp_left, lift_snd] <;> rfl

theorem gx_ext {Z : Scheme.{0}} (p q : Z ⟶ Gx x)
    (h1 : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h2 : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left) : p = q := by
  have e : (Over.mk x ⊗ Xo.univ.t.G).hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  have hw : q ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    rw [e, ← Category.assoc, ← h1, Category.assoc]
  let P : Over.mk (p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk p rfl
  let Q : Over.mk (p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk q hw
  have hPQ : P = Q := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa [P, Q] using h1
    · ext
      simpa [P, Q] using h2
  have := congrArg (fun f => f.left) hPQ
  simpa [P, Q] using this

theorem gx_w : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x := by
  exact (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm

def gxU : pullback Xo.univ.t.G.hom x ⟶ Gx x := gxLift x (pullback.snd _ _) (pullback.fst _ _) pullback.condition

def gxV : Gx x ⟶ pullback Xo.univ.t.G.hom x :=
  pullback.lift (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (gx_w x)

theorem gxU_fst : gxU x ≫ (fst (Over.mk x) Xo.univ.t.G).left = pullback.snd _ _ := by
  exact gxLift_fst x _ _ _
theorem gxU_snd : gxU x ≫ (snd (Over.mk x) Xo.univ.t.G).left = pullback.fst _ _ := by
  exact gxLift_snd x _ _ _
theorem gxV_fst : gxV x ≫ pullback.fst _ _ = (snd (Over.mk x) Xo.univ.t.G).left := by
  exact pullback.lift_fst _ _ _
theorem gxV_snd : gxV x ≫ pullback.snd _ _ = (fst (Over.mk x) Xo.univ.t.G).left := by
  exact pullback.lift_snd _ _ _

theorem gxU_gxV : gxU x ≫ gxV x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, gxV_fst, gxU_snd, Category.id_comp]
  · rw [Category.assoc, gxV_snd, gxU_fst, Category.id_comp]

theorem gxV_gxU : gxV x ≫ gxU x = 𝟙 _ := by
  apply gx_ext x
  · rw [Category.assoc, gxU_fst, gxV_snd, Category.id_comp]
  · rw [Category.assoc, gxU_snd, gxV_fst, Category.id_comp]

theorem gs_scal (a : S) (i : Fin 1 → Xo.univ.t.PP.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Gx x) (z : Z)
    (hz : r z ∈ (PPx x).U i) :
    gs r z ((PPx x).U i) (scal x a i) = cst (r ≫ (fst (Over.mk x) Xo.univ.t.G).left) z a := by
  exact (gs_res r z le_top hz _).trans (gs_pull r _ z ⊤ trivial _)

theorem scal_eq_iff (s t : LB.Sec (PPx x)) (a : S) :
    (∀ i, s.f i = scal x a i * t.f i) ↔ ∀ i, ∀ y ∈ (PPx x).U i,
      gs (𝟙 _) y _ (s.f i) = cst (fst (Over.mk x) Xo.univ.t.G).left y a * gs (𝟙 _) y _ (t.f i) := by
  constructor
  · intro h i y hy
    rw [h i, gs_mul (𝟙 _) y _ hy, gs_scal x a i (𝟙 _) y hy, Category.id_comp]
  · intro h i
    apply fn_ext
    intro y hy
    rw [gs_mul (𝟙 _) y _ hy, gs_scal x a i (𝟙 _) y hy, Category.id_comp]
    exact h i y hy

end Gx

section BC

variable {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem bcU_w : (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ≫ pullback.fst Xo.univ.t.G.hom x) ≫
    Xo.univ.t.G.hom = pullback.snd (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ≫ spMap ψ ≫ x := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]

def bcU : pullback (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ⟶ Gx (spMap ψ ≫ x) :=
  gxLift (spMap ψ ≫ x) (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst _ _) (bcU_w ψ x)

theorem bcV_w : (bcPm ψ x ≫ gxV x) ≫ pullback.snd Xo.univ.t.G.hom x =
    (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Category.assoc, gxV_snd, bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left] <;> rfl

def bcV : Gx (spMap ψ ≫ x) ⟶ pullback (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) :=
  pullback.lift (bcPm ψ x ≫ gxV x) (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left (bcV_w ψ x)

theorem bcU_fst : bcU ψ x ≫ (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left = pullback.snd _ _ := by
  exact gxLift_fst _ _ _ _
theorem bcU_snd : bcU ψ x ≫ (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left =
    pullback.fst _ _ ≫ pullback.fst Xo.univ.t.G.hom x := by
  exact gxLift_snd _ _ _ _
theorem bcV_fst : bcV ψ x ≫ pullback.fst _ _ = bcPm ψ x ≫ gxV x := by
  exact pullback.lift_fst _ _ _
theorem bcV_snd : bcV ψ x ≫ pullback.snd _ _ = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  exact pullback.lift_snd _ _ _

theorem bcV_snd' : bcV ψ x ≫ pullback.fst _ _ ≫ pullback.fst Xo.univ.t.G.hom x =
    (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  have hbs : bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left
      = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
    rw [bcPm, ← Over.comp_left, whiskerRight_snd]
  rw [← Category.assoc, bcV_fst, Category.assoc, gxV_fst, hbs]

theorem bcV_bcU : bcV ψ x ≫ bcU ψ x = 𝟙 _ := by
  apply gx_ext (spMap ψ ≫ x)
  · rw [Category.assoc, bcU_fst, bcV_snd, Category.id_comp]
  · rw [Category.assoc, bcU_snd, bcV_snd', Category.id_comp]

theorem bcU_bcPm : bcU ψ x ≫ bcPm ψ x = pullback.fst _ _ ≫ gxU x := by
  have hbs : bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left
      = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
    rw [bcPm, ← Over.comp_left, whiskerRight_snd]
  have hbf : bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left
      = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
    rw [bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left] <;> rfl
  apply gx_ext x
  · rw [Category.assoc, hbf, ← Category.assoc, bcU_fst, Category.assoc, gxU_fst, pullback.condition]
  · rw [Category.assoc, hbs, bcU_snd, Category.assoc, gxU_snd]

theorem bcU_bcV : bcU ψ x ≫ bcV ψ x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcV_fst, ← Category.assoc, bcU_bcPm, Category.assoc, gxU_gxV,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, bcV_snd, bcU_fst, Category.id_comp]

theorem bcV_gxU : bcV ψ x ≫ pullback.fst _ _ ≫ gxU x = bcPm ψ x := by
  rw [← Category.assoc, bcV_fst, Category.assoc, gxV_gxU, Category.comp_id]

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
