import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegSymm

section Bundle

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem base_cancel {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) (x : X) : F (G x) = x := by
  have := congrArg (fun f : X ⟶ X => f x) h
  exact this

theorem le_rev {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) (p : (LB.div (L'.pull G) L).ι) :
    (LB.div (L'.pull G) L).U p ≤ G ⁻¹ᵁ ((L.pull F).U (fun _ => p.2) ⊓ L'.U (p.1 PUnit.unit)) :=
  fun x hx => ⟨mem_pull.2 (by rw [base_cancel h]; exact hx.2), mem_pull.1 hx.1⟩

def revIso (w : LB.Iso L' (L.pull F)) (G : X ⟶ X') (h : G ≫ F = 𝟙 X) : LB.Iso L (L'.pull G) :=
  ⟨fun p => (res (le_rev h p) (pullU G _ (w.s (fun _ => p.2, p.1 PUnit.unit))))⁻¹⟩

theorem gw_revIso (w : LB.Iso L' (L.pull F)) {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z)
    (j' : L'.ι) (j : L.ι) (h₁ : G (f z) ∈ L'.U j') (h₂ : f z ∈ L.U j) :
    gw (revIso w G h) f z j' j = (gw w (f ≫ G) z j j')⁻¹ := by
  have hm : f z ∈ (LB.div (L'.pull G) L).U (fun _ => j', j) := ⟨mem_pull.2 h₁, h₂⟩
  exact (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z _ hm _).trans (gm_pull f G z _ (le_rev h _ hm) _)))

theorem revIso_isGen (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) :
    (revIso w G h).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have hp := (isGen_iff w).1 hw Z (f ≫ G) z k k' j j' (show F (G (f z)) ∈ _ by rw [base_cancel h]; exact hk)
    (show F (G (f z)) ∈ _ by rw [base_cancel h]; exact hk') hj hj'
  have e : (f ≫ G) ≫ F = f := by rw [Category.assoc, h, Category.comp_id]
  rw [e] at hp
  rw [gw_revIso w h f z j k hj hk, gw_revIso w h f z j' k' hj' hk', hp]
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem carriesAt_iff (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    CarriesAt L L' F w p' p hp n a b ↔ ∀ (y : Y) (j : L.ι) (j' : L'.ι), F (p' y) ∈ L.U j → p' y ∈ L'.U j' →
      gm (𝟙 Y) y _ (b.s (fun _ => j)) = gw w p' y j j' ^ n * gm (𝟙 Y) y _ (a.s (fun _ => j')) := by
  constructor
  · intro H y j j' h₁ h₂
    have hm : y ∈ p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') := ⟨mem_pull.2 h₁, h₂⟩
    have e := congrArg (gm (𝟙 Y) y _) (H j j')
    refine (gm_res _ y _ hm _).symm.trans (e.trans ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))
    exact (gm_pull _ _ y _ hm _).trans (by rw [Category.id_comp]; rfl)
  · intro H j j'
    apply unit_ext
    intro y hm
    refine (gm_res _ y _ hm _).trans ((H y j j' (mem_pull.1 hm.1) hm.2).trans ?_)
    refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _)))
    exact (gm_pull _ _ y _ hm _).trans (by rw [Category.id_comp]; rfl)

theorem carriesAt_rev (w : LB.Iso L' (L.pull F)) {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) {p' : Y ⟶ X'} {p : Y ⟶ X}
    (hp : p' ≫ F = p) (hq : p ≫ G = p') (n : ℤ)
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    (H : CarriesAt L L' F w p' p hp n a b) : CarriesAt L' L G (revIso w G h) p p' hq n b a := by
  rw [carriesAt_iff] at H ⊢
  intro y j' j h₁ h₂
  have e₁ : p' y = G (p y) := congrArg (fun f : Y ⟶ X' => f y) hq.symm
  have e₂ : F (p' y) = p y := congrArg (fun f : Y ⟶ X => f y) hp
  have := H y j j' (by rw [e₂]; exact h₂) (by rw [e₁]; exact h₁)
  rw [gw_revIso w h p y j' j h₁ h₂, hq, this, inv_zpow, inv_mul_cancel_left]

end Bundle

section Grp

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem specOf_id' : GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) = 𝟙 _ := Spec.map_id _

instance isIso_F (p : PullIdent (RingHom.id R) D D') : IsIso p.F := by
  have : IsIso (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) := by rw [specOf_id']; infer_instance
  exact MorphismProperty.of_isPullback (P := .isomorphisms _) p.cart.flip this

abbrev Finv (p : PullIdent (RingHom.id R) D D') : D.P.A.left ⟶ D'.P.A.left := inv p.F

theorem Finv_F (p : PullIdent (RingHom.id R) D D') : Finv p ≫ p.F = 𝟙 _ := IsIso.inv_hom_id _

theorem cart' (p : PullIdent (RingHom.id R) D D') :
    IsPullback (Finv p) D.P.A.hom D'.P.A.hom (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) := by
  have : IsIso (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) := by rw [specOf_id']; infer_instance
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  have w := p.cart.w
  rw [specOf_id', Category.comp_id] at w
  rw [IsIso.inv_comp_eq, specOf_id', Category.comp_id, w]

theorem F_one' (p : PullIdent (RingHom.id R) D D') :
    eSec D.P.A ≫ Finv p = GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D'.P.A := by
  have e := p.F_one
  rw [specOf_id', Category.id_comp] at e
  rw [specOf_id', Category.id_comp, IsIso.comp_inv_eq, e]

theorem F_mul' (p : PullIdent (RingHom.id R) D D') : (μ[D.P.A]).left ≫ Finv p =
    pullback.map D.P.A.hom D.P.A.hom D'.P.A.hom D'.P.A.hom (Finv p) (Finv p) (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R))
      (cart' p).w.symm (cart' p).w.symm ≫ (μ[D'.P.A]).left := by
  rw [IsIso.comp_inv_eq, Category.assoc, p.F_mul, ← Category.assoc]
  have key : pullback.map D.P.A.hom D.P.A.hom D'.P.A.hom D'.P.A.hom (Finv p) (Finv p)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (cart' p).w.symm (cart' p).w.symm ≫
      pullback.map D'.P.A.hom D'.P.A.hom D.P.A.hom D.P.A.hom p.F p.F (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R))
        p.cart.w.symm p.cart.w.symm = 𝟙 _ := by
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, Finv_F, Category.comp_id]
    · erw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, Finv_F, Category.comp_id]
  rw [key]
  exact (Category.id_comp _).symm

theorem c_eq' (p : PullIdent (RingHom.id R) D D') (χ : D.X) :
    (D.c χ).left ≫ Finv p = GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ (D'.c (p.xe.symm χ)).left := by
  have e := p.c_eq (p.xe.symm χ)
  rw [AddEquiv.apply_symm_apply, specOf_id', Category.id_comp] at e
  rw [specOf_id', Category.id_comp, IsIso.comp_inv_eq, e]

abbrev wInv (p : PullIdent (RingHom.id R) D D') : LB.Iso D.P.L (D'.P.L.pull (Finv p)) :=
  revIso p.w (Finv p) (Finv_F p)

theorem wInv_isGen (p : PullIdent (RingHom.id R) D D') : (wInv p).IsGen := revIso_isGen p.w p.w_gen _

theorem w_rig' (p : PullIdent (RingHom.id R) D D') :
    CarriesAt D'.P.L D.P.L (Finv p) (wInv p) (eSec D.P.A) (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D'.P.A)
      (F_one' p) 1 D.rig (LB.pullGen D'.P.L _ _ D'.rig (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R))) := by
  have es : GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A = eSec D.P.A := by
    rw [specOf_id', Category.id_comp]
  have es' : GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D'.P.A = eSec D.P.A ≫ Finv p := (F_one' p).symm
  have hq : (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A) ≫ Finv p = eSec D'.P.A := by
    rw [es, F_one' p, specOf_id', Category.id_comp]
  have H := carriesAt_rev p.w (Finv_F p) p.F_one hq 1 p.w_rig
  have h1 : 𝟙 (Spec (CommRingCat.of R)) ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [specOf_id', Category.id_comp]
  rw [carriesAt_iff] at H ⊢
  intro y j j' h₁ h₂
  have m₁ : Finv p ((GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A) y) ∈ D'.P.L.U j := by rw [es]; exact h₁
  have m₂ : (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A) y ∈ D.P.L.U j' := by rw [es]; exact h₂
  have e := H y j j' m₁ m₂
  have a₁ := gm_pullGen D'.P.L _ _ D'.rig (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (𝟙 (Spec (CommRingCat.of R))) y
    (fun _ => j) (Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ D'.P.L.U j) es').mpr h₁)
  have a₂ := gm_pullGen D.P.L _ _ D.rig (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (𝟙 (Spec (CommRingCat.of R))) y
    (fun _ => j') (Set.mem_iInter.2 fun _ => m₂)
  rw [h1] at a₁ a₂
  exact a₁.trans (e.trans (congrArg₂ (· * ·) (by rw [es]) a₂))

end Grp

end GlobalTheory.PullDegSymm
