import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem cross_resG_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V W : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (s : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom s) = (f.appLE U W (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem cross_resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    resG X h2 (resG X h1 s) = resG X (h2.trans h1) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

theorem cross_resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) : resG X h s = s := by
  change (X.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cross_appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (s : Γ(Y, U')) :
    (f.appLE U V e).hom (resG Y h s) = (f.appLE U' V (e.trans fun _ hx => h hx)).hom s := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem cross_ratio_val {k Ω : Type} [CommRing k] [Field Ω] {n : ℕ} {x : Sp Ω ⟶ PSpace k n}
    {c : Fin (n + 1) → Ω} (hc : PCrd x c) {U : (PSpace k n).Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) {a : Fin (n + 1)}
    (ha : U ≤ chart k n a) :
    c a ≠ 0 ∧ ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b * (c a)⁻¹) := by
  obtain ⟨τ, -, H⟩ := hc
  have h1 : ((O1 k n).pull x).U (fun _ => a) ≤ x ⁻¹ᵁ (O1 k n).U a :=
    LB.wchart_le (O1 k n) (fun _ => x) (fun _ => a) PUnit.unit
  have h2 : ⊤ ≤ ((O1 k n).pull x).U (fun _ => a) :=
    fun y hy => Set.mem_iInter.2 fun _ => ha (hU hy)
  set t : Γ(Sp Ω, ⊤) := resG _ h2 (τ.s (fun _ => a)).val with ht
  have key : ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b) * t := by
    intro b
    have e := congrArg (resG _ h2) (H b (fun _ => a) h1)
    rw [map_mul, cross_resG_appLE] at e
    have e2 : ratioOn U a ha b = resG _ ha (ratio k n a b) := rfl
    rw [e2, cross_appLE_resG]
    refine e.trans (congrArg (· * t) ?_)
    exact (cross_resG_resG _ _ _).trans (cross_resG_self _ _)
  have ka := key a
  rw [ratioOn_self, map_one] at ka
  have hne : c a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ka
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ka
    rw [map_one, map_zero] at this
    exact one_ne_zero (α := Ω) this
  refine ⟨hne, fun b => ?_⟩
  rw [key, map_mul]
  congr 1
  have : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) = 1 := by
    rw [← map_mul]
    exact (congrArg _ (inv_mul_cancel₀ hne)).trans (map_one _)
  calc t = (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) * t) := by rw [← _root_.mul_assoc, this, _root_.one_mul]
    _ = _ := by rw [← ka, _root_.mul_one]

theorem cross_pull_base {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    {N : S.Opens} (hN : ⊤ ≤ ξ ⁻¹ᵁ N) {V : G.left.Opens} (hV : V ≤ G.hom ⁻¹ᵁ N) {W : (Over.mk ξ ⊗ G).left.Opens}
    (hW : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ V) (r : Γ(S, N)) :
    ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) := by
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  have e1 : ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      (G.hom.appLE N V hV ≫ (snd (Over.mk ξ) G).left.appLE V W hW).hom r := rfl
  have e2 : liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) =
      (ξ.appLE N ⊤ hN ≫ (fst (Over.mk ξ) G).left.appLE ⊤ W le_top).hom r := rfl
  rw [e1, e2, Scheme.Hom.appLE_comp_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  simp only [e]

theorem cross_ratio_sections : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  intro k Ω _ _ _ M G _ L n c h v hc huniq a b sa sb ha hb i
  by_cases hne : ((h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · have hbot : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) = ⊥ :=
      eq_bot_iff.2 fun y hy => hne ⟨_, hy.2⟩
    have : Subsingleton Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b))) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨ha1, ha2⟩ := ha (hne.mono fun _ hx => hx.1)
  obtain ⟨hb1, hb2⟩ := hb (hne.mono fun _ hx => hx.2)
  have htop := M.top_le_preimage_pt hne
  have hr : Set.range M.pt ⊆ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) :=
    (top_le_preimage_iff _ _).1 htop
  have htop' : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (chart k n a ⊓ chart k n b) := htop
  obtain ⟨hca, hra⟩ := cross_ratio_val hc htop' inf_le_left
  obtain ⟨hcb, -⟩ := cross_ratio_val hc htop' inf_le_right
  let s₂ : LocSec G L (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) := fun i =>
    resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i)
  have g₂ : GenIs M.pt s₂ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v) := by
    refine ⟨hr, funext fun j => ?_⟩
    have e3 := congrFun hb2 j
    simp only [genPull, s₂] at e3 ⊢
    rw [map_mul, cross_pull_base G M.pt htop]
    refine (congrArg (_ * ·) ((cross_appLE_resG _ _ _ _).trans e3)).trans ?_
    have e4 : (M.pt.appLE _ ⊤ htop).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b)) =
        ((M.pt ≫ h).appLE _ ⊤ htop').hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b) := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e4, hra]
    change liftHom G _ _ * (liftHom G _ _ * v.1 j) = liftHom G _ _ * v.1 j
    rw [← _root_.mul_assoc, ← map_mul]
    congr 2
    erw [← map_mul]
    congr 1
    change c b * (c a)⁻¹ * (c b)⁻¹ = (c a)⁻¹
    field_simp
  have e := congrArg (resG _ (fun _ hx => ⟨hx.1, hx.2.1, hx.2⟩ :
    L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
      L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a ⊓ h ⁻¹ᵁ (chart k n a ⊓ chart k n b))))
    (huniq _ _ sa s₂ _ ⟨ha1, ha2⟩ g₂ i)
  exact (cross_resG_resG _ _ _).symm.trans (e.trans ((cross_resG_resG _ _ _).trans (cross_resG_self _ _)))

end GlobalTheory.UMin.ThBdl
