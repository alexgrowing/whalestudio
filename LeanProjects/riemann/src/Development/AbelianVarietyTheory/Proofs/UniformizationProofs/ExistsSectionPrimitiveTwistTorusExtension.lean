import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtSec

theorem stalkMap_injective {X Z : Scheme.{0}} (r : Z ⟶ X) [Flat r] (z : Z) :
    Function.Injective (r.stalkMap z).hom :=
  (injective_iff_map_eq_zero _).2 fun b hb =>
    zero_dvd_iff.1 (dvd_descend r z (a := 0) (b := b) (by rw [hb, map_zero]))

theorem exists_gs_ne_zero {X : Scheme.{0}} {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) :
    ∃ x ∈ V, gs (𝟙 X) x V a ≠ 0 := by
  by_contra h
  refine ha (fn_ext fun x hx => ?_)
  rw [LBGerm.gs_zero _ x V hx]
  exact by_contra fun k => h ⟨x, hx, k⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem isWt_sub {i : splitTorus S X ⟶ G} {V : G.left.Opens} {u v : Γ(G.left, V)} {χ : X} (hu : IsWt i V u χ)
    (hv : IsWt i V v χ) : IsWt i V (u - v) χ :=
  fun Z t g h₁ h₂ => by rw [map_sub, map_sub, hu Z t g h₁ h₂, hv Z t g h₁ h₂, mul_sub]

variable (Q : TQ G X)

theorem isWt_app (V : Q.B.left.Opens) (c : Γ(Q.B.left, V)) : IsWt Q.i _ ((Q.q.left.app V).hom c) 0 := by
  intro Z t g k₁ k₂
  have e : ∀ (r : Z.left ⟶ G.left) (k : ⊤ ≤ r ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V)),
      (r.appLE _ ⊤ k).hom ((Q.q.left.app V).hom c) = ((r ≫ Q.q.left).appLE V ⊤ k).hom c := fun r k =>
    (congrArg (fun q => q.hom c) (Scheme.Hom.comp_appLE r Q.q.left V ⊤ k)).symm
  have e' : ∀ (r r' : Z.left ⟶ Q.B.left) (_ : r = r') (k : ⊤ ≤ r ⁻¹ᵁ V) (k' : ⊤ ≤ r' ⁻¹ᵁ V),
      (r.appLE V ⊤ k).hom c = (r'.appLE V ⊤ k').hom c := by
    rintro r _ rfl k k'; rfl
  rw [e, e, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  have k : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, WtBundle.act_comp]
  exact e' _ _ k _ _

theorem exists_app_of_isWt (V : Q.B.left.Opens) (a : Γ(G.left, Q.q.left ⁻¹ᵁ V)) (h : IsWt Q.i _ a 0) :
    ∃ c, (Q.q.left.app V).hom c = a := by
  have := Q.q_affine
  refine (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V).2.2 a fun Z t g k₁ k₂ => ?_
  rw [h Z t g k₁ k₂, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]

theorem graded (V : Q.B.left.Opens) (hV : IsAffineOpen V) :
    (∀ u : Γ(G.left, Q.q.left ⁻¹ᵁ V), ∃ a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V),
      (∀ χ, IsWt Q.i _ (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
    ∀ a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V), (∀ χ, IsWt Q.i _ (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0 := by
  have := Q.q_affine
  refine GlobalTheory.functions_graded_by_weights S G X Q.i Q.i_hom _ (hV.preimage _) ?_
  have e := congrArg (fun q => q.left) (WtBundle.act_comp Q (fst (splitTorus _ X) G) (snd _ G))
  simp only [Over.comp_left] at e
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, e]

theorem comp_compat {V V' U : Q.B.left.Opens} (g : Γ(Q.B.left, U)) (hU : V ⊓ V' ≤ U)
    (a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V)) (a' : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V'))
    (ha : ∀ χ, IsWt Q.i _ (a χ) χ) (ha' : ∀ χ, IsWt Q.i _ (a' χ) χ)
    (h : ∀ x, Q.q.left x ∈ V → Q.q.left x ∈ V' → gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V) (a.sum fun _ x => x) =
      gs Q.q.left x U g * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V') (a'.sum fun _ x => x))
    (χ : X) (x : G.left) (hx : Q.q.left x ∈ V) (hx' : Q.q.left x ∈ V') :
    gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V) (a χ) = gs Q.q.left x U g * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V') (a' χ) := by
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (show Q.q.left x ∈ V ⊓ V' from ⟨hx, hx'⟩)
  have hle : W ≤ V ⊓ V' := hle
  have l₁ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ V := fun _ k => (hle k).1
  have l₂ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ V' := fun _ k => (hle k).2
  have l₃ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ U := fun _ k => hU (hle k)
  let g' : Γ(G.left, Q.q.left ⁻¹ᵁ W) := (G.left.presheaf.map (homOfLE l₃).op).hom ((Q.q.left.app U).hom g)
  let r₁ : Γ(G.left, Q.q.left ⁻¹ᵁ V) →+ Γ(G.left, Q.q.left ⁻¹ᵁ W) :=
    (G.left.presheaf.map (homOfLE l₁).op).hom.toAddMonoidHom
  let r₂ : Γ(G.left, Q.q.left ⁻¹ᵁ V') →+ Γ(G.left, Q.q.left ⁻¹ᵁ W) :=
    (AddMonoidHom.mulLeft g').comp (G.left.presheaf.map (homOfLE l₂).op).hom.toAddMonoidHom
  have v : ∀ y, Q.q.left y ∈ W → ∀ b b', gs (𝟙 _) y (Q.q.left ⁻¹ᵁ W) (r₁ b - r₂ b') =
      gs (𝟙 _) y (Q.q.left ⁻¹ᵁ V) b - gs Q.q.left y U g * gs (𝟙 _) y (Q.q.left ⁻¹ᵁ V') b' := fun y hy b b' => by
    refine (LBGerm.gs_sub (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy _ _).trans (congrArg₂ (· - ·) (gs_res (𝟙 _) y l₁ hy _)
      ((gs_mul (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy g' _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y l₃ hy _).trans ?_)
        (gs_res (𝟙 _) y l₂ hy _))))
    rw [gs_pull (𝟙 _) Q.q.left y U (l₃ hy), Category.id_comp]
  have s : ∀ {A B : Type} [AddCommGroup A] [AddCommGroup B] (r : A →+ B) (b : X →₀ A),
      ((b.mapRange r (map_zero r)).sum fun _ x => x) = r (b.sum fun _ x => x) := fun r b => by
    rw [Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum]
  have z := (graded Q W hW).2 (a.mapRange r₁ (map_zero r₁) - a'.mapRange r₂ (map_zero r₂))
    (fun ψ => isWt_sub ((ha ψ).res l₁) (by
      have := ((isWt_app Q U g).res l₃).mul ((ha' ψ).res l₂)
      rwa [zero_add] at this)) (by
      rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), s, s]
      refine fn_ext fun y hy => ?_
      rw [v y hy, h y (l₁ hy) (l₂ hy), sub_self, LBGerm.gs_zero (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy])
  have z' : r₁ (a χ) - r₂ (a' χ) = 0 := DFunLike.congr_fun z χ
  rw [← sub_eq_zero, ← v x hxW, z', LBGerm.gs_zero (𝟙 _) x (Q.q.left ⁻¹ᵁ W) hxW]

theorem exists_component (M : LB Q.B.left) (hM : M.IsLB) (s : LB.Sec (M.pull Q.q.left)) (hs : ∃ j, s.f j ≠ 0) :
    ∃ (χ : X) (α : Type) (V : α → Q.B.left.Opens) (i : α → M.ι) (f : ∀ p, Γ(G.left, Q.q.left ⁻¹ᵁ V p)),
      (∀ p, V p ≤ M.U (i p)) ∧ (∀ y, ∃ p, y ∈ V p) ∧ (∀ p, IsWt Q.i _ (f p) χ) ∧ (∃ p, f p ≠ 0) ∧
      ∀ p p' x, Q.q.left x ∈ V p → Q.q.left x ∈ V p' → gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p) (f p) =
        (gm Q.q.left x (M.U (i p) ⊓ M.U (i p')) (M.g (i p) (i p'))).val * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p') (f p') := by
  let α := {p : Q.B.left.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2}
  have le : ∀ p : α, Q.q.left ⁻¹ᵁ p.1.1 ≤ (M.pull Q.q.left).U fun _ => p.1.2 := fun p _ k => mem_pull.2 (p.2.2 k)
  choose a ha hsum using fun p : α => (graded Q p.1.1 p.2.1).1
    ((G.left.presheaf.map (homOfLE (le p)).op).hom (s.f fun _ => p.1.2))
  have cov : ∀ y j, y ∈ M.U j → ∃ p : α, y ∈ p.1.1 ∧ p.1.2 = j := fun y j hj => by
    obtain ⟨W, hW, hy, hle⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨⟨(W, j), hW, hle⟩, hy, rfl⟩
  obtain ⟨J, hJ⟩ := hs
  obtain ⟨x, hx, hx0⟩ := exists_gs_ne_zero hJ
  obtain ⟨p₀, hp, e⟩ := cov _ _ (mem_pull.1 hx)
  obtain rfl : (fun _ => p₀.1.2) = J := funext fun _ => e
  have n : a p₀ ≠ 0 := fun k => hx0 (by
    rw [← gs_res (𝟙 _) x (le p₀) hp, hsum, k, Finsupp.sum_zero_index,
      LBGerm.gs_zero (𝟙 _) x (Q.q.left ⁻¹ᵁ p₀.1.1) hp])
  obtain ⟨χ, hχ⟩ := Finsupp.ne_iff.1 n
  refine ⟨χ, α, fun p => p.1.1, fun p => p.1.2, fun p => a p χ, fun p => p.2.2, fun y => ?_, fun p => ha p χ,
    ⟨p₀, hχ⟩, fun p p' x hx hx' => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hM y
    exact (cov y j hj).imp fun _ k => k.1
  · rw [← gs_unit Q.q.left x (M.U p.1.2 ⊓ M.U p'.1.2) ⟨p.2.2 hx, p'.2.2 hx'⟩]
    refine comp_compat Q _ (inf_le_inf p.2.2 p'.2.2) _ _ (ha p) (ha p') (fun y hy hy' => ?_) χ x hx hx'
    rw [← hsum, ← hsum, gs_res (𝟙 _) y (le p) hy, gs_res (𝟙 _) y (le p') hy',
      gs_unit Q.q.left y (M.U p.1.2 ⊓ M.U p'.1.2) ⟨p.2.2 hy, p'.2.2 hy'⟩]
    refine (gs_compat s (𝟙 _) y (le p hy) (le p' hy')).trans ?_
    rw [gm_pull_g M Q.q.left (𝟙 _) y _ _ (le p hy) (le p' hy'), Category.id_comp]

theorem exists_sec_div [IsCommMonObj G] (M : LB Q.B.left) (hM : M.IsLB) (s : LB.Sec (M.pull Q.q.left))
    (hs : ∃ j, s.f j ≠ 0) : ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧
      ∃ s : LB.Sec (LB.div M O), ∃ j, s.f j ≠ 0 := by
  have := Q.q_flat
  have := Q.q_surj
  obtain ⟨χ, α, V, i, f, hV, hc, hf, ⟨p₀, hp₀⟩, hff⟩ := exists_component Q M hM s hs
  obtain ⟨N, u, hN, hw, hu⟩ := WtBundle.exists_bundle Q χ
  refine ⟨N, hN, WtBundle.exists_gen_lam Q χ N hN u hw hu, ?_⟩
  have loc : ∀ p : α × N.ι, ∃ c : Γ(Q.B.left, V p.1 ⊓ N.U p.2), ∀ x, Q.q.left x ∈ V p.1 ⊓ N.U p.2 →
      gs Q.q.left x _ c = gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p.1) (f p.1) *
        (gm (𝟙 _) x (Q.q.left ⁻¹ᵁ N.U p.2) (u p.2))⁻¹.val := fun p => by
    have l₁ : Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2) ≤ Q.q.left ⁻¹ᵁ V p.1 := fun _ k => k.1
    have l₂ : Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2) ≤ Q.q.left ⁻¹ᵁ N.U p.2 := fun _ k => k.2
    have w := ((hf p.1).res l₁).mul ((hw p.2).inv.res l₂)
    rw [add_neg_cancel] at w
    obtain ⟨c, hc⟩ := exists_app_of_isWt Q _ _ w
    refine ⟨c, fun x hx => ?_⟩
    have e := gs_pull (𝟙 _) Q.q.left x _ hx c
    rw [Category.id_comp] at e
    rw [← e, hc, gs_mul (𝟙 _) x (Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2)) hx, gs_res (𝟙 _) x l₁ hx, gs_res (𝟙 _) x l₂ hx,
      gs_unit (𝟙 _) x _ (l₂ hx), map_inv]
  choose c hc' using loc
  obtain ⟨σ, hσ⟩ := exists_sec_of_refinement (LB.isLB_div hM hN) (fun p : α × N.ι => V p.1 ⊓ N.U p.2)
    (fun p => (i p.1, p.2)) (fun p => inf_le_inf_right _ (hV p.1))
    (fun y => (hc y).elim fun p hp => (exists_chart hN y).elim fun k hk => ⟨(p, k), hp, hk⟩) c
    (fun y p p' hp hp' => by
      obtain ⟨x, rfl⟩ := Q.q.left.surjective y
      apply stalkMap_injective Q.q.left x
      have hm : Q.q.left x ∈ M.U (i p.1) ⊓ N.U p.2 ⊓ (M.U (i p'.1) ⊓ N.U p'.2) :=
        ⟨⟨hV _ hp.1, hp.2⟩, hV _ hp'.1, hp'.2⟩
      have e₁ := congrArg Units.val ((WtBundle.gm_stalkMap Q.q.left x (𝟙 _) _ hm
        ((LB.div M N).g (i p.1, p.2) (i p'.1, p'.2))).trans
        (gm_div N M (Q.q.left ≫ 𝟙 _) x (i p.1, p.2) (i p'.1, p'.2) hm))
      have e₂ := hu _ (𝟙 _) x p.2 p'.2 hp.2 hp'.2
      rw [Category.comp_id] at e₁
      rw [Category.id_comp] at e₂
      rw [map_mul, ← gs_stalkMap _ x _ hp, ← gs_stalkMap _ x _ hp', hc' p x hp, hc' p' x hp',
        hff _ _ x hp.1 hp'.1, e₂]
      refine Eq.trans ?_ (congrArg (· * _) e₁).symm
      simp only [mul_inv, Units.val_mul]
      ring)
  obtain ⟨x, hx, hx0⟩ := exists_gs_ne_zero hp₀
  obtain ⟨k, hk⟩ := exists_chart hN (Q.q.left x)
  have hm : Q.q.left x ∈ (LB.div M N).U (i p₀, k) := ⟨hV _ hx, hk⟩
  refine ⟨σ, (i p₀, k), fun h => hx0 ?_⟩
  have e := hσ _ (i p₀, k) (p₀, k) hm ⟨hx, hk⟩
  rw [h, LBGerm.gs_zero (𝟙 _) (Q.q.left x) _ hm, eq_comm, Units.mul_right_eq_zero] at e
  have e' := hc' (p₀, k) x ⟨hx, hk⟩
  rw [gs_stalkMap _ x _ (show _ ∈ V p₀ ⊓ N.U k from ⟨hx, hk⟩), e, map_zero, eq_comm, Units.mul_left_eq_zero] at e'
  exact e'

end GlobalTheory.WtSec

namespace GlobalTheory

theorem exists_sec_primitive_twist : GlobalFnsSt → ∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (M : LB Q.B.left), M.IsLB → (∃ s : LB.Sec (M.pull Q.q.left), (∃ j, s.f j ≠ 0)) → ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧ ∃ s : LB.Sec (LB.div M O), (∃ j, s.f j ≠ 0) :=
  fun _ _ _ _ _ _ _ _ _ Q M hM ⟨s, hs⟩ => WtSec.exists_sec_div Q M hM s hs

end GlobalTheory
end
