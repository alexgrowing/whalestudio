import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTransportEquivariantCartesianPreservesComStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

open MonObj GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem spMap_eps_alg {R : Type} [CommRing R] (a : R) :
    spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [epsMul]

theorem spMap_fst_alg {R : Type} [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 (Sp R) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]))

theorem cancel_g_ψ (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) {T : Scheme.{0}} {u₁ u₂ : T ⟶ G'.left}
    (h₁ : u₁ ≫ G'.hom = u₂ ≫ G'.hom) (h₂ : u₁ ≫ g ≫ ψ = u₂ ≫ g ≫ ψ) : u₁ = u₂ :=
  hg.hom_ext (hψ.hom_ext (by simpa using h₂) (by simp only [Category.assoc, hg.w, reassoc_of% h₁])) h₁

variable {R : Type} [CommRing R]

theorem one_g_ψ (hG : IsGrpPullback G' t.G p ψ) {b : X ⟶ X} {g : G'.left ⟶ G'.left} (hgb : IsGrpPullback G' G' b g)
    (q : Sp R ⟶ X) : (1 : Over.mk q ⟶ G').left ≫ g ≫ ψ = (1 : Over.mk ((q ≫ b) ≫ p) ⟶ t.G).left := by
  have h1 := grpPull_one hgb (Over.mk q)
  have h2 := grpPull_one hG (Over.mk (q ≫ b))
  rw [← Category.assoc, ← h1]
  exact h2.symm

theorem isTan_trv (hG : IsGrpPullback G' t.G p ψ) {b : X ⟶ X} {g : G'.left ⟶ G'.left} (hgb : IsGrpPullback G' G' b g)
    (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t (q ≫ p) v) :
    IsTanAtG t ((q ≫ b) ≫ p) (trv hG.1 g q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hG.1 q hv.1
  refine ⟨trv_over hG.1 g hgb.1.w q hv.1, ?_⟩
  rw [trv_eq hG.1 g q w hw hw']
  have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w = (1 : Over.mk q ⟶ G').left :=
    hG.1.hom_ext (by rw [Category.assoc, hw, hv.2]; exact grpPull_one hG (Over.mk q))
      (by rw [Category.assoc, hw', ← Category.assoc, spMap_fst_alg, Category.id_comp]
          exact (Over.w (1 : Over.mk q ⟶ G')).symm)
  rw [← Category.assoc, e, one_g_ψ hG hgb q]

theorem trv_eig (hψ : IsPullback ψ G'.hom t.G.hom p) {act' : OAct (𝓞 E) G'}
    (hact : ∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) {g : G'.left ⟶ G'.left}
    (hgc : ∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p)
    (a : 𝓞 E) (c : R) (he : v ≫ (t.act.act a).left = spMap (epsMul c) ≫ v) :
    trv hψ g q v ≫ (t.act.act a).left = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have hwa : w ≫ (act'.act a).left = spMap (epsMul c) ≫ w :=
    hψ.hom_ext (by rw [Category.assoc, hact, ← Category.assoc, hw, he, Category.assoc, hw])
      (by rw [Category.assoc, Over.w, hw', Category.assoc, hw', ← Category.assoc, spMap_eps_alg])
  rw [trv_eq hψ g q w hw hw']
  simp only [Category.assoc]
  rw [← hact a, ← reassoc_of% (hgc a), reassoc_of% hwa]

theorem exists_trv_eq (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) (q : Sp R ⟶ X) {w' : Sp (DualNumber R) ⟶ t.G.left}
    (hw' : w' ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p) :
    ∃ w₀ : Sp (DualNumber R) ⟶ G'.left, w₀ ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q ∧
      w₀ ≫ g ≫ ψ = w' := by
  obtain ⟨w'', h1, h2⟩ := exists_lift hψ (q ≫ b) hw'
  refine ⟨hg.lift w'' (spMap (algebraMap R (DualNumber R)) ≫ q) (by rw [h2, Category.assoc]), hg.lift_snd _ _ _, ?_⟩
  rw [← Category.assoc, hg.lift_fst, h1]

theorem trv_injective (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) (q : Sp R ⟶ X) {v₁ v₂ : Sp (DualNumber R) ⟶ t.G.left}
    (h₁ : v₁ ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p)
    (h₂ : v₂ ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) (h : trv hψ g q v₁ = trv hψ g q v₂) :
    v₁ = v₂ := by
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_lift hψ q h₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := exists_lift hψ q h₂
  rw [trv_eq hψ g q w₁ hw₁ hw₁', trv_eq hψ g q w₂ hw₂ hw₂'] at h
  rw [← hw₁, ← hw₂, cancel_g_ψ hψ hg (hw₁'.trans hw₂'.symm) h]

end

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Y : Scheme.{0}} {t : SAB H Y} {R : Type} [CommRing R] {x0 : Sp R ⟶ Y} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → R} {w₁ w₂ : Sp (DualNumber R) ⟶ t.G.left}
    (h₁ : IsCombAtG t x0 v a w₁) (h₂ : IsCombAtG t x0 v a w₂) : w₁ = w₂ := by
  obtain ⟨u, hu, e⟩ := h₁
  obtain ⟨u', hu', e'⟩ := h₂
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← e, ← e', this]

open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections in

theorem trv_eigFrame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {X' : Scheme.{0}} (p : X' ⟶ Y.X) (G' : Over X') [GrpObj G'] (ψ : G'.left ⟶ Y.t.G.left) (act' : OAct (𝓞 E) G') (b : X' ≅ X') (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' Y.t.G p ψ), (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (Y.t.act.act a).left) → IsGrpPullback G' G' b.hom g → (∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) → ∀ {R : Type} [CommRing R] (φR : c.F →+* R) (q : Sp R ⟶ X') (x' : Sp R ⟶ Y.X), x' = (q ≫ b.hom) ≫ p → ∀ e : GlobalTheory.ShFam.EigFrame Y φR (q ≫ p), ∃ e' : GlobalTheory.ShFam.EigFrame Y φR x', ∀ τ i, e'.v τ i = GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y X' p G' _ ψ act' b g hG hact hgb hgc R _ φR q x' hx' e
  subst hx'
  have hv : ∀ τ i, e.v τ i ≫ Y.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun τ i => (e.tan τ i).1
  refine ⟨{ v := fun τ i => GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i)
            tan := fun τ i => GlobalTheory.EqvTrans.isTan_trv hG hgb q (e.tan τ i)
            eig := fun τ i a => GlobalTheory.EqvTrans.trv_eig hG.1 hact hgc q (hv τ i) a _ (e.eig τ i a)
            basis := ?_ }, fun τ i => rfl⟩
  intro τ w' hw' heig
  obtain ⟨w₀, hw₀, hw₀g⟩ := GlobalTheory.EqvTrans.exists_trv_eq hG.1 hgb.1 q hw'.1
  have htr : GlobalTheory.EqvTrans.trv hG.1 g q (w₀ ≫ ψ) = w' := (GlobalTheory.EqvTrans.trv_eq hG.1 g q w₀ rfl hw₀).trans hw₀g
  have hone : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w₀ = (1 : Over.mk q ⟶ G').left :=
    GlobalTheory.EqvTrans.cancel_g_ψ hG.1 hgb.1
      (by rw [Category.assoc, hw₀, ← Category.assoc, GlobalTheory.EqvTrans.spMap_fst_alg, Category.id_comp]
          exact (Over.w (1 : Over.mk q ⟶ G')).symm)
      (by rw [Category.assoc, hw₀g, hw'.2, GlobalTheory.EqvTrans.one_g_ψ hG hgb q])
  have hwt : IsTanAtG Y.t (q ≫ p) (w₀ ≫ ψ) :=
    ⟨by rw [Category.assoc, hG.1.w, ← Category.assoc, hw₀, Category.assoc],
      by rw [← Category.assoc, hone]; exact (grpPull_one hG (Over.mk q)).symm⟩
  have hwe : ∀ a : 𝓞 E, (w₀ ≫ ψ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (φR (embK c τ a))) ≫ (w₀ ≫ ψ) := fun a => by
    have h0 : w₀ ≫ (act'.act a).left = spMap (epsMul (φR (embK c τ a))) ≫ w₀ :=
      GlobalTheory.EqvTrans.cancel_g_ψ hG.1 hgb.1
        (by rw [Category.assoc, Over.w, hw₀, Category.assoc, hw₀, ← Category.assoc, GlobalTheory.EqvTrans.spMap_eps_alg])
        (by rw [Category.assoc, reassoc_of% (hgc a), hact a, ← Category.assoc w₀, ← Category.assoc (w₀ ≫ g),
              Category.assoc w₀, hw₀g, heig a, Category.assoc, hw₀g])
    rw [Category.assoc, ← hact a, ← Category.assoc, h0, Category.assoc]
  obtain ⟨a, ha, huniq⟩ := e.basis τ (w₀ ≫ ψ) hwt hwe
  refine ⟨a, ?_, fun a' ha' => ?_⟩
  · have h := GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb Y.t p G' ψ b.hom g hG hgb q (e.v τ) a (w₀ ≫ ψ) (e.tan τ) hwt ha
    rwa [htr] at h
  · obtain ⟨u, hut, huc⟩ : ∃ u : Sp (DualNumber R) ⟶ Y.t.G.left, IsTanAtG Y.t (q ≫ p) u ∧
        IsCombAtG Y.t (q ≫ p) (e.v τ) a' u :=
      ⟨(tv (∑ i, a' i • tanOf (e.tan τ i))).left, isTan_tv _, (isComb_iff (fun i => tanOf (e.tan τ i)) a' _).2 rfl⟩
    have h1 := GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb Y.t p G' ψ b.hom g hG hgb q (e.v τ) a' u (e.tan τ) hut huc
    have h2 : GlobalTheory.EqvTrans.trv hG.1 g q u = w' := GlobalTheory.EqvTrans.isCombAtG_unique h1 ha'
    have h3 : u = w₀ ≫ ψ := GlobalTheory.EqvTrans.trv_injective hG.1 hgb.1 q hut.1 hwt.1 (h2.trans htr.symm)
    exact huniq a' (h3 ▸ huc)

end GlobalTheory.EqvTrans
