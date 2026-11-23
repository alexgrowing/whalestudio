import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sabMap_of_iso (hG : GlobalFnsSt) {S S' : Scheme.{0}} {t t' : SAB H S} {u u' : SAB H S'} {f : S' ⟶ S}
    (n : SABMap u t f) (n' : SABMap u' t' f) (hA : IsAbelianScheme u.G) (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hL : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left)) :
    ∃ m : SABMap u u' (𝟙 _), m.φ ≫ n'.φ = n.φ ≫ ψ.hom.left := by
  have c := n.cart.comp (isGrpPullback_of_iso ψ)
  rw [Category.comp_id] at c
  obtain ⟨α, hα, hφ⟩ := grpPullback_iso c n'.cart
  have ha : ∀ x, (u.act.act x).left ≫ α.hom.left = α.hom.left ≫ (u'.act.act x).left := fun x => by
    have e : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act x).left := congrArg (fun q => q.left) (hact x)
    apply n'.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, n'.act, ← Category.assoc, n.act, ← Category.assoc, hφ, Category.assoc,
        Category.assoc, e]
    · simp only [Category.assoc, Over.w]
  have hb : LBIso u.PP.L (u'.PP.L.pull α.hom.left) := by
    obtain ⟨w, hw⟩ := hL
    obtain ⟨w₁, g₁, -⟩ := (isPullCubical_iff _ _ _).1 n.lin
    obtain ⟨w₂, g₂, -⟩ := (isPullCubical_iff _ _ _).1 n'.lin
    have hw' := (isGen_iff w).1 hw
    obtain ⟨w₃, T⟩ := exists_comp t.PP.isLB w w₁ hw' g₁ t'.PP.isLB u.PP.isLB
    obtain ⟨w₄, g₄⟩ : ∃ w₄ : LB.Iso u.PP.L (t'.PP.L.pull (α.hom.left ≫ n'.cm.F)), PGen w₄ := by
      rw [hφ]; exact ⟨w₃, T.pgen_comp t.PP.isLB hw' g₁⟩
    obtain ⟨w₅, T'⟩ := exists_cancel t'.PP.isLB w₂ w₄ g₂ g₄ u'.PP.isLB u.PP.isLB
    exact ⟨w₅, (isGen_iff w₅).2 (T'.pgen_cancel t'.PP.isLB g₂ g₄)⟩
  exact ⟨⟨CubeMap.ofHom α.hom, isGrpPullback_of_iso α, rfl, ha,
    HeckePoint.isPullCubical_of_iso hG hA α.hom u.cub u'.cub hb⟩, hφ⟩

theorem exists_sab_fac {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : h = g ≫ f) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

variable {D : Datum H} {l : Level H}

theorem objMap_eq (hS : SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {F : Type} [Field F]
    {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s'} {y y' : Sp F ⟶ S} (e : y = y')
    (m : ObjMap o₁ o y) (m' : ObjMap o₁ o y') : m.toSABMap.φ = m'.toSABMap.φ := by
  subst e
  exact objMap_unique_of_field hS m m'

theorem point_eq (hL : Laws) {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Scheme.{0}} {χ : S ⟶ Y.X}
    {χ' : S ⟶ Y'.X} {t t' : SAB H S} (m : SABMap t Y.t χ) (m' : SABMap t' Y'.t χ') (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hb : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left))
    {K : Type} [Field K] (j : Sp K ⟶ S) (y y' : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = j ≫ χ) (hy' : y' ≫ Y'.j = j ≫ χ')
    (hs : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _)
    (hlev : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      ∀ g : Sp K ⟶ t.G.left, g ≫ t.G.hom = j → g ≫ m.φ = y ≫ σ.left ≫ Y.m.φ →
        g ≫ ψ.hom.left ≫ m'.φ = y' ≫ σ'.left ≫ Y'.m.φ) :
    y = y' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp K),
      g ≫ t.G.hom = τ ≫ j → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ m.φ = g₁ ≫ Y.m.φ →
      g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ ψ.hom.left ≫ m'.φ = g₂ ≫ Y'.m.φ := by
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  have hs' : y' ≫ pullback.fst _ _ ≫ Xo.s = y ≫ pullback.fst _ _ ≫ Xo.s := by
    rw [pullback.condition, reassoc_of% hs]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y
    rfl rfl (by rw [hid, Category.comp_id]) Y.oF
  obtain ⟨o', ⟨m₂⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y'
    rfl rfl (by rw [hid, Category.comp_id, hs']) Y'.oF
  obtain ⟨k₁, e₁⟩ := ObjMaps.exists_sab_comp Y.m m₁.toSABMap
  obtain ⟨k₂, e₂⟩ := ObjMaps.exists_sab_comp Y'.m m₂.toSABMap
  obtain ⟨n, hn⟩ := exists_sab_fac m k₁ hy
  obtain ⟨n', hn'⟩ := exists_sab_fac m' k₂ hy'
  obtain ⟨ν, hν⟩ := exists_sabMap_of_iso hL.globalFns n n'
    ⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ ψ hact hb
  have hνw : ν.φ ≫ o'.t.G.hom = o.t.G.hom := ν.cart.1.w.trans (Category.comp_id _)
  have hψ : n.φ ≫ ψ.hom.left ≫ m'.φ = ν.φ ≫ m₂.toSABMap.φ ≫ Y'.m.φ := by
    rw [← e₂, hn', reassoc_of% hν]
  have key : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
      (x : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (x' : 𝟙_ (Over (Sp K)) ⟶ o'.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      x.left ≫ m₁.toSABMap.φ = y ≫ σ.left → x'.left ≫ m₂.toSABMap.φ = y' ≫ σ'.left →
      x.left ≫ ν.φ = 𝟙 _ ≫ x'.left := by
    intro σ σ' x x' h hx hx'
    have b : x.left ≫ o.t.G.hom = 𝟙 _ := Over.w x
    have b' : x'.left ≫ o'.t.G.hom = 𝟙 _ := Over.w x'
    have q := hlev σ σ' h (x.left ≫ n.φ) (by rw [Category.assoc, n.cart.1.w, reassoc_of% b])
      (by rw [Category.assoc, ← hn, e₁, reassoc_of% hx])
    rw [Category.id_comp]
    apply k₂.cart.1.hom_ext
    · show (_ ≫ _) ≫ k₂.φ = _ ≫ k₂.φ
      rw [e₂, Category.assoc, ← hψ, reassoc_of% hx', ← q, Category.assoc]
    · rw [Category.assoc, hνw, b, b']
  let ν' : ObjMap o o' (𝟙 _) :=
    ⟨ν, fun a => key _ _ _ _ (Or.inr ⟨a, rfl, rfl⟩) (m₁.eta a) (m₂.eta a),
      fun a => key _ _ _ _ (Or.inl ⟨a, rfl, rfl⟩) (m₁.etaA a) (m₂.etaA a)⟩
  obtain ⟨p₁, f₁⟩ := ObjComp.objMap_comp Y.m0 m₁
  obtain ⟨p₀, f₀⟩ := ObjComp.objMap_comp m₂ ν'
  obtain ⟨p₂, f₂⟩ := ObjComp.objMap_comp Y'.m0 p₀
  have hf := (Xo.rep _ _ inferInstance o).unique ⟨Category.assoc _ _ _, ⟨p₁⟩⟩
    ⟨by rw [Category.id_comp, Category.assoc, hs'], ⟨p₂⟩⟩
  have hp : m₁.toSABMap.φ ≫ Y.m0.toSABMap.φ = (ν.φ ≫ m₂.toSABMap.φ) ≫ Y'.m0.toSABMap.φ :=
    f₁.symm.trans ((objMap_eq hL.serre hf p₁ p₂).trans (f₂.trans (congrArg (· ≫ _) f₀)))
  rw [Category.id_comp] at hf
  obtain rfl : y = y' := pullback.hom_ext hf hs
  refine ⟨rfl, fun T g g₁ g₂ τ h₁ h₂ h₃ h₄ h₅ => ?_⟩
  obtain ⟨u, u₁, u₂⟩ : ∃ u : T ⟶ o.t.G.left, u ≫ m₁.toSABMap.φ = g₁ ∧ u ≫ o.t.G.hom = τ :=
    ⟨m₁.cart.1.lift g₁ τ h₂, m₁.cart.1.lift_fst _ _ _, m₁.cart.1.lift_snd _ _ _⟩
  have a₁ : u ≫ n.φ = g := by
    apply m.cart.1.hom_ext
    · show (_ ≫ _) ≫ m.φ = _ ≫ m.φ
      rw [Category.assoc, ← hn, e₁, reassoc_of% u₁, h₃]
    · rw [Category.assoc, n.cart.1.w, reassoc_of% u₂, h₁]
  have a₂ : u ≫ ν.φ ≫ m₂.toSABMap.φ = g₂ := by
    apply Y'.m0.cart.1.hom_ext
    · show (_ ≫ _) ≫ Y'.m0.toSABMap.φ = _ ≫ Y'.m0.toSABMap.φ
      rw [Category.assoc, ← hp, reassoc_of% u₁, h₄]
    · rw [Category.assoc, Category.assoc, m₂.cart.1.w, reassoc_of% hνw, reassoc_of% u₂, ← h₅, h₂]
  rw [← a₁, ← a₂, Category.assoc, hψ, Category.assoc, Category.assoc]

end ArcObj

theorem arcWit_point_eq_of_iso : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) → y = y' ∧ (Mono Y.j → ∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left), g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) := by
  intro hL _ E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ψ bc hψ _ hbc hU hact y y' hy hy' hs hs' hlev
  have hb : LBIso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hU.lg
    rw [← W.P.bundle, ← W'.P.bundle, ← hbc]
    exact ⟨w, hw⟩
  obtain ⟨e, h⟩ := ArcObj.point_eq hL W.m W'.m ψ hact hb _ y y' hy hy' (hs.trans hs'.symm) hlev
  refine ⟨e, fun hm T g g₁ g₂ h₁ h₂ h₃ => ?_⟩
  have := ThetaShiftProofs.isOpenImmersion_jK_powerSeries k
  have q : (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j := by
    have h₁' : g ≫ W.m.cm.F = g₁ ≫ Y.m.cm.F := h₁
    rw [Category.assoc, ← W.m.cart.1.w, reassoc_of% h₁', Y.m.cart.1.w, Category.assoc]; rfl
  have hr : Set.range (g ≫ W.t.G.hom) ⊆ Set.range (jK (PowerSeries k)) := by
    rintro _ ⟨p, rfl⟩
    exact arcWit_mem_range_jK_of_mem_range_j E H D l Xo c k bF a O β Y χ W _
      ⟨(g₁ ≫ Y.oF.t.G.hom) p, congrArg (fun z => z p) q.symm⟩
  have hτ := IsOpenImmersion.lift_fac (jK (PowerSeries k)) _ hr
  refine h T g g₁ g₂ _ hτ.symm ?_ h₁ h₂ h₃
  rw [← cancel_mono Y.j, ← q, Category.assoc _ y, hy, ← Category.assoc _ (jK _), hτ]

end GlobalTheory
