import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional

noncomputable section

namespace GlobalTheory.ArcLevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have : Surjective (spMap β) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_genPt {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} {A : Over (Sp (FractionRing R))}
    (gen : (Over.pullback (jK R)).obj G ≅ A) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : Sp F ⟶ G.left) (hg : g ≫ G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ A, x.left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) = g := by
  let z : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift g (jFK (R := R) F) hg) (pullback.lift_snd _ _ _)
  refine ⟨z ≫ gen.hom, ?_⟩
  have hgi : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show (z.left ≫ gen.hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc gen.hom.left, hgi, Category.id_comp]
  exact pullback.lift_fst _ _ _

theorem genRel_of_heq {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ φ' : B ⟶ B₀} (h : φ' = φ)
    {w : LB.Iso M (M₀.pull φ)} {w' : LB.Iso M (M₀.pull φ')} (hw : HEq w' w)
    {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (H : GenRel w t t₀ x) :
    GenRel w' t t₀ x := by
  subst h
  obtain rfl := eq_of_heq hw
  exact H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_conj_part (v : D.La) : ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {S : Scheme.{0}} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta v = o.eta v' := by
  have h : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]; trivial
  obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := Submodule.mem_sup.1 h
  exact ⟨v₂, h₂, fun o => by rw [o.eta_add, o.eta_ker _ h₁, _root_.one_mul]⟩

variable {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}

theorem witData {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {χ : Sp (PowerSeries k) ⟶ Y.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) :
    WitData a W.P.D W.P.oD W.φ W.he W.w W.e := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  exact ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF h₁ h₂ => (s6 F uF h₁ h₂).1⟩

set_option maxHeartbeats 1600000 in

theorem level_core (hL : Laws) (hL2 : Laws2) (h5 : Laws5) {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre)
    (hφ : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ)
    (hxe : ∀ x, hD.xe (W.e x) = W'.e x)
    (w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫
      pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)))
    (hw₁ : HEq w₁ W.w) (T : Tri W'.w hD.w w₁) (ψ : W.t.G ≅ W'.t.G)
    (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G) (hbc : IsMonHom bc.hom)
    (hψ : bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left)
    (hPU : IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U)
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ)
    (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ') (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n)
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
    (hσ : (n = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨
      (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v))
    (g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left) (hg : g ≫ W.t.G.hom = jK (PowerSeries k))
    (hgm : g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ) : g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := by
  have hG : GlobalFnsSt := globalFns_holds
  have hR := admissibleBase_powerSeries k
  obtain ⟨F, _, _, _, _, hF⟩ := ArcTransport.exists_commonField k
  have hn : 1 ≤ n := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  have hn' : n ∣ l.M' := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_lcm_left _ _
  obtain ⟨q₀, e1, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing k) F) (RingHom.comp_id _) p₀
  obtain ⟨q, e2, e3⟩ := ArcTransport.exists_transport (witData W) hF rfl hG hn' q₀
  have hF' : ∀ r : PowerSeries k, algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ r) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ ((RingHom.id _) r)) := fun _ => rfl
  obtain ⟨q', hq₁, hq₂⟩ := qkPullExists hG _ _ (RingHom.id _) W'.P.D.toPre W.P.D.toPre hD F hF' n q

  have hc : (y' ≫ σ'.left ≫ Y'.m.φ) ≫ Y'.t.G.hom = jK (PowerSeries k) ≫ χ' := by
    have a₁ : Y'.m.φ ≫ Y'.t.G.hom = Y'.oF.t.G.hom ≫ Y'.j := Y'.m.cart.1.w
    have a₂ : σ'.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ'
    rw [Category.assoc, Category.assoc, a₁, reassoc_of% a₂, hy']
  let g' : Sp (FractionRing (PowerSeries k)) ⟶ W'.t.G.left := W'.m.cart.1.lift _ _ hc
  have hg' : g' ≫ W'.t.G.hom = jK (PowerSeries k) := W'.m.cart.1.lift_snd _ _ _
  have hgm' : g' ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := W'.m.cart.1.lift_fst _ _ _
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨x, hx⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g) (by rw [Category.assoc, hg])
  obtain ⟨x', hx'⟩ := exists_genPt W'.P.U.gen (jFK (R := PowerSeries k) F ≫ g') (by rw [Category.assoc, hg'])
  obtain ⟨x'', hx''⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g' ≫ ψ.inv.left)
    (by rw [Category.assoc, Category.assoc, Over.w, hg'])
  have t₁ : QkToAkU W.P.U.toUnifPre F n q x := by
    refine (W.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y) (by rw [Category.assoc, hy]) n p₀ σ ?_
      q₀ q x e1 e2 e3 ?_
    · rcases hσ with ⟨h, v, h₁, h₂, -⟩ | ⟨h, v, hv, h₁, h₂, -⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · rw [reassoc_of% hx, hgm, Category.assoc]
  have t₂ : QkToAkU W'.P.U.toUnifPre F n q' x' := by
    refine (W'.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y') (by rw [Category.assoc, hy']) n p₀ σ' ?_
      q₀ q' x' e1 ?_ (fun z => ?_) ?_
    · rcases hσ with ⟨h, v, h₁, -, h₂⟩ | ⟨h, v, hv, h₁, -, h₂⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · have : hD.xe q.y = q'.y := by rw [hq₁, AddEquiv.apply_symm_apply]
      rw [← this, e2]; exact hxe _
    · obtain ⟨hψ', hm⟩ := hq₂.2 (W.e z)
      have pm := (maps_iff hD.w _ _ _ (q.g.s (W.e z)) (q'.g.s (hD.xe (W.e z))) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
      have k' := (genRel_transfer T W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB hψ' pm _ _).2
        (genRel_of_heq hφ hw₁ (e3 z))
      rw [hxe z] at k'
      exact k'
    · rw [reassoc_of% hx', hgm', Category.assoc]
  have t₃ : QkToAkU W.P.U.toUnifPre F n q x'' :=
    h5.qkBaseChange _ _ _ _ hR hR (RingHom.id _) W'.P.D W'.P.A W'.t.G W'.P.U W.t.G bc hbc W.P.A W.P.D hD W.P.U
      hPU F hF' n hn q' x' q x'' hq₁ hq₂ (by rw [hψ, reassoc_of% hx'', hih, Category.comp_id, hx']) t₂
  have hxx := TorsionImage.qkToAkU_unique hL hL2 _ _ hR W.P.D W.P.A W.t.G W.t.semi W.P.U F n hn q x x'' t₁ t₃
  have := epi_spMap (algebraMap (FractionRing (PowerSeries k)) F)
  have hgg : g = g' ≫ ψ.inv.left :=
    (cancel_epi (spMap (algebraMap (FractionRing (PowerSeries k)) F))).1 (hx.symm.trans (hxx ▸ hx''))
  rw [hgg, Category.assoc, reassoc_of% hih, hgm']

theorem level_match : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  intro hL hL2 h5 E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ⟨hφ, hxe, w₁, hw₁, T⟩ ψ bc _ hbc hψ hPU _
    y y' hy hy' _ _ σ σ' hσ g hg hgm
  rcases hσ with ⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩
  · exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.A (a.etaA v) σ σ'
      (Or.inl ⟨rfl, v, HEq.rfl, h₁, h₂⟩) g hg hgm
  · obtain ⟨v', hv', e⟩ := exists_conj_part (l := l) v
    exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.M (a.eta v') σ σ'
      (Or.inr ⟨rfl, v', hv', HEq.rfl, h₁.trans (e _), h₂.trans (e _)⟩) g hg hgm

end GlobalTheory.ArcLevel
