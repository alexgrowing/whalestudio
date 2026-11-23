import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_germ_top {Z X : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs f z U a = (Z.presheaf.germ ⊤ z trivial).hom ((f.appLE U ⊤ h).hom a) := by
  rw [gs_eq f z U (h trivial)]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z trivial _).symm

theorem specMap_appLE_top {R Ω : Type} [CommRing R] [CommRing Ω] (f : R →+* Ω) (V : (Sp R).Opens) (hV : ⊤ ≤ V)
    (h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ V) (a : Γ(Sp R, V)) :
    ((Spec.map (CommRingCat.ofHom f)).appLE V ⊤ h).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (((Sp R).presheaf.map (homOfLE hV).op).hom a))) := by
  have e1 := Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom f)) (U := ⊤) (U' := V) (V := ⊤) (fun _ _ => trivial) (homOfLE hV).op
  have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  rw [← e1]
  have e3 : (Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ (fun _ _ => trivial) = (Spec.map (CommRingCat.ofHom f)).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have e4 : ∀ x, ((Spec.map (CommRingCat.ofHom f)).appTop).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)) := fun x => by
    have := congrArg (fun t => t.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [CommRingCat.hom_comp, RingHom.comp_apply, e3, e4]

theorem fromSpec_appLE_self {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{0}) (a : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom a) = a := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_specMap_comp {R Ω : Type} [CommRing R] [CommRing Ω] {X : Scheme.{0}} (f : R →+* Ω) (g : Sp R ⟶ X)
    (z : Sp Ω) (U : X.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (Spec.map (CommRingCat.ofHom f) ≫ g) z U a = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((g.appLE U ⊤ hg).hom a)))) := by
  have h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ (g ⁻¹ᵁ U) := fun x _ => hg trivial
  rw [← gs_pull (Spec.map (CommRingCat.ofHom f)) g z U (hg trivial) a, gs_eq_germ_top _ z _ h,
    specMap_appLE_top f _ hg h]
  rfl

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartVal_mem_range_of_agree : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  intro X S Y gX L hL α k s j W hW hWa hαW T _ lam W' _ io σ hσ Ω _ ψ e hψ
  have hq : (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) ≫ gX =
      𝟙 (Sp W') ≫ (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.id_comp]
    simp only [spMap, Category.assoc]
  let q'' := pullback.lift (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) (𝟙 (Sp W')) hq
  let P : Sp Ω ⟶ _ := Spec.map (CommRingCat.ofHom e) ≫ q''
  let pY : Sp Ω ⟶ Y := Spec.map (CommRingCat.ofHom ψ) ≫ hαW.fromSpec
  have hring : α.appLE W (α ⁻¹ᵁ W) le_rfl ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (e.comp (io.comp lam)) := by
    ext c
    rw [Scheme.Hom.appLE_eq_app]
    exact hψ c
  have hA : P ≫ pullback.fst _ _ = pY ≫ α := by
    simp only [P, pY, q'', Category.assoc, pullback.lift_fst]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec α hWa hαW le_rfl, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      hring, ← CommRingCat.ofHom_comp]
  have hαmem : ∀ x, hαW.fromSpec x ∈ α ⁻¹ᵁ W := fun x => by
    show _ ∈ ((α ⁻¹ᵁ W : Y.Opens) : Set Y)
    rw [← hαW.range_fromSpec]
    exact ⟨x, rfl⟩
  have hWmem : ∀ x, hWa.fromSpec x ∈ W := fun x => by
    show _ ∈ ((W : X.Opens) : Set X)
    rw [← hWa.range_fromSpec]
    exact ⟨x, rfl⟩
  obtain ⟨z⟩ : Nonempty (Sp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
  have hz : (pY ≫ α) z ∈ L.U j := hW (hαmem _)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := Unit) (fun _ => pY ≫ α) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hz)
  have hag := hσ (Sp Ω) P pY hA z J hJ
  have hl : sval s pY z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ (chartVal L α s j W hW))) := by
    rw [sval_of s pY z J (fun _ => j) (fun _ => hJj ()),
      ← gs_res pY z (locInt_le_chart L α j W hW) (hαmem _) (s.f (fun _ => j))]
    rw [gs_specMap_comp ψ hαW.fromSpec z (α ⁻¹ᵁ W) hαW.fromSpec_preimage_self.ge]
    rw [fromSpec_appLE_self hαW]
    exact congrArg (fun t => ((Sp Ω).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ t)))
      (ΓSpecIso_hom_inv_apply _ _)
  have hq'' : ⊤ ≤ q'' ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => pullback.fst _ _) (fun _ => j) := fun x _ =>
    Set.mem_iInter.2 fun _ => hW (by
      show (q'' ≫ pullback.fst _ _) x ∈ W
      rw [pullback.lift_fst]
      exact hWmem _)
  have hr : sval σ P z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (e ((Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom
        ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j)))))) := by
    rw [sval_of σ P z J (fun _ => j) (fun _ => by rw [hA]; exact hJj ())]
    exact gs_specMap_comp e q'' z _ hq'' _
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j))),
    ((((Sp Ω).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).injective) ?_⟩
  simp only [RingHom.comp_apply]
  rw [← hl, ← hr, hag]

end GlobalTheory.Mum
