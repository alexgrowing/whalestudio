import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex
namespace LateralTheory.CohomologicalPurity.TubeCut

variable {d : ℕ}

theorem hmap_congr (H : Hens) {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} {φ ψ : A →+* B}
    (e : φ = ψ) (h : I ≤ J.comap φ) (h' : I ≤ J.comap ψ) : H.map φ h = H.map ψ h' := by subst e; rfl

theorem hmap_sq (H : Hens) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D} (a : A →+* B) (b : B →+* D) (c : A →+* C) (e : C →+* D)
    (ha : I ≤ J.comap a) (hb : J ≤ L.comap b) (hc : I ≤ K.comap c) (he : K ≤ L.comap e) (e0 : b.comp a = e.comp c) :
    (H.map b hb).comp (H.map a ha) = (H.map e he).comp (H.map c hc) := by
  rw [← H.map_comp a b ha hb (fun x hx => hb (ha hx)), ← H.map_comp c e hc he (fun x hx => he (hc hx))]
  exact hmap_congr H e0 _ _

theorem appLE_congr {X Y : Scheme.{0}} {u v : X ⟶ Y} (e : u = v) (U : Y.Opens) (W : X.Opens) (h : W ≤ u ⁻¹ᵁ U) :
    u.appLE U W h = v.appLE U W (e ▸ h) := by subst e; rfl

theorem idl {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens) (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    P.ι.ker.ideal V ≤ (P'.ι.ker.ideal V').comap (φ.f.appLE V.1 V'.1 h).hom := by
  have := P.cl; have := P'.cl
  intro a ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [← CommRingCat.comp_apply, P'.ι.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr φ.cart.w,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]

theorem cotangentAtUnit_tangentBijection_naturality (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V1 V2 : P.X.affineOpens) (V1' V2' : P'.X.affineOpens)
    (h1 : V1'.1 ≤ φ.f ⁻¹ᵁ V1.1) (h2 : V2'.1 ≤ φ.f ⁻¹ᵁ V2.1) (hV : V1 ≤ V2) (hV' : V1' ≤ V2') :
    Spec.map (CommRingCat.ofHom (H.map _ (P'.ι.ker.ideal_le_comap_ideal hV'))) ≫
      Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V2.1 V2'.1 h2).hom (idl φ V2 V2' h2))) =
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V1.1 V1'.1 h1).hom (idl φ V1 V1' h1))) ≫
      Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal hV))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact hmap_sq H _ _ _ _ _ _ _ _ (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE])

theorem henselization_spec_map_commutes_with_smooth_pair_hom (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens)
    (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V.1 V'.1 h).hom (idl φ V V' h))) ≫ hensTo H P V =
      hensTo H P' V' ≫ φ.f := by
  dsimp only [hensTo, eta]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H.map_η, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  exact (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec φ.f V.2 V'.2 h)).trans (Category.assoc _ _ _).symm

abbrev RJ {P' P : SP d} (φ : P'.Hom P) : Type :=
  {p : P'.X.affineOpens × P.X.affineOpens // Good P' p.1 ∧ Good P p.2 ∧ p.1.1 ≤ φ.f ⁻¹ᵁ p.2.1}

def Sys.ref (hC : LateralTheory.CohomologicalPurity.LeafChart) {P' P : SP d} (φ : P'.Hom P) : Sys P' where
  J := RJ φ
  V j := j.1.1
  mono h := (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
  good j := j.2.1
  cov x := by
    obtain ⟨V, hV, -, g⟩ := hC d P (φ.f x) ⊤ trivial
    obtain ⟨V', hV', l, g'⟩ := hC d P' x (φ.f ⁻¹ᵁ V.1) hV
    exact ⟨⟨(V', V), g', g, l⟩, hV'⟩
  dir x j k hj hk := by
    have hj2 : φ.f x ∈ j.1.2.1 := j.2.2.2 hj
    have hk2 : φ.f x ∈ k.1.2.1 := k.2.2.2 hk
    obtain ⟨V, hV, l, g⟩ := hC d P (φ.f x) (j.1.2.1 ⊓ k.1.2.1) ⟨hj2, hk2⟩
    obtain ⟨V', hV', l', g'⟩ := hC d P' x (j.1.1.1 ⊓ k.1.1.1 ⊓ φ.f ⁻¹ᵁ V.1) ⟨⟨hj, hk⟩, hV⟩
    exact ⟨⟨(V', V), g', g, l'.trans inf_le_right⟩, ⟨l'.trans (inf_le_left.trans inf_le_left), l.trans inf_le_left⟩,
      ⟨l'.trans (inf_le_left.trans inf_le_right), l.trans inf_le_right⟩, hV'⟩

theorem EtaleRefine_of_push (hP : LeafPush) : LeafRefine := by
  intro hC H d P' P φ
  let S' := Sys.ref hC φ
  let G1 : S'.J ⥤ (Sys.all hC P').J := Monotone.functor (f := fun j => (⟨j.1.1, j.2.1⟩ : {V : P'.X.affineOpens // Good P' V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1)
  let G2 : S'.J ⥤ (Sys.all hC P).J := Monotone.functor (f := fun j => (⟨j.1.2, j.2.2.1⟩ : {V : P.X.affineOpens // Good P V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2)
  let α1 : S'.hen H ⋙ yoneda ⟶ G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda :=
    { app := fun j => (𝟙 ((S'.hen H ⋙ yoneda).obj j) : _ ⟶ (G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).obj j)
      naturality := fun j k f => (Category.comp_id _).trans (Category.id_comp ((G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).map f)).symm }
  obtain ⟨a, ha⟩ := hP _ _ _ _ G1 α1 _ _ (𝟙 (yoneda.obj P'.X)) _ _ (S'.cocHen H) ((Sys.all hC P').cocHen H)
    (fun j => (Category.id_comp _).trans (Category.comp_id _).symm)
  have ea : a ≫ (Sys.all hC P').π H = S'.π H := by
    have := ha; rw [disc.map_id, Category.comp_id] at this; exact this
  let α2 : S'.hen H ⋙ yoneda ⟶ G2 ⋙ (Sys.all hC P).hen H ⋙ yoneda :=
    { app := fun j => yoneda.map (Spec.map (CommRingCat.ofHom
        (H.map (φ.f.appLE (j.1.2).1 (j.1.1).1 j.2.2.2).hom (idl φ j.1.2 j.1.1 j.2.2.2))))
      naturality := fun j k f => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
        (cotangentAtUnit_tangentBijection_naturality H φ j.1.2 k.1.2 j.1.1 k.1.1 j.2.2.2 k.2.2.2 (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).2
          (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).1)).trans (yoneda.map_comp _ _)) }
  obtain ⟨b, hb⟩ := hP _ _ _ _ G2 α2 _ _ (yoneda.map φ.f) _ _ (S'.cocHen H) ((Sys.all hC P).cocHen H)
    (fun j => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map (henselization_spec_map_commutes_with_smooth_pair_hom H φ j.1.2 j.1.1 j.2.2.2)).trans
      (yoneda.map_comp _ _)))
  exact ⟨S', a, b, ea, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
