import Development.EtaleCohomology.CohomologicalPurity.OffChaseGeoOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem ht_transport (q : ℕ) {J : Type} [SmallCategory J] (X Y : J → Spc) (X0 Y0 : Spc) (a : ∀ j, X0 ⟶ X j)
    (b : ∀ j, Y0 ⟶ Y j) (ma : ∀ {j k : J} (_ : j ⟶ k), X k ⟶ X j) (mb : ∀ {j k : J} (_ : j ⟶ k), Y k ⟶ Y j)
    (α : ∀ j, X j ≅ Y j) (α0 : X0 ≅ Y0) (hab : ∀ j, a j ≫ (α j).hom = α0.hom ≫ b j)
    (hm : ∀ j k (f : j ⟶ k), ma f ≫ (α j).hom = (α k).hom ≫ mb f) (n i : ℤ)
    (H : (∀ x : Ht q X0 n i, ∃ j, ∃ y, pull _ (a j) (tw q i) n y = x) ∧
      ∀ j y, pull _ (a j) (tw q i) n y = 0 → ∃ (k : J) (f : j ⟶ k), pull _ (ma f) (tw q i) n y = 0) :
    (∀ x : Ht q Y0 n i, ∃ j, ∃ y, pull _ (b j) (tw q i) n y = x) ∧
      ∀ j y, pull _ (b j) (tw q i) n y = 0 → ∃ (k : J) (f : j ⟶ k), pull _ (mb f) (tw q i) n y = 0 := by
  have hba : ∀ j, b j ≫ (α j).inv = α0.inv ≫ a j := fun j => by
    rw [Iso.comp_inv_eq, Category.assoc, hab, Iso.inv_hom_id_assoc]
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := H.1 (pull _ α0.hom (tw q i) n x)
    refine ⟨j, pull _ (α j).inv (tw q i) n y, ?_⟩
    rw [← pull_comp, hba, pull_comp, hy, ← pull_comp, Iso.inv_hom_id, pull_id]
  · have h0 : pull _ (a j) (tw q i) n (pull _ (α j).hom (tw q i) n y) = 0 := by
      rw [← pull_comp, hab, pull_comp, hy, map_zero]
    obtain ⟨k, f, hk⟩ := H.2 j _ h0
    refine ⟨k, f, ?_⟩
    have : pull _ (mb f) (tw q i) n y = pull _ (α k).inv (tw q i) n (pull _ (ma f) (tw q i) n (pull _ (α j).hom (tw q i) n y)) := by
      rw [← pull_comp, ← pull_comp, Category.assoc, hm, Iso.inv_hom_id_assoc]
    rw [this, hk, map_zero]

theorem oj_sup_eq {A : Type} [CommRing A] {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})
    (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (I1 I2 : Ideal A) (j : J) :
    oj D s I1 j ⊔ oj D s I2 j = oj D s (I1 ⊔ I2) j := by
  unfold oj; rw [Ideal.map_sup, off_sup]

theorem sq_iso {X' X : Scheme.{0}} (f : X' ⟶ X) (V W : X.Opens) (V' W' : X'.Opens) (e : V = W) (e' : V' = W')
    (h1 : V' ≤ f ⁻¹ᵁ V) (h2 : W' ≤ f ⁻¹ᵁ W) :
    sch.map (f.resLE V V' h1) ≫ sch.map (X.isoOfEq e).hom = sch.map (X'.isoOfEq e').hom ≫ sch.map (f.resLE W W' h2) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← cancel_mono W.ι]
  simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.resLE_comp_ι, Scheme.isoOfEq_hom_ι_assoc]

theorem ocg_BR : OCG_BR := by
  intro q A B _ _ φ I1 I2 J _ _ D s t hc he n i H
  have T := ht_transport q (fun j => sch.obj (oj D s I1 j ⊔ oj D s I2 j).toScheme)
    (fun j => sch.obj (oj D s (I1 ⊔ I2) j).toScheme)
    (sch.obj (off B (I1.map φ) ⊔ off B (I2.map φ)).toScheme) (sch.obj (off B ((I1 ⊔ I2).map φ)).toScheme)
    (fun j => (conB φ I1 I2 D s t he j).right)
    (fun j => (opnMap (Spec.map (t.app j)) _ _ (oinf_pre φ D s t (I1 ⊔ I2) he j).le).left)
    (fun f => ((sysB I1 I2 D s).map f.op).right)
    (fun f => (opnMap (Spec.map (D.map f)) _ _ (oj_pre D s (I1 ⊔ I2) f).le).left)
    (fun j => sch.mapIso (Scheme.isoOfEq _ (oj_sup_eq D s I1 I2 j)))
    (sch.mapIso (Scheme.isoOfEq _ (by rw [Ideal.map_sup, off_sup])))
    (fun j => sq_iso _ _ _ _ _ _ _ _ _) (fun j k f => sq_iso _ _ _ _ _ _ _ _ _) n i H
  refine ⟨fun x => ?_, fun j h y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := T.1 x
    exact ⟨j, (oinf_pre φ D s t (I1 ⊔ I2) he j).le, y, hy⟩
  · obtain ⟨k, f, hk⟩ := T.2 j y hy
    exact ⟨k, f, (oj_pre D s (I1 ⊔ I2) f).le, hk⟩

theorem sq_le {X' X : Scheme.{0}} (f : X' ⟶ X) (U V : X.Opens) (U' V' : X'.Opens) (hUV : U ≤ V) (hUV' : U' ≤ V')
    (h1 : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (h3 : V'.ι ⁻¹ᵁ U' ≤ (f.resLE V V' hV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)) :
    sch.map (f.resLE U U' h1) ≫ sch.map (Scheme.Opens.isoOfLE hUV).inv =
      sch.map (Scheme.Opens.isoOfLE hUV').inv ≫ sch.map ((f.resLE V V' hV).resLE (V.ι ⁻¹ᵁ U) (V'.ι ⁻¹ᵁ U') h3) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← cancel_mono (Scheme.Opens.ι _), ← cancel_mono (Scheme.Opens.ι _)]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, Scheme.Opens.isoOfLE_inv_ι,
    Scheme.Opens.isoOfLE_inv_ι_assoc]

theorem ocg_BL : OCG_BL := by
  intro q A B _ _ φ I1 I2 J _ _ D s t hc he m i H
  have T := ht_transport q (fun j => sch.obj (oj D s I1 j).toScheme)
    (fun j => ((sysB I1 I2 D s).obj (op j)).left)
    (sch.obj (off B (I1.map φ)).toScheme) (limB φ I1 I2).left
    (fun j => (opnMap (Spec.map (t.app j)) _ _ (oinf_pre φ D s t I1 he j).le).left)
    (fun j => (conB φ I1 I2 D s t he j).left)
    (fun f => (opnMap (Spec.map (D.map f)) _ _ (oj_pre D s I1 f).le).left)
    (fun f => ((sysB I1 I2 D s).map f.op).left)
    (fun j => sch.mapIso (Scheme.Opens.isoOfLE (le_sup_left : oj D s I1 j ≤ oj D s I1 j ⊔ oj D s I2 j)).symm)
    (sch.mapIso (Scheme.Opens.isoOfLE (le_sup_left : off B (I1.map φ) ≤ off B (I1.map φ) ⊔ off B (I2.map φ))).symm)
    (fun j => sq_le _ _ _ _ _ le_sup_left le_sup_left _ _ _) (fun j k f => sq_le _ _ _ _ _ le_sup_left le_sup_left _ _ _) m i
    ⟨fun x => let ⟨j, _, y, hy⟩ := H.1 x; ⟨j, y, hy⟩, fun j y hy => let ⟨k, f, _, hk⟩ := H.2 j _ y hy; ⟨k, f, hk⟩⟩
  exact T

theorem pre_inf {X : Scheme.{0}} (U V : X.Opens) : V.ι ⁻¹ᵁ (U ⊓ V) = V.ι ⁻¹ᵁ U := by
  apply le_antisymm
  · intro x hx; exact hx.1
  · intro x hx
    refine ⟨hx, ?_⟩
    change V.ι x ∈ (V : Set X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩

theorem oj_mul_eq {A : Type} [CommRing A] {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})
    (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (I1 I2 : Ideal A) (j : J) :
    oj D s (I1 * I2) j = oj D s I1 j ⊓ oj D s I2 j := by
  unfold oj; rw [Ideal.map_mul, off_mul]

def isoW {X : Scheme.{0}} (U V W : X.Opens) (e : W = U ⊓ V) : W.toScheme ≅ (V.ι ⁻¹ᵁ U).toScheme :=
  X.isoOfEq e ≪≫ (Scheme.Opens.isoOfLE (inf_le_right : U ⊓ V ≤ V)).symm ≪≫ Scheme.isoOfEq _ (pre_inf U V)

theorem isoW_ι {X : Scheme.{0}} (U V W : X.Opens) (e : W = U ⊓ V) :
    (isoW U V W e).hom ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = W.ι := by
  simp [isoW]

theorem resLE_comp_isoOpenInfPreimage_hom_naturality {X' X : Scheme.{0}} (f : X' ⟶ X) (U V W : X.Opens) (U' V' W' : X'.Opens) (e : W = U ⊓ V)
    (e' : W' = U' ⊓ V') (h1 : W' ≤ f ⁻¹ᵁ W) (hV : V' ≤ f ⁻¹ᵁ V) (h3 : V'.ι ⁻¹ᵁ U' ≤ (f.resLE V V' hV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)) :
    sch.map (f.resLE W W' h1) ≫ sch.map (isoW U V W e).hom =
      sch.map (isoW U' V' W' e').hom ≫ sch.map ((f.resLE V V' hV).resLE (V.ι ⁻¹ᵁ U) (V'.ι ⁻¹ᵁ U') h3) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← cancel_mono (Scheme.Opens.ι _), ← cancel_mono (Scheme.Opens.ι _)]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, isoW_ι]
  rw [← Category.assoc (isoW U' V' W' e').hom, ← Category.assoc ((isoW U' V' W' e').hom ≫ _), Category.assoc (isoW U' V' W' e').hom, isoW_ι]

theorem ocg_AL : OCG_AL := by
  intro q A B _ _ φ I1 I2 J _ _ D s t hc he m i H
  have T := ht_transport q (fun j => sch.obj (oj D s (I1 * I2) j).toScheme)
    (fun j => ((sysA I1 I2 D s).obj (op j)).left)
    (sch.obj (off B ((I1 * I2).map φ)).toScheme) (limA φ I1 I2).left
    (fun j => (opnMap (Spec.map (t.app j)) _ _ (oinf_pre φ D s t (I1 * I2) he j).le).left)
    (fun j => (conA φ I1 I2 D s t he j).left)
    (fun f => (opnMap (Spec.map (D.map f)) _ _ (oj_pre D s (I1 * I2) f).le).left)
    (fun f => ((sysA I1 I2 D s).map f.op).left)
    (fun j => sch.mapIso (isoW _ _ _ (oj_mul_eq D s I1 I2 j)))
    (sch.mapIso (isoW _ _ _ (by rw [Ideal.map_mul, off_mul])))
    (fun j => resLE_comp_isoOpenInfPreimage_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _) (fun j k f => resLE_comp_isoOpenInfPreimage_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _) m i
    ⟨fun x => let ⟨j, _, y, hy⟩ := H.1 x; ⟨j, y, hy⟩, fun j y hy => let ⟨k, f, _, hk⟩ := H.2 j _ y hy; ⟨k, f, hk⟩⟩
  exact T

theorem OffChaseGeo_full : OffChaseGeo := OffChaseGeo_of ocg_AL ocg_BL ocg_BR

end LateralTheory.CohomologicalPurity
