import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

def IsCop {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) : Prop :=
  ∀ (R : Type) [CommRing R] (g : ι → (A' →+* R)) (c : A →+* R), (∀ i, (g i).comp φ = c) →
    ∃! h : B →+* R, (∀ i, h.comp (l i) = g i) ∧ h.comp χ = c

theorem le_l {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : I.map φ ≤ (I.map χ).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hf]

abbrev lq {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : A' ⧸ I.map φ →+* B ⧸ I.map χ :=
  Ideal.quotientMap (I.map χ) f (le_l φ χ f hf I)

def coneOf {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) :
    Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : ι => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))) :=
  WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom χ))) (fun i => yoneda.map (Spec.map (CommRingCat.ofHom (l i))))
    (fun i => by
      change yoneda.map _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom φ)) = _
      rw [← yoneda.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])

def SpecLim : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) (n : ℕ)
  (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ), IsCop φ χ l → Nonempty (IsLimit (coneOf φ χ l hl))

def TensCop : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (n : ℕ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ),
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ IsCop φ χ l

def QuotCop : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A), IsCop φ χ l →
    IsCop (qm φ I) (qm χ I) (fun i => lq φ χ (l i) (hl i) I)

theorem lq_hl {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A) (i : ι) :
    (lq φ χ (l i) (hl i) I).comp (qm φ I) = qm χ I := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [qm, lq, ← hl i]

theorem ysq {R S S' T : Type} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] (f : R →+* S) (g : S →+* T)
    (f' : R →+* S') (g' : S' →+* T) (h : g.comp f = g'.comp f') :
    yoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f)) =
      yoneda.map (Spec.map (CommRingCat.ofHom g')) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f')) := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, h]

theorem LevelsGen_of (hT : TensCop) (hQ : QuotCop) (hS : SpecLim) : LevelsGen := by
  intro A A' _ _ φ I p
  obtain ⟨B, _, χ, l, hl, hc, hcop⟩ := hT A A' φ (p.unop.len)
  refine ⟨B, inferInstance, χ, _, l, hl, hc, ?_⟩
  obtain ⟨L⟩ := hS A A' B φ χ _ l hl hcop
  obtain ⟨Lr⟩ := hS _ _ _ (qm φ I) (qm χ I) _ _ (lq_hl φ χ l hl I) (hQ A A' B φ χ l hl I hcop)
  let e : (cech (Spec.map (CommRingCat.ofHom φ))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of B)) := (limit.isLimit _).conePointUniqueUpToIso L
  let er : (cech (Spec.map (CommRingCat.ofHom (qm φ I)))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of (B ⧸ I.map χ))) := (limit.isLimit _).conePointUniqueUpToIso Lr
  refine ⟨Arrow.isoMk er e ?_⟩
  simp only [Arrow.mk_hom]
  apply L.hom_ext
  rintro (_|i)
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (qm χ I))) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr none
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L none
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ))
    rw [Category.assoc, Category.assoc, h2, ysq χ (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk I) (qm χ I) (qm_comp χ I).symm,
      ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_right]
    erw [WidePullback.lift_base]
    all_goals rfl
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (lq φ χ (l i) (hl i) I))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr (some i)
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L (some i)
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i)))
    rw [Category.assoc, Category.assoc, h2, ysq (l i) (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk (I.map φ))
      (lq φ χ (l i) (hl i) I) (Ideal.quotientMap_comp_mk _).symm, ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_left]
    erw [WidePullback.lift_π]
    all_goals rfl

end LateralTheory.E.LevelsGenPf
