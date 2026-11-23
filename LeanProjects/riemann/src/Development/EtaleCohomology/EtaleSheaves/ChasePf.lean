import Development.EtaleCohomology.EtaleSheaves.DiagramChase

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.StepSPf

namespace LateralTheory.E.ChasePf

theorem pp_comp {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (hfg : f ≫ g = h) (y : H R (sch.obj C) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map h) F n y := by
  rw [← pull_comp, ← Functor.map_comp, hfg]

theorem pp_id {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A : Scheme.{0}} {f : A ⟶ A} (hf : f = 𝟙 A)
    (y : H R (sch.obj A) F n) : pull R (sch.map f) F n y = y := by
  rw [hf, CategoryTheory.Functor.map_id, pull_id]

def psi {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) : pullback A.ι B.ι ≅ C.toScheme :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst A.ι B.ι ≫ A.ι) C.ι (by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hC]; rfl)

@[reassoc (attr := simp)]
theorem psi_hom_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).hom ≫ C.ι = pullback.fst A.ι B.ι ≫ A.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc]
theorem psi_hom_snd {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).hom ≫ C.ι = pullback.snd A.ι B.ι ≫ B.ι := by
  rw [psi_hom_fst, pullback.condition]

@[reassoc (attr := simp)]
theorem psi_inv_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.fst A.ι B.ι ≫ A.ι = C.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc (attr := simp)]
theorem psi_inv_snd {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.snd A.ι B.ι ≫ B.ι = C.ι := by
  rw [← pullback.condition, psi_inv_fst]

theorem cover2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) (hAB : A ⊔ B = ⊤) :
    Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ A)).ι ∪ Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ B)).ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  refine Set.eq_univ_of_forall fun y => ?_
  have : ψ.base (φ.base y) ∈ A ⊔ B := by rw [hAB]; trivial
  simpa using this

theorem inf2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) :
    φ ⁻¹ᵁ (ψ ⁻¹ᵁ (A ⊓ B)) = φ ⁻¹ᵁ (ψ ⁻¹ᵁ A) ⊓ φ ⁻¹ᵁ (ψ ⁻¹ᵁ B) := by
  ext; simp

section
variable {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens)

abbrev rL {k : J} (f : k ⟶ j0) : (c.π.app j0 ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, c.w])

abbrev rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    (D.map f' ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map f' ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, h])

theorem rL_rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    rL D c j0 W f' ≫ rT D j0 W g f f' h = rL D c j0 W f := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp [rL, rT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

theorem rT_rT {l' l k : J} (g' : l' ⟶ l) (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (f'' : l' ⟶ j0)
    (h : g ≫ f = f') (h' : g' ≫ f' = f'') :
    rT D j0 W g' f' f'' h' ≫ rT D j0 W g f f' h = rT D j0 W (g' ≫ g) f f'' (by rw [Category.assoc, h, h']) := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp [rT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

end

theorem pp3' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' C' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g' ≫ k') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n (pull R (sch.map k') F n y)) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp3 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {l : A ⟶ E} (h : f ≫ g ≫ k = l) (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) = pull R (sch.map l) F n y := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp2' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp32 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp24 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' C' E' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E'} {l' : E' ⟶ E} (h : f ≫ g = f' ≫ g' ≫ k' ≫ l')
    (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n
      (pull R (sch.map k') F n (pull R (sch.map l') F n y))) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

macro "meq" : tactic => `(tactic| first
  | (apply pullback.hom_ext <;> rw [← cancel_mono (Scheme.Opens.ι _)] <;>
      simp [rL, rT, Scheme.Hom.resLE_comp_ι_assoc, pullback.condition_assoc, ← Functor.map_comp_assoc, Cone.w_assoc, Cone.w, pullback.map])
  | (rw [← cancel_mono (Scheme.Opens.ι _)];
      simp [rL, rT, Scheme.Hom.resLE_comp_ι_assoc, pullback.condition_assoc, ← Functor.map_comp_assoc, Cone.w_assoc, Cone.w, pullback.map]))

theorem Chase_of : DiagramChase₂ := by
  intro hH hmv q J _ _ D c hc ha hcs hqs hu j0 X e U V hUV pU pV pW n i
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  intro x
  obtain ⟨δ, hex, hnat⟩ := hmv hH (ZMod q) (tw q i)
  have cov : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι ∪ Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι = Set.univ :=
    fun φ => cover2 φ e.hom U V hUV
  have hinf : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      φ ⁻¹ᵁ (e.hom ⁻¹ᵁ (U ⊓ V)) = φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U) ⊓ φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V) :=
    fun φ => inf2 φ e.hom U V

  obtain ⟨k1, f1, a1, ha1⟩ := (pU (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x)
  obtain ⟨k2, f2, b1, hb1⟩ := (pV (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x)
  obtain ⟨k3, g1, g2, hg⟩ := IsCofiltered.cospan f1 f2

  obtain ⟨a2, ha2d⟩ : ∃ a2, a2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g1 f1 (g1 ≫ f1) rfl)) (tw q i) (m + 1) a1 :=
    ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b2, b2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g2 f2 (g1 ≫ f1) hg.symm)) (tw q i) (m + 1) b1 :=
    ⟨_, rfl⟩
  have ha2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1))) (tw q i) (m + 1) a2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x := by
    rw [ha2d, pp_comp (rL_rT D c j0 _ g1 f1 _ rfl)]; exact ha1
  have hb2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1))) (tw q i) (m + 1) b2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x := by
    rw [hb2d, pp_comp (rL_rT D c j0 _ g2 f2 _ hg.symm)]; exact hb1

  obtain ⟨dC, hdC⟩ : ∃ dC, dC = pull _ (sch.map (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv) (tw q i) (m + 1)
      (pull _ (sch.map (pullback.fst _ _)) _ _ a2 - pull _ (sch.map (pullback.snd _ _)) _ _ b2) := ⟨_, rfl⟩
  have hd : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) (g1 ≫ f1))) (tw q i) (m + 1) dC = 0 := by
    rw [hdC, map_sub, map_sub,
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.fst _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1)) (by meq),
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.snd _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1)) (by meq),
      ha2, hb2, pp3 (psi_inv_fst _ _ _ _), pp3 (psi_inv_snd _ _ _ _), sub_self]
  obtain ⟨k4, g4, hk4⟩ := (pW (m + 1) i).2 k3 (g1 ≫ f1) dC hd

  obtain ⟨a3, ha3d⟩ : ∃ a3, a3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) a2 := ⟨_, rfl⟩
  obtain ⟨b3, hb3d⟩ : ∃ b3, b3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) b2 := ⟨_, rfl⟩
  have hab : pull _ (sch.map (pullback.fst _ _)) _ _ a3 = pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
      (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 := by
    have key : pull _ (sch.map (pullback.fst _ _)) _ _ a3 - pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
        (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 =
        pull _ (sch.map (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom) _ _
          (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl)) _ _ dC) := by
      have E3 : (pullback.fst (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.fst (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by meq
      have E4 : (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.snd (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by meq
      rw [hdC, ha3d, hb3d]; simp only [map_sub]; rw [pp24 E3, pp24 E4]
    rw [hk4, map_zero] at key
    exact sub_eq_zero.mp key
  obtain ⟨xk, hxa, hxb⟩ := (hex (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (cov _) (m + 1)).1 a3 b3 hab

  obtain ⟨x', hx'⟩ : ∃ x' : Ht q (sch.obj c.pt) (m + 1) i, x' = x -
      (show Ht q (sch.obj c.pt) (m + 1) i from pull _ (sch.map (c.π.app k4)) (tw q i) (m + 1) xk) := ⟨_, rfl⟩
  have h1 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) (by simp [rL]), hxa, ha3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), ha2, sub_self]
  have h2 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) (by simp [rL]), hxb, hb3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), hb2, sub_self]
  obtain ⟨w, hw⟩ := ((hex (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) m).2.2 x').mp
    ⟨h1, h2⟩

  obtain ⟨k5, f5, w5, hw5⟩ := (pW m i).1 (pull _ (sch.map (psi _ _ _ (hinf (c.π.app j0))).inv) _ _ w)
  obtain ⟨k6, h4, h5, hh⟩ := IsCofiltered.cospan (g4 ≫ g1 ≫ f1) f5
  obtain ⟨w6, hw6⟩ : ∃ w6, w6 = pull _ (sch.map (psi _ _ _ (hinf (D.map (h4 ≫ g4 ≫ g1 ≫ f1)))).hom) (tw q i) m
      (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) h5 f5 (h4 ≫ g4 ≫ g1 ≫ f1) hh.symm)) _ _ w5) := ⟨_, rfl⟩
  have hn := hnat (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) (cov _)
    (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6)
    (by simp [rL]) (by simp [rL]) m w6
  have hpb : pull _ (sch.map (pullback.map _ _ _ _ (rL D c j0 (e.hom ⁻¹ᵁ U) (h4 ≫ g4 ≫ g1 ≫ f1))
      (rL D c j0 (e.hom ⁻¹ᵁ V) (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6) (by simp [rL]) (by simp [rL]))) (tw q i) m w6 = w := by
    rw [hw6, pp32 (f' := (psi _ _ _ (hinf (c.π.app j0))).hom) (g' := rL D c j0 _ f5) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp only [Category.assoc, rT, rL, Scheme.Hom.resLE_comp_ι, psi_hom_fst_assoc]
      erw [pullback.lift_fst_assoc]
      simp [Scheme.Hom.resLE_comp_ι_assoc, Cone.w]), hw5,
      pp_comp (Iso.hom_inv_id _), pp_id rfl]
  refine ⟨k6, δ _ _ m w6 + pull _ (sch.map (D.map h4)) _ _ xk, ?_⟩
  rw [map_add, ← hn, hpb, hw, pp_comp (c.w h4), hx', sub_add_cancel]

end LateralTheory.E.ChasePf
