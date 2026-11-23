import Development.EtaleCohomology.CohomologicalPurity.LeafOffContPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def OffContLoc : Prop := A1 → ∀ r : ℕ, OffContN r → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (x : Fin r → A) (f : A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span (Set.range x) * Ideal.span {f}) D s t n i

def OffContMV : Prop := A1 → LeafBd → LeafExc → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (I1 I2 : Ideal A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ i : ℤ,
  (∀ m, HtOffCont q φ I1 D s t m i) → (∀ m, HtOffCont q φ I2 D s t m i) →
  (∀ m, HtOffCont q φ (I1 * I2) D s t m i) → ∀ n : ℤ, HtOffCont q φ (I1 ⊔ I2) D s t n i

theorem off_sup (A : Type) [CommRing A] (I1 I2 : Ideal A) : off A (I1 ⊔ I2) = off A I1 ⊔ off A I2 := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I1 ⊔ I2 : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I1 : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus (I2 : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_sup, Set.compl_inter]

theorem off_mul (A : Type) [CommRing A] (I1 I2 : Ideal A) : off A (I1 * I2) = off A I1 ⊓ off A I2 := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I1 * I2 : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I1 : Set A))ᶜ ∩ (PrimeSpectrum.zeroLocus (I2 : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_mul, Set.compl_union]

theorem off_map_comp {A R R' : Type} [CommRing A] [CommRing R] [CommRing R'] (I : Ideal A) (g : A →+* R)
    (ψ : R →+* R') : off R' (I.map (ψ.comp g)) = Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ off R (I.map g) := by
  apply TopologicalSpace.Opens.ext
  ext p
  change ¬ (((I.map (ψ.comp g)) : Set R') ⊆ (show PrimeSpectrum R' from p).asIdeal) ↔
    ¬ (((I.map g) : Set R) ⊆ (PrimeSpectrum.comap ψ (show PrimeSpectrum R' from p)).asIdeal)
  rw [← Ideal.map_map, SetLike.coe_subset_coe, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap,
    PrimeSpectrum.comap_asIdeal]

theorem span_range_fin_succ {A : Type} [CommRing A] {r : ℕ} (x : Fin (r + 1) → A) :
    Ideal.span (Set.range x) = Ideal.span (Set.range (fun k : Fin r => x k.castSucc)) ⊔ Ideal.span {x (Fin.last r)} := by
  rw [range_fin_succ, Ideal.span_union]

theorem offContStep_of (hL : OffContLoc) (hM : OffContMV) : OffContStep := by
  intro a1 a4 b1 bd ex hb r ih q A B _ _ φ x hq J _ _ D s t hc he n i
  rw [span_range_fin_succ]
  exact hM a1 bd ex q φ _ _ hq J D s t hc he i
    (fun m => ih q φ _ hq J D s t hc he m i)
    (fun m => hb a1 a4 b1 q φ _ hq J D s t hc he m i)
    (fun m => hL a1 r ih q φ _ _ hq J D s t hc he m i) n

def excMap {X : Scheme.{0}} (U V : X.Opens) :
    opn (V.ι ⁻¹ᵁ U) ⟶ opn ((U ⊔ V).ι ⁻¹ᵁ U) :=
  opnMap (X.homOfLE (le_sup_right : V ≤ U ⊔ V)) _ _ (by
    intro x hx
    change ((U ⊔ V).ι).base ((X.homOfLE (le_sup_right : V ≤ U ⊔ V)).base x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact hx)

def OffExcMV : Prop := A1 → LeafExc → ∀ (q : ℕ) (X : Scheme.{0}) (U V : X.Opens), Exc q (excMap U V)

def OffChaseMV : Prop := LeafBd → (∀ (q : ℕ) (X : Scheme.{0}) (U V : X.Opens), Exc q (excMap U V)) →
  ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (I1 I2 : Ideal A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ i : ℤ,
  (∀ m, HtOffCont q φ I1 D s t m i) → (∀ m, HtOffCont q φ I2 D s t m i) →
  (∀ m, HtOffCont q φ (I1 * I2) D s t m i) → ∀ n : ℤ, HtOffCont q φ (I1 ⊔ I2) D s t n i

theorem offContMV_of (hE : OffExcMV) (hC : OffChaseMV) : OffContMV := by
  intro a1 bd ex q A B _ _ φ I1 I2 hq J _ _ D s t hc he i h1 h2 h12 n
  exact hC bd (fun q X U V => hE a1 ex q X U V) q φ I1 I2 hq J D s t hc he i h1 h2 h12 n

theorem offContStep_of' (hL : OffContLoc) (hE : OffExcMV) (hC : OffChaseMV) : OffContStep :=
  offContStep_of hL (offContMV_of hE hC)

theorem offExcMV : OffExcMV := by
  intro a1 ex q X U V
  let U0 : (U ⊔ V).toScheme.Opens := (U ⊔ V).ι ⁻¹ᵁ U
  let C : TopologicalSpace.Closeds (U ⊔ V).toScheme := ⟨(U0 : Set _)ᶜ, U0.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let f := X.homOfLE (le_sup_right : V ≤ U ⊔ V)
  have hr : Set.range I.subschemeι = (U0 : Set _)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hsub : Set.range I.subschemeι ⊆ Set.range f := by
    rw [hr, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    intro x hx
    have hw : ((U ⊔ V).ι x) ∈ U ⊔ V := x.2
    rcases (TopologicalSpace.Opens.mem_sup.mp hw) with h1 | h2
    · exact absurd h1 hx
    · exact h2
  have h : V.ι ⁻¹ᵁ U = f ⁻¹ᵁ U0 := by
    apply TopologicalSpace.Opens.ext
    ext x
    change V.ι x ∈ U ↔ (U ⊔ V).ι (f x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  have hU : (U0 : Set _) = (Set.range I.subschemeι)ᶜ := by rw [hr, compl_compl]
  exact ex a1 q f (IsOpenImmersion.lift f I.subschemeι hsub) I.subschemeι
    (IsOpenImmersion.isPullback_lift_id I.subschemeι f hsub) (V.ι ⁻¹ᵁ U) U0 hU h

section DiagramChase₂
variable (q : ℕ) {J : Type} [SmallCategory J] (F : Jᵒᵖ ⥤ Arrow Spc) (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j))

def ContL (n i : ℤ) : Prop :=
  (∀ x : Ht q P.left n i, ∃ j, ∃ y, pull _ (c j).left (tw q i) n y = x) ∧
  ∀ j y, pull _ (c j).left (tw q i) n y = 0 → ∃ (k : J) (f : j ⟶ k), pull _ (F.map f.op).left (tw q i) n y = 0

def ContR (n i : ℤ) : Prop :=
  (∀ x : Ht q P.right n i, ∃ j, ∃ y, pull _ (c j).right (tw q i) n y = x) ∧
  ∀ j y, pull _ (c j).right (tw q i) n y = 0 → ∃ (k : J) (f : j ⟶ k), pull _ (F.map f.op).right (tw q i) n y = 0

def ContS (n i : ℤ) : Prop :=
  (∀ x : Hs q P n i, ∃ j, ∃ y, Hs.pull q (c j) n i y = x) ∧
  ∀ j y, Hs.pull q (c j) n i y = 0 → ∃ (k : J) (f : j ⟶ k), Hs.pull q (F.map f.op) n i y = 0

end DiagramChase₂

def PairFiveS : Prop := LeafBd → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
  (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)), (∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j) →
  (∀ j, Mono (F.obj (op j)).hom) → Mono P.hom → ∀ i : ℤ, (∀ m, ContL q F P c m i) → (∀ m, ContR q F P c m i) →
  ∀ n, ContS q F P c n i

def PairFiveR : Prop := LeafBd → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
  (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)), (∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j) →
  (∀ j, Mono (F.obj (op j)).hom) → Mono P.hom → ∀ i : ℤ, (∀ m, ContL q F P c m i) → (∀ m, ContS q F P c m i) →
  ∀ n, ContR q F P c n i

def OffChaseGeo : Prop := PairFiveS → PairFiveR → OffChaseMV

theorem etale_complement_continuity_induction_of_five_lemma_inputs (hL : OffContLoc) (hS : PairFiveS) (hR : PairFiveR) (hG : OffChaseGeo) : OffContStep :=
  offContStep_of' hL offExcMV (hG hS hR)

theorem dbl.inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

theorem dbl.map_comp {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) :
    dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  apply pushout.hom_ext
  · change dbl.inl P'' ≫ dbl.map (φ ≫ ψ) = dbl.inl P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inl_map, ← Category.assoc, dbl.inl_map, Category.assoc, dbl.inl_map, ← Category.assoc]; rfl
  · change dbl.inr P'' ≫ dbl.map (φ ≫ ψ) = dbl.inr P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, ← Category.assoc]; rfl

theorem Hs.pullComp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (φ ≫ ψ)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map φ) _ n (GlobalTheory.EtC.pull _ (dbl.map ψ) _ n x.1)
  rw [dbl.map_comp, GlobalTheory.EtC.pull_comp]

theorem Hs.fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = GlobalTheory.EtC.pull _ φ.right (tw q i) n (Hs.fgt q P n i x) := by
  change GlobalTheory.EtC.pull _ (dbl.inl P') _ n (GlobalTheory.EtC.pull _ (dbl.map φ) _ n x.1) =
    GlobalTheory.EtC.pull _ φ.right _ n (GlobalTheory.EtC.pull _ (dbl.inl P) _ n x.1)
  rw [← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, dbl.inl_map]

theorem pairFiveR_surj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i n : ℤ) (hL : ContL q F P c n i)
    (hS : ∀ m, ContS q F P c m i) (x : Ht q P.right n i) :
    ∃ j, ∃ y, pull _ (c j).right (tw q i) n y = x := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  obtain ⟨j, y, hy⟩ := hL.1 (pull _ P.hom (tw q i) n x)
  have hδ : δ q P n i (pull _ P.hom (tw q i) n x) = 0 := ((hex q P hP n i).2.1 _).mpr ⟨x, rfl⟩
  have h1 : Hs.pull q (c j) _ _ (δ q (F.obj (op j)) n i y) = 0 := by
    rw [hnat q _ _ (c j) hP (hm j) n i y, hy, hδ]
  obtain ⟨k, f, hk⟩ := (hS (n + 1)).2 j _ h1
  rw [hnat q _ _ (F.map f.op) (hm k) (hm j)] at hk
  obtain ⟨z, hz⟩ := ((hex q _ (hm k) n i).2.1 _).mp hk
  have hres : pull _ P.hom (tw q i) n (x - pull _ (c k).right (tw q i) n z) = 0 := by
    rw [map_sub, ← GlobalTheory.EtC.pull_comp, ← Arrow.w (c k), GlobalTheory.EtC.pull_comp, hz, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, hc, hy, sub_self]
  obtain ⟨s, hs⟩ := ((hex q P hP n i).1 _).mp hres
  obtain ⟨l, w, hw⟩ := (hS n).1 s
  refine ⟨IsFiltered.max k l, pull _ (F.map (IsFiltered.leftToMax k l).op).right (tw q i) n z +
    pull _ (F.map (IsFiltered.rightToMax k l).op).right (tw q i) n (Hs.fgt q _ n i w), ?_⟩
  rw [map_add, ← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_right, ← Arrow.comp_right, hc, hc, ← Hs.fgt_pull, hw, hs,
    add_sub_cancel]

theorem pairFiveR_inj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hS : ∀ m, ContS q F P c m i) (m : ℤ) (j : J) (y : Ht q (F.obj (op j)).right (m + 1) i)
    (hy : pull _ (c j).right (tw q i) (m + 1) y = 0) :
    ∃ (k : J) (f : j ⟶ k), pull _ (F.map f.op).right (tw q i) (m + 1) y = 0 := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  have h0 : pull _ (c j).left (tw q i) (m + 1) (pull _ (F.obj (op j)).hom (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, Arrow.w (c j), GlobalTheory.EtC.pull_comp, hy, map_zero]
  obtain ⟨k, f, hk⟩ := (hL (m + 1)).2 j _ h0
  have hk' : pull _ (F.obj (op k)).hom (tw q i) (m + 1) (pull _ (F.map f.op).right (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, ← Arrow.w (F.map f.op), GlobalTheory.EtC.pull_comp, hk]
  obtain ⟨s, hs⟩ := ((hex q _ (hm k) (m + 1) i).1 _).mp hk'
  have hv : Hs.fgt q P (m + 1) i (Hs.pull q (c k) _ _ s) = 0 := by
    rw [Hs.fgt_pull, hs, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_right, hc, hy]
  obtain ⟨u, hu⟩ := ((hex q P hP m i).2.2 _).mp hv
  obtain ⟨l, a, ha⟩ := (hL m).1 u
  rw [← ha, ← hnat q _ _ (c l) hP (hm l)] at hu
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  have hd : Hs.pull q (c M) _ _ (Hs.pull q (F.map g1.op) _ _ s - Hs.pull q (F.map g2.op) _ _ (δ q _ m i a)) = 0 := by
    rw [map_sub, ← Hs.pullComp, ← Hs.pullComp, hc, hc, hu, sub_self]
  obtain ⟨p, h, hp⟩ := (hS (m + 1)).2 M _ hd
  rw [map_sub, sub_eq_zero] at hp
  have hp' : Hs.pull q (F.map (g1 ≫ h).op) _ _ s = δ q _ m i (pull _ (F.map (g2 ≫ h).op).left (tw q i) m a) := by
    rw [op_comp, F.map_comp, Hs.pullComp, hp, ← Hs.pullComp, ← F.map_comp, ← op_comp, hnat q _ _ _ (hm p) (hm l)]
  refine ⟨p, f ≫ g1 ≫ h, ?_⟩
  have e : F.map (f ≫ g1 ≫ h).op = F.map (g1 ≫ h).op ≫ F.map f.op := by rw [op_comp, F.map_comp]
  rw [e, Arrow.comp_right, GlobalTheory.EtC.pull_comp, ← hs, ← Hs.fgt_pull, hp']
  exact ((hex q _ (hm p) m i).2.2 _).mpr ⟨_, rfl⟩

theorem pairFiveR : PairFiveR := by
  intro bd q J _ _ F P c hc hm hP i hL hS n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact ⟨pairFiveR_surj bd q F P c hc hm hP i _ (hL _) hS,
    fun j y hy => pairFiveR_inj bd q F P c hc hm hP i hL hS m j y hy⟩

theorem etale_complement_continuity_induction_of_localization_and_pair_lemmas (hL : OffContLoc) (hS : PairFiveS) (hG : OffChaseGeo) : OffContStep :=
  etale_complement_continuity_induction_of_five_lemma_inputs hL hS pairFiveR hG

end LateralTheory.CohomologicalPurity
