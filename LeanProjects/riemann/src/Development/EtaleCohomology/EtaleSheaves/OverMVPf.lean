import Development.EtaleCohomology.EtaleSheaves.InjStepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf LateralTheory.E.InjStepPf

namespace LateralTheory.E.OverMVPf

variable {X S : Scheme.{0}}

@[reassoc]
theorem resO_fst (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.fst p U.ι = pullback.fst p V.ι := by
  simp only [resO, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem resO_snd (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.snd p U.ι ≫ U.ι = pullback.snd p V.ι ≫ V.ι := by
  simp only [resO, pullback.map, pullback.lift_snd_assoc, Category.assoc, Scheme.homOfLE_ι]

instance resO_open (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : IsOpenImmersion (resO p h) := by
  have : IsOpenImmersion (resO p h ≫ pullback.fst p U.ι) := by rw [resO_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst p U.ι)

theorem range_sub {T : Scheme.{0}} (U : S.Opens) (a : T ⟶ U) :
    Set.range (a ≫ U.ι) ⊆ (U : Set S) := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
  exact ⟨_, rfl⟩

theorem cover (p : X ⟶ S) (V W : S.Opens) :
    Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) ∪ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : p (pullback.fst p (V ⊔ W).ι y) ∈ ((V ⊔ W : S.Opens) : Set S) := by
    have := range_sub (V ⊔ W) (pullback.snd p (V ⊔ W).ι) ⟨y, rfl⟩
    rwa [← pullback.condition, Scheme.Hom.comp_apply] at this
  have inj := (pullback.fst p (V ⊔ W).ι).isOpenEmbedding.injective
  rcases hy with hV | hW
  · obtain ⟨s, hs⟩ : p (pullback.fst p (V ⊔ W).ι y) ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := V.ι) _ s hs.symm
    left; refine ⟨z, inj ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hz]
  · obtain ⟨s, hs⟩ : p (pullback.fst p (V ⊔ W).ι y) ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := W.ι) _ s hs.symm
    right; refine ⟨z, inj ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hz]

abbrev PP (p : X ⟶ S) (V W : S.Opens) : Scheme.{0} :=
  pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W))

abbrev g0 (p : X ⟶ S) (V W : S.Opens) : PP p V W ⟶ S := pullback.fst _ _ ≫ pullback.fst p V.ι ≫ p

theorem overOpenPullbackStructureMap_eq_via_left_open (p : X ⟶ S) (V W : S.Opens) : g0 p V W = pullback.fst _ _ ≫ pullback.snd p V.ι ≫ V.ι := by
  rw [g0, pullback.condition]

theorem overOpenPullbackStructureMap_eq_via_right_open (p : X ⟶ S) (V W : S.Opens) : g0 p V W = pullback.snd _ _ ≫ pullback.snd p W.ι ≫ W.ι := by
  rw [g0, ← pullback.condition, ← resO_fst_assoc p (le_sup_left : V ≤ V ⊔ W), pullback.condition_assoc, resO_fst_assoc]

theorem overOpenPullbackStructureMap_range_subset_inter (p : X ⟶ S) (V W : S.Opens) :
    Set.range (g0 p V W) ⊆ Set.range (V ⊓ W).ι := by
  rw [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf]
  intro s hs
  refine ⟨?_, ?_⟩
  · rw [overOpenPullbackStructureMap_eq_via_left_open, ← Category.assoc] at hs; exact range_sub V _ hs
  · rw [overOpenPullbackStructureMap_eq_via_right_open, ← Category.assoc] at hs; exact range_sub W _ hs

def kk (p : X ⟶ S) (V W : S.Opens) : PP p V W ⟶ overO p (V ⊓ W) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst p V.ι) (IsOpenImmersion.lift (V ⊓ W).ι (g0 p V W) (overOpenPullbackStructureMap_range_subset_inter p V W))
    (by rw [IsOpenImmersion.lift_fac, Category.assoc])

def ee (p : X ⟶ S) (V W : S.Opens) : overO p (V ⊓ W) ⟶ PP p V W :=
  pullback.lift (resO p (inf_le_left : V ⊓ W ≤ V)) (resO p (inf_le_right : V ⊓ W ≤ W))
    (by rw [resO_comp, resO_comp])

@[reassoc]
theorem kk_fst' (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ pullback.fst p (V ⊓ W).ι = pullback.fst _ _ ≫ pullback.fst p V.ι := by
  simp only [kk, pullback.lift_fst]

theorem kk_snd' (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ pullback.snd p (V ⊓ W).ι ≫ (V ⊓ W).ι = g0 p V W := by
  simp only [kk, pullback.lift_snd_assoc, IsOpenImmersion.lift_fac]

theorem kk_l (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ resO p (inf_le_left : V ⊓ W ≤ V) = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, resO_fst, kk_fst']
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, resO_snd, kk_snd', overOpenPullbackStructureMap_eq_via_left_open, Category.assoc]

theorem kk_r (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ resO p (inf_le_right : V ⊓ W ≤ W) = pullback.snd _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, resO_fst, kk_fst', ← resO_fst p (le_sup_left : V ≤ V ⊔ W), pullback.condition_assoc, resO_fst]
  · rw [← cancel_mono W.ι, Category.assoc, Category.assoc, resO_snd, kk_snd', overOpenPullbackStructureMap_eq_via_right_open, Category.assoc]

theorem kk_ee (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ ee p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ee, pullback.lift_fst, kk_l, Category.id_comp]
  · rw [Category.assoc, ee, pullback.lift_snd, kk_r, Category.id_comp]

theorem ee_kk (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ kk p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kk_fst', ee, pullback.lift_fst_assoc, resO_fst, Category.id_comp]
  · rw [← cancel_mono (V ⊓ W).ι, Category.assoc, Category.assoc, kk_snd', g0, ee, pullback.lift_fst_assoc,
      resO_fst_assoc, pullback.condition, Category.id_comp]

theorem ee_fst (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ pullback.fst _ _ = resO p (inf_le_left : V ⊓ W ≤ V) := by
  simp only [ee, pullback.lift_fst]

theorem ee_snd (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ pullback.snd _ _ = resO p (inf_le_right : V ⊓ W ≤ W) := by
  simp only [ee, pullback.lift_snd]

@[reassoc]
theorem fO_fst {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.fst p U.ι = pullback.fst (f ≫ p) U.ι ≫ f := by
  simp only [fO, pullback.map, pullback.lift_fst]

@[reassoc]
theorem fO_snd {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.snd p U.ι = pullback.snd (f ≫ p) U.ι := by
  simp only [fO, pullback.map, pullback.lift_snd, Category.comp_id]

theorem kk_nat {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (V W : S.Opens) :
    kk (f ≫ p) V W ≫ fO f p (V ⊓ W) = pullback.map _ _ _ _ (fO f p V) (fO f p W) (fO f p (V ⊔ W))
      (fO_res f p le_sup_left) (fO_res f p le_sup_right) ≫ kk p V W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, fO_fst, kk_fst'_assoc, kk_fst', pullback.lift_fst_assoc, Category.assoc, fO_fst]
  · rw [← cancel_mono (V ⊓ W).ι, Category.assoc, Category.assoc, Category.assoc, Category.assoc, fO_snd_assoc, kk_snd',
      kk_snd', g0, g0, pullback.lift_fst_assoc, Category.assoc, fO_fst_assoc]

theorem OverMV_of : OverMV := by
  intro hM hH q Y X S f p i m V W
  obtain ⟨δ, hex, hnat⟩ := hM hH (ZMod q) (tw q i)
  have cX := cover p V W
  have cY := cover (f ≫ p) V W
  refine ⟨(δ (resO p le_sup_left) (resO p le_sup_right) m).comp (pull _ (sch.map (kk p V W)) _ m),
    (δ (resO (f ≫ p) le_sup_left) (resO (f ≫ p) le_sup_right) m).comp (pull _ (sch.map (kk (f ≫ p) V W)) _ m),
    ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    obtain ⟨w', hw'⟩ := ((hex _ _ cX m).2.2 x).1 ⟨h1, h2⟩
    refine ⟨pull _ (sch.map (ee p V W)) _ _ w', ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, ← Functor.map_comp, kk_ee, CategoryTheory.Functor.map_id, pull_id, hw']
  · intro a b
    rw [AddMonoidHom.comp_apply, map_sub, ← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, kk_l, kk_r]
    exact ((hex _ _ cX m).2.1 _).2 ⟨a, b, rfl⟩
  · intro w hw
    obtain ⟨a, b, hab⟩ := ((hex _ _ cY m).2.1 _).1 hw
    refine ⟨a, b, ?_⟩
    have e : w = pull _ (sch.map (ee (f ≫ p) V W)) _ _ (pull _ (sch.map (kk (f ≫ p) V W)) _ _ w) := by
      rw [← pull_comp, ← Functor.map_comp, ee_kk, CategoryTheory.Functor.map_id, pull_id]
    rw [e, hab, map_sub, ← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, ee_fst, ee_snd]
  · intro w
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← pull_comp, ← Functor.map_comp, kk_nat, Functor.map_comp,
      pull_comp, hnat _ _ _ _ cY cX]

end LateralTheory.E.OverMVPf
