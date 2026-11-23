import Development.EtaleCohomology.EtaleSheaves.ZariskiLocalCech

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigmaProof

abbrev cov {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    (∐ fun j => (V j).toScheme) ⟶ O.toScheme :=
  Sigma.desc fun j => X.homOfLE (hV j)

theorem pre_le {Y X : Scheme.{0}} (g : Y ⟶ X) {A B : X.Opens} (h : A ≤ B) : g ⁻¹ᵁ A ≤ g ⁻¹ᵁ B :=
  fun _ hx => h hx

theorem sq_cov {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Limits.Sigma.map (fun j => g ∣_ V j) ≫ cov O V hV = cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) ≫ g ∣_ O := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [← cancel_mono O.ι]
  simp [cov, morphismRestrict_ι]

theorem cov_surj {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
    (hc : O ≤ ⨆ j, V j) : Surjective (cov O V hV) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  refine Set.eq_univ_iff_forall.2 fun x => ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc x.2)
  refine Set.mem_iUnion.2 ⟨j, ⟨⟨x.1, hj⟩, ?_⟩⟩
  apply Subtype.ext
  exact congr($(X.homOfLE_ι (hV j)) ⟨x.1, hj⟩)

instance cov_smooth {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Smooth (cov O V hV) :=
  haveI : IsZariskiLocalAtSource @Smooth.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := RingHom.Smooth)
  IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) fun _ => inferInstance

def arr {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (yoneda.map (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)))) ⟶
      Arrow.mk (yoneda.map (cov O V hV)) :=
  Arrow.homMk (yoneda.map (Limits.Sigma.map fun j => g ∣_ V j)) (yoneda.map (g ∣_ O))
    (by simp only [Arrow.mk_hom]; rw [← Functor.map_comp, ← Functor.map_comp, sq_cov g O V hV])

def LevelIso : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk ((Arrow.mapCechNerve (arr g O V hV)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))))

section
variable {R : Type} [CommRing R] {F : Shv R}

theorem eqv_of_arrowIso {E E' E₁ E₁' : Spc} {f : E ⟶ E'} {f' : E₁ ⟶ E₁'} (e : Arrow.mk f ≅ Arrow.mk f')
    (h : Eqv R f' F) : Eqv R f F := by
  have w : f = e.hom.left ≫ f' ≫ e.inv.right := by
    have := Arrow.w e.hom
    simp only [Arrow.mk_hom] at this
    rw [← Category.assoc, this, Category.assoc, ← Arrow.comp_right, e.hom_inv_id, Arrow.id_right]
    simp
  rw [w]
  exact ZariskiLocalCech.eqv_comp (ZariskiLocalCech.eqv_iso _) (ZariskiLocalCech.eqv_comp h (ZariskiLocalCech.eqv_iso _))

theorem eqv_of_comp_left {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  have := hfg n
  rw [h] at this
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 this

theorem eqv_of_comp_right {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hg : Eqv R g F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R f F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  have := hfg n
  rw [h] at this
  exact (Function.Bijective.of_comp_iff _ (hg n)).1 this

end

theorem CechSigma_of (hL : LevelIso) : ZariskiLocalCech.CechSigma := by
  unfold LevelIso at hL
  intro hH R _ F Y X g O ι V hV hc hn
  obtain ⟨_, hA2, hA3, -⟩ := hH
  have hc' : g ⁻¹ᵁ O ≤ ⨆ j, g ⁻¹ᵁ V j := by
    rw [← Scheme.Hom.preimage_iSup]; exact pre_le g hc
  have := cov_surj O V hV hc
  have := cov_surj (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) hc'
  have e1 : Eqv R (cechAug (cov O V hV)) F := hA2 R _ F
  have e2 : Eqv R (cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)))) F := hA2 R _ F
  have e3 : Eqv R (Arrow.mapCechNerve (arr g O V hV)) F := by
    refine hA3 R _ F fun m => ?_
    obtain ⟨e⟩ := hL g O V hV m.unop.len
    have e' : Arrow.mk (disc.map ((Arrow.mapCechNerve (arr g O V hV)).app m)) ≅
        Arrow.mk (sch.map (Limits.Sigma.map fun j : Fin (m.unop.len + 1) → ι => g ∣_ (⨅ k, V (j k)))) :=
      (disc.mapArrow).mapIso e
    exact eqv_of_arrowIso e' (hn _)
  have w : Arrow.mapCechNerve (arr g O V hV) ≫ cechAug (cov O V hV) =
      cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ≫ sch.map (g ∣_ O) := by
    have h := (Arrow.mapAugmentedCechNerve (arr g O V hV)).w
    exact h
  have h4 : Eqv R (cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ≫ sch.map (g ∣_ O)) F := by
    rw [← w]; exact ZariskiLocalCech.eqv_comp e3 e1
  exact eqv_of_comp_left e2 h4

end LateralTheory.E.CechSigmaProof
