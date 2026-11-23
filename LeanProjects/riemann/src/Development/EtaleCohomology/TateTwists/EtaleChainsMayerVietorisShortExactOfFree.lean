import Development.EtaleCohomology.TateTwists.EtaleMayerVietorisChainsShortExact

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleFreePresheafMayerVietorisShortExact : Prop :=
  ∀ (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g],
    Mono (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g))) ∧
    ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g)))
      (biprod.desc ((free R).map f) ((free R).map g)) w).Exact

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    ((chains R).map φ).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom =
      (chainsXIso R E p).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk p))) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := p) (i' := -(p:ℤ)) rfl
  have h2 : ((chains R).map φ).f (-(p:ℤ)) = (HomologicalComplex.extendMap ((chainsN R).map φ) ComplexShape.embeddingDownNat).f (-(p:ℤ)) := rfl
  rw [h2, h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i:ℤ) = n at h
  omega

theorem chainsXIso_nat' (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map φ).f (-(p : ℤ)) =
      (free R).map (φ.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← chainsXIso_nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem sq1 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    ((free R).map (pullbackObjIso f g (op (SimplexCategory.mk p))).inv ≫ (chainsXIso R (pullback f g) p).inv) ≫
      (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))).f (-(p:ℤ)) =
    biprod.lift ((free R).map (pullback.fst (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))))
        (-(free R).map (pullback.snd (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))))) ≫
      (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) := by
  rw [← cancel_mono (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_fst, chainsXIso_nat', ← Category.assoc, ← Functor.map_comp,
      pullbackObjIso_inv_comp_fst]
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
      chainsXIso_nat']
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← Category.assoc, ← Functor.map_comp, pullbackObjIso_inv_comp_snd]

theorem sq2 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) ≫
      (biprod.desc ((chains R).map f) ((chains R).map g)).f (-(p:ℤ)) =
    biprod.desc ((free R).map (f.app (op (SimplexCategory.mk p)))) ((free R).map (g.app (op (SimplexCategory.mk p)))) ≫
      (chainsXIso R E p).inv := by
  apply biprod.hom_ext'
  · have h1 : biprod.inl ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inl : (chains R).obj U ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inl_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inl_desc,
      chainsXIso_nat', biprod.inl_desc_assoc]
  · have h1 : biprod.inr ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inr : (chains R).obj V ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inr_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inr_desc,
      chainsXIso_nat', biprod.inr_desc_assoc]

theorem etale_chains_mayer_vietoris_short_exact_of_free (hfree : EtaleFreePresheafMayerVietorisShortExact) : EtaleMayerVietorisChainsShortExact := by
  intro R _ U V E f g hc
  obtain ⟨hf, hg, hep⟩ := hc
  have w : biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) ≫
      biprod.desc ((chains R).map f) ((chains R).map g) = 0 := by
    rw [biprod.lift_desc, ← Functor.map_comp, Preadditive.neg_comp, ← Functor.map_comp, pullback.condition]
    simp
  refine ⟨w, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : 0 < n
  · have h1 := chains_isZero R (pullback f g) n hn
    have h3 := chains_isZero R E n hn
    have h2 : IsZero ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n).obj
        ((chains R).obj U ⊞ (chains R).obj V)) :=
by
      have hU := chains_isZero R U n hn
      have hV := chains_isZero R V n hn
      refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ n)
      rw [IsZero.iff_id_eq_zero, ← biprod.total, hU.eq_of_tgt biprod.fst 0, hV.eq_of_tgt biprod.snd 0]
      simp
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h2) ?_ ?_
    · exact ⟨fun a b _ => h1.eq_of_tgt a b⟩
    · exact ⟨fun a b _ => h3.eq_of_src a b⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  obtain ⟨hmono, w', hex⟩ := hfree R (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))
  have hT := ShortComplex.ShortExact.mk' hex hmono (hep _)
  refine ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk ?e1 ?e2 ?e3 ?c1 ?c2
  case e1 =>
    refine ?_ ≪≫ (chainsXIso R _ p).symm
    exact (free R).mapIso (pullbackObjIso f g _).symm
  case e2 => exact biprod.mapIso (chainsXIso R U p).symm (chainsXIso R V p).symm ≪≫
      (HomologicalComplex.biprodXIso _ _ _).symm
  case e3 => exact (chainsXIso R E p).symm
  case c1 => exact sq1 R f g p
  case c2 => exact sq2 R f g p

end LateralTheory.EtaleFoundations
