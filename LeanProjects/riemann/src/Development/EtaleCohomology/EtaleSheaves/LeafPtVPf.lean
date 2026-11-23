import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafPtVPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling
  LateralTheory.E.SecondDegreeKilling.Comp LateralTheory.E.SecondDegreeKilling.Nbhd

theorem isZero_sec_empty (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    IsZero (F.obj.obj (op X)) :=
  (Sheaf.isTerminalOfBotCover F X (Scheme.bot_mem_grothendieckTopology (P := @Etale) X)).isZero

theorem isZero_free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext1
  ext1 U
  by_cases hU : IsEmpty U.unop
  · exact (isZero_sec_empty R ((free R).obj (yoneda.obj X)) U.unop).eq_of_tgt _ _
  · have hE : IsEmpty (ULift.{1} (unop U ⟶ X)) := ⟨fun f => by
      obtain ⟨x⟩ := not_isEmpty_iff.1 hU; exact IsEmpty.false (f.down.base x)⟩
    haveI : Subsingleton ↑(((freeP R).obj (yoneda.obj X)).obj U) := by
      change Subsingleton (ULift.{1} (unop U ⟶ X) →₀ ULift.{1} R); infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

theorem isZero_chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases p with _ | k
    · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) 0)
    · exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro j; change -(j : ℤ) ≠ (k : ℤ) + 1; omega)
  · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) p)

theorem isIso_inr (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (hK : ∀ n, IsZero (K.X n)) :
    IsIso (mappingCone.inr φ) := by
  have : ∀ p, IsIso ((mappingCone.inr φ).f p) := fun p => ⟨⟨(mappingCone.snd φ).v p p (add_zero p), by simp, by
    rw [← mappingCone.id_X φ p (p + 1) rfl, (hK (p + 1)).eq_of_tgt ((mappingCone.fst φ).1.v p (p + 1) rfl) 0]
    simp⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem fgt_bij (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} [IsEmpty X] {E : Spc}
    (f : sch.obj X ⟶ E) (n : ℤ) : Function.Bijective (fgt R f F n) := by
  haveI := isIso_inr R ((chains R).map f) (isZero_chains_empty R X)
  exact hH.1 R (mappingCone.inr ((chains R).map f)) F n

theorem rpl_zero (hH : Hyps) (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') [IsEmpty U']
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (he : pl q i e n = 0)
    (x : Hrel (ZMod q) (sch.map f) (tw q i) n) : rpl q i f f' u e comm n x = 0 := by
  apply (fgt_bij hH (ZMod q) (tw q i) (sch.map f') n).1
  rw [map_zero]
  refine (relNat (ZMod q) (tw q i) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) n x).trans ?_
  change pl q i e n _ = 0
  rw [he]; rfl

theorem isEmpty_pullback_closed_subscheme_section_into_complement {B W Y S : Scheme.{0}} (ι : W ⟶ B) (V : B.Opens) (hVW : (V : Set B) = (Set.range ι)ᶜ)
    (p : Y ⟶ B) (s : S ⟶ B) (hs : Set.range ⇑s ⊆ (V : Set B)) :
    IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun x => by
  have h1 : (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s ≫ s) x = (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x := by
    rw [pullback.condition]
  have h2 : (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x ∈ (V : Set B) := by
    rw [← h1]; apply hs; simp only [Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
  rw [hVW] at h2; simp only [Scheme.Hom.comp_apply] at h2; exact h2 ⟨_, rfl⟩⟩

theorem LeafPtV_of : LateralTheory.E.SecondDegreeKilling.LeafPtV := by
  intro hH q _ k _ hq i B W Y Y' toK ι _ V hVW p g hp hgp U A _ t hA hV m hpl y
  haveI := isEmpty_pullback_closed_subscheme_section_into_complement ι V hVW (g ≫ p) (t ≫ U.hom) hV
  let wA : pullback (pullback.snd (g ≫ p) (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶
      pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι :=
    pullback.map _ ι _ ι (fibMap g p (t ≫ U.hom)) (𝟙 W) (𝟙 B)
      (by rw [Category.comp_id, ← Category.assoc (fibMap g p (t ≫ U.hom)), pullback.lift_snd, Category.comp_id]) (by simp)
  have commA : prS (g ≫ p) ι (t ≫ U.hom) ≫ fibMap g p (t ≫ U.hom) = wA ≫ prS p ι (t ≫ U.hom) :=
    (pullback.lift_fst _ _ _).symm
  have hA : prS p ι (t ≫ U.hom) ≫ tY p U t = tW p ι U t ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have hB : prS (g ≫ p) ι (t ≫ U.hom) ≫ tY (g ≫ p) U t = tW (g ≫ p) ι U t ≫ prU (g ≫ p) ι U :=
    (pullback.lift_fst _ _ _).symm
  have hC : prU (g ≫ p) ι U ≫ mY p g U = mW p g ι U ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have E1 : tY (g ≫ p) U t ≫ mY p g U = fibMap g p (t ≫ U.hom) ≫ tY p U t := by
    simp only [tY, mY, fibMap, pullback.map_comp, Category.id_comp, Category.comp_id]
  have c1 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (tY (g ≫ p) U t ≫ mY p g U) =
      (tW (g ≫ p) ι U t ≫ mW p g ι U) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mY p g U) hB).trans ((Category.assoc _ _ _).trans
      ((congrArg (tW (g ≫ p) ι U t ≫ ·) hC).trans (Category.assoc _ _ _).symm)))
  have c2 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (fibMap g p (t ≫ U.hom) ≫ tY p U t) =
      (wA ≫ tW p ι U t) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ tY p U t) commA).trans ((Category.assoc _ _ _).trans
      ((congrArg (wA ≫ ·) hA).trans (Category.assoc _ _ _).symm)))
  have E2 : tW (g ≫ p) ι U t ≫ mW p g ι U = wA ≫ tW p ι U t := by
    simp only [tW, mW, wA, pullback.map_comp]
    congr 1
  rw [rpl_comp q i _ _ _ _ _ _ _ _ _ c1, rpl_congr q i _ _ _ _ _ _ c1 c2 E2 E1, ← rpl_comp q i _ _ _ _ _ hA _ _ commA c2]
  exact rpl_zero hH q i _ _ _ _ commA m hpl _

end LateralTheory.E.LeafPtVPf
