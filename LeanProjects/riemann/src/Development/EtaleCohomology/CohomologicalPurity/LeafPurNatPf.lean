import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurNatPf

open PurPf

theorem fold_map {P' P : Arrow Spc} (ψ : P' ⟶ P) : dbl.map ψ ≫ dbl.fold P = dbl.fold P' ≫ ψ.right := by
  apply pushout.hom_ext <;>
    simp only [dbl.map, dbl.fold, pushout.map] <;> (first
      | (erw [pushout.inl_desc_assoc, Category.assoc]; erw [pushout.inl_desc, pushout.inl_desc_assoc]; simp)
      | (erw [pushout.inr_desc_assoc, Category.assoc]; erw [pushout.inr_desc, pushout.inr_desc_assoc]; simp)
      | (erw [pushout.inl_desc_assoc, Category.assoc, Category.assoc]; erw [pushout.inl_desc, pushout.inl_desc]; simp)
      | (erw [pushout.inr_desc_assoc, Category.assoc, Category.assoc]; erw [pushout.inr_desc, pushout.inr_desc]; simp))

theorem proj_pull (q : ℕ) {P' P : Arrow Spc} (ψ : P' ⟶ P) (n i : ℤ) (c : Ht q (dbl P) n i) :
    Hs.pull q ψ n i (Hs.proj q P n i c) = Hs.proj q P' n i (pull _ (dbl.map ψ) _ n c) := by
  apply Subtype.ext
  change pull _ (dbl.map ψ) _ n (c - _) = _ - _
  rw [map_sub, ← pull_comp, fold_map, pull_comp, ← pull_comp _ (dbl.inr P') (dbl.map ψ), dbl.inr_map, pull_comp]

theorem act_pull (hN : DivisorNaturality) (q : ℕ) [NeZero q] {P' P : Arrow Spc} (ψ : P' ⟶ P) {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : Hs.pull q ψ _ _ (Hs.act q a b) = Hs.act q (pull _ ψ.right _ _ a) (Hs.pull q ψ _ _ b) := by
  unfold Hs.act
  rw [proj_pull, (hN q).1]
  congr 2
  rw [← pull_comp, ← pull_comp, fold_map]

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map α ≫ dbl.map β = dbl.map (α ≫ β) := by
  apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [← Category.assoc, inl_map, Category.assoc, inl_map, inl_map, Arrow.comp_right, Category.assoc]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_pull (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q α n i (Hs.pull q β n i x) = Hs.pull q (α ≫ β) n i x := by
  apply Subtype.ext
  change pull _ (dbl.map α) _ n (pull _ (dbl.map β) _ n x.1) = pull _ (dbl.map (α ≫ β)) _ n x.1
  rw [← pull_comp, dbl_map_comp]

def purOf {d : ℕ} {P : SP d} (t : Tube P) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ)
    (x : Ht q (sch.obj P.Z) n i) : Hs q (opn P.U) (n + 2 * d) (i + d) :=
  (AddEquiv.ofBijective _ ((t.ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
    (Hs.act q (P := abv P.U t.π) ((AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm
      (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)) (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P)))

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : purT T q P n i x = purOf (T P) q hq n i x := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dif_pos h]
  rfl

theorem purOf_char {d : ℕ} {P : SP d} (t : Tube P) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ)
    (x : Ht q (sch.obj P.Z) n i) (y : Hs q (opn P.U) (n + 2 * d) (i + d)) (e : Ht q t.E n i)
    (he : pull _ (pullback.fst t.π (sch.map P.ι)) (tw q i) n e = pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)
    (hy : Hs.pull q (abvMap P.U t.π) _ _ y = Hs.act q (P := abv P.U t.π) e (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P))) :
    purOf t q hq n i x = y := by
  have he' : (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm
      (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x) = e := by
    rw [AddEquiv.symm_apply_eq]; exact he.symm
  unfold purOf
  rw [he', AddEquiv.symm_apply_eq]
  exact hy.symm

theorem unit_of {d : ℕ} {P' P : SP d} (φ : P'.Hom P) (q : ℕ) (hq : IsUnit (q : Γ(P.X, ⊤))) :
    IsUnit (q : Γ(P'.X, ⊤)) := by
  have := hq.map φ.f.appTop.hom
  simpa using this

theorem purOf_nat (hN : DivisorNaturality) {d : ℕ} (hC : IsCl d (fcl d)) {P' P : SP d} (φ : P'.Hom P) (t : Tube P) (t' : Tube P')
    (b : t'.E ⟶ t.E) (hb : b ≫ t.π = t'.π ≫ sch.map φ.f) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) :
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purOf t q hq n i x) =
      purOf t' q (unit_of φ q hq) n i (pull _ (sch.map φ.g) _ _ x) := by
  symm

  set e := (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)
    with he_def
  have he : pull _ (pullback.fst t.π (sch.map P.ι)) (tw q i) n e = pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x :=
    (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).apply_symm_apply _
  have hy : Hs.pull q (abvMap P.U t.π) _ _ (purOf t q hq n i x) =
      Hs.act q (P := abv P.U t.π) e (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P)) :=
    (AddEquiv.ofBijective _ ((t.ok q hq).2.2.1 (n + 2 * d) (i + d))).apply_symm_apply _

  have hw : (pullback.fst t'.π (sch.map P'.ι) ≫ b) ≫ t.π = (pullback.snd t'.π (sch.map P'.ι) ≫ sch.map φ.g) ≫ sch.map P.ι := by
    rw [Category.assoc, hb, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, φ.cart.w]
  let c : pullback t'.π (sch.map P'.ι) ⟶ pullback t.π (sch.map P.ι) := pullback.lift _ _ hw

  have hw2 : (pullback.fst t'.π (sch.map P'.U.ι) ≫ b) ≫ t.π =
      (pullback.snd t'.π (sch.map P'.U.ι) ≫ sch.map (φ.f.resLE P.U P'.U φ.le)) ≫ sch.map P.U.ι := by
    rw [Category.assoc, hb, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]
  let ψ : abv P'.U t'.π ⟶ abv P.U t.π := Arrow.homMk (pullback.lift _ _ hw2) b (by simp only [abv, Arrow.mk_hom]; exact pullback.lift_fst _ _ _)
  have hsq : abvMap P'.U t'.π ≫ opnMap φ.f _ _ φ.le = ψ ≫ abvMap P.U t.π := by
    apply Arrow.hom_ext
    · simp only [Arrow.comp_left, abvMap, opnMap, ψ, Arrow.homMk_left]; exact (pullback.lift_snd _ _ _).symm
    · simp only [Arrow.comp_right, abvMap, opnMap, ψ, Arrow.homMk_right]; exact hb.symm
  apply purOf_char t' q _ n i _ _ (pull _ b _ _ e)
  · rw [← pull_comp, ← pull_comp, show pullback.fst t'.π (sch.map P'.ι) ≫ b = c ≫ pullback.fst t.π (sch.map P.ι) from (pullback.lift_fst _ _ hw).symm,
      show pullback.snd t'.π (sch.map P'.ι) ≫ sch.map φ.g = c ≫ pullback.snd t.π (sch.map P.ι) from (pullback.lift_snd _ _ hw).symm,
      pull_comp, pull_comp, he]
  · rw [pull_pull, hsq, ← pull_pull, hy]
    refine (act_pull hN q ψ (P := abv P.U t.π) e _).trans ?_
    congr 1
    rw [pull_pull, ← hsq, ← pull_pull, (hC q).2.1 P' P φ hq]

theorem dbl_map_of_right {P : Arrow Spc} (ψ : P ⟶ P) (h : ψ.right = 𝟙 _) : dbl.map ψ = 𝟙 _ := by
  apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [inl_map, h, Category.id_comp, Category.comp_id]
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [dbl.inr_map, h, Category.id_comp, Category.comp_id]

theorem pull_of_right (q : ℕ) {P : Arrow Spc} (ψ : P ⟶ P) (h : ψ.right = 𝟙 _) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q ψ n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map ψ) _ n x.1 = x.1
  rw [dbl_map_of_right ψ h, pull_id]

def idHom {d : ℕ} (P : SP d) : P.Hom P where
  f := 𝟙 _
  g := 𝟙 _
  cart := by
    first
      | exact IsPullback.of_vert_isIso ⟨by simp⟩
      | exact IsPullback.of_horiz_isIso ⟨by simp⟩
  le := fun x hx => hx

end PurNatPf

open PurNatPf PurPf

theorem LeafPurNat_of : EtalePurityNaturality := by
  intro hH hCl d T hT q _ P hq P' φ n i x
  have hN : DivisorNaturality := hH.2.2.2.2.1
  have hC : IsCl d (fcl d) := pick_spec (hCl hH d)
  obtain ⟨T', a, b, ha, hb⟩ := hT P' P φ
  have hq' := unit_of φ q hq
  rw [purT_eq T q P hq, purT_eq T q P' hq', purOf_nat hN hC φ (T P) T' b hb q hq]
  have hb' : a ≫ (T P').π = T'.π ≫ sch.map (idHom P').f := by
    rw [ha]; change _ = T'.π ≫ sch.map (𝟙 _); rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have key := purOf_nat hN hC (idHom P') (T P') T' a hb' q hq' n i (pull _ (sch.map φ.g) _ _ x)
  rw [pull_of_right] at key
  · rw [key]
    change _ = purOf T' q _ n i (pull _ (sch.map (𝟙 _)) _ _ _)
    rw [CategoryTheory.Functor.map_id, pull_id]
  · change sch.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    rfl

end LateralTheory.CohomologicalPurity
