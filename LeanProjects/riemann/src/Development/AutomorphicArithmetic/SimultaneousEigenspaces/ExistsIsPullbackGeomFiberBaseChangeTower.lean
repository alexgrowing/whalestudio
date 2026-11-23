import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

noncomputable section

section Gen

variable {C : Type*} [Category C] [HasPullbacks C] {S A B D X : C}

private theorem uu_cond (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    (pullback.fst p' d ≫ pullback.fst p b) ≫ p = (pullback.snd p' d ≫ c) ≫ a := by
  subst hp
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, w]

private def uu (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) : pullback p' d ⟶ pullback p a :=
  pullback.lift (pullback.fst p' d ≫ pullback.fst p b) (pullback.snd p' d ≫ c) (uu_cond p a b c d w p' hp)

@[reassoc] private theorem uu_fst (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    uu p a b c d w p' hp ≫ pullback.fst p a = pullback.fst p' d ≫ pullback.fst p b := pullback.lift_fst _ _ _

@[reassoc] private theorem uu_snd (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    uu p a b c d w p' hp ≫ pullback.snd p a = pullback.snd p' d ≫ c := pullback.lift_snd _ _ _

private theorem uu_sq (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    IsPullback (uu p a b c d w p' hp) (pullback.snd p' d) (pullback.snd p a) c := by
  subst hp
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (v₁₃ := p) (h₂₂ := a) ?_ (uu_snd p a b c d w _ rfl)
    (IsPullback.of_hasPullback p a)
  rw [uu_fst, w]
  exact (IsPullback.of_hasPullback (pullback.snd p b) d).paste_horiz (IsPullback.of_hasPullback p b)

private theorem uu_nat {Y : C} (p : Y ⟶ S) (q : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B)
    (w : c ≫ a = d ≫ b) (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b)
    (q' : pullback q b ⟶ B) (hq : q' = pullback.snd q b) (f : Y ⟶ X)
    (fB : pullback p b ⟶ pullback q b) (fA : pullback p a ⟶ pullback q a) (fD : pullback p' d ⟶ pullback q' d)
    (h1 : fB ≫ pullback.fst q b = pullback.fst p b ≫ f) (h2 : fA ≫ pullback.fst q a = pullback.fst p a ≫ f)
    (h3 : fA ≫ pullback.snd q a = pullback.snd p a) (h4 : fD ≫ pullback.fst q' d = pullback.fst p' d ≫ fB)
    (h5 : fD ≫ pullback.snd q' d = pullback.snd p' d) :
    uu p a b c d w p' hp ≫ fA = fD ≫ uu q a b c d w q' hq := by
  apply pullback.hom_ext
  · simp only [Category.assoc, h2, uu_fst, uu_fst_assoc, reassoc_of% h4, h1]
  · simp only [Category.assoc, h3, uu_snd, reassoc_of% h5]

end Gen

end

theorem UpperTheory.exists_isPullback_geomFiber_baseChange_tower :
    ∀ (k K Ω Ω' : Type) [Field k] [Field K] [Field Ω] [Field Ω'] [Algebra k Ω] [Algebra K Ω'] (τ : k →+* K) (j : Ω →+* Ω'), (∀ x, j (algebraMap k Ω x) = algebraMap K Ω' (τ x)) → ∀ (H : HTower k), ∃ (u : (bcAlong H τ).geomZ Ω' ⟶ H.geomZ Ω) (v : ∀ g : H.Γ, GlobalTheory.Et.geom Ω' ((bcAlong H τ).s g ≫ (bcAlong H τ).q) ⟶ GlobalTheory.Et.geom Ω (H.s g ≫ H.q)), IsPullback u (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom j)) ∧ (∀ g, IsPullback (v g) ((bcAlong H τ).sΩ Ω' g) (H.sΩ Ω g) u ∧ v g ≫ H.tΩ Ω g = (bcAlong H τ).tΩ Ω' g ≫ u) ∧ ∀ (σ : Ω ≃ₐ[k] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → GlobalTheory.Et.galMap Ω' (bcAlong H τ).q σ' ≫ u = u ≫ GlobalTheory.Et.galMap Ω H.q σ := by
  intro k K Ω Ω' _ _ _ _ _ _ τ j hj H
  have w : Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω')) ≫ Spec.map (CommRingCat.ofHom τ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact hj x
  have hZ : (bcAlong H τ).q = pullback.snd H.q (Spec.map (CommRingCat.ofHom τ)) := rfl
  have hY : ∀ g, (bcAlong H τ).s g ≫ (bcAlong H τ).q =
      pullback.snd (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom τ)) := fun g => pullback.lift_snd _ _ _
  let u : (bcAlong H τ).geomZ Ω' ⟶ H.geomZ Ω := uu H.q _ _ _ _ w _ hZ
  let v : ∀ g : H.Γ, GlobalTheory.Et.geom Ω' ((bcAlong H τ).s g ≫ (bcAlong H τ).q) ⟶ GlobalTheory.Et.geom Ω (H.s g ≫ H.q) :=
    fun g => uu (H.s g ≫ H.q) _ _ _ _ w _ (hY g)
  have hu : IsPullback u (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom j)) :=
    uu_sq H.q _ _ _ _ w _ hZ
  have hu1 : u ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := uu_fst H.q _ _ _ _ w _ hZ
  have hu2 : u ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom j) :=
    uu_snd H.q _ _ _ _ w _ hZ
  have vs : ∀ g, v g ≫ H.sΩ Ω g = (bcAlong H τ).sΩ Ω' g ≫ u := fun g =>
    uu_nat (H.s g ≫ H.q) H.q _ _ _ _ w _ (hY g) _ hZ (H.s g) ((bcAlong H τ).s g) (H.sΩ Ω g) ((bcAlong H τ).sΩ Ω' g)
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have vt : ∀ g, v g ≫ H.tΩ Ω g = (bcAlong H τ).tΩ Ω' g ≫ u := fun g =>
    uu_nat (H.s g ≫ H.q) H.q _ _ _ _ w _ (hY g) _ hZ (H.t g) ((bcAlong H τ).t g) (H.tΩ Ω g) ((bcAlong H τ).tΩ Ω' g)
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨u, v, hu, fun g => ⟨?_, vt g⟩, ?_⟩
  · refine IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := pullback.snd _ _) ?_ (vs g) hu
    have e1 : (bcAlong H τ).sΩ Ω' g ≫ pullback.snd (bcAlong H τ).q (Spec.map (CommRingCat.ofHom (algebraMap K Ω'))) =
        pullback.snd _ _ := pullback.lift_snd _ _ _
    have e2 : H.sΩ Ω g ≫ pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) =
        pullback.snd _ _ := pullback.lift_snd _ _ _
    rw [e1, e2]
    exact uu_sq (H.s g ≫ H.q) _ _ _ _ w _ (hY g)
  · intro σ σ' hσ
    have hg : Spec.map (CommRingCat.ofHom (σ' : Ω' →+* Ω')) ≫ Spec.map (CommRingCat.ofHom j) =
        Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact hσ x
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst, hu1]
      exact GlobalTheory.Et.galMap_fst_assoc Ω' (bcAlong H τ).q σ' _
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, hu2, GlobalTheory.Et.galMap_snd_assoc, reassoc_of% hu2, hg]
