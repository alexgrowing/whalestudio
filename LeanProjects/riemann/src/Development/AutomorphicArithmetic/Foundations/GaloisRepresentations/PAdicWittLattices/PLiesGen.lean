import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fEt_comp_iso {Y X X' : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ X') [IsIso i] (d : ℕ) (hf : FEt f d) :
    FEt (f ≫ i) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  haveI := h1
  haveI := h2
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv i)]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun y => ?_
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [← Category.assoc, h]
    simp

theorem UpperTheory.Gal.G3.pLiesGen :
    LiesGen := by
  intro k L O _ _ _ _ H θ C g D s t hst m hL
  obtain ⟨-, κ0, h0, h1, hF⟩ := hL
  have hq : κ0 ≫ s ≫ C.p = (H.s g ≫ H.q) ≫ gen O k := by
    rw [← Category.assoc, ← h0, Category.assoc, C.ov, Category.assoc]
  let κ : H.Y g ⟶ pullback (s ≫ C.p) (gen O k) := pullback.lift κ0 (H.s g ≫ H.q) hq
  have hA : H.s g ≫ piK C = κ ≫ bcMap (gen O k) s rfl := by
    apply pullback.hom_ext
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact h0
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  refine ⟨κ, hA, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact h1
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact (H.comm g).symm
  · have w1 : pullback.snd C.π s ≫ s ≫ C.p = (pullback.fst C.π s ≫ H.q) ≫ gen O k := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, C.ov, Category.assoc]
    let i0 : pullback C.π s ⟶ pullback (s ≫ C.p) (gen O k) :=
      pullback.lift (pullback.snd C.π s) (pullback.fst C.π s ≫ H.q) w1
    have w2 : pullback.fst C.π s ≫ piK C = i0 ≫ bcMap (gen O k) s rfl := by
      apply pullback.hom_ext
      · simp only [piK, bcMap, i0, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact pullback.condition
      · simp only [piK, bcMap, i0, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    let i : pullback C.π s ⟶ pullback (piK C) (bcMap (gen O k) s rfl) :=
      pullback.lift (pullback.fst C.π s) i0 w2
    have c0 := pullback.condition (f := piK C) (g := bcMap (gen O k) s rfl)
    have c1 := congrArg (· ≫ pullback.fst C.p (gen O k)) c0
    have c2 := congrArg (· ≫ pullback.snd C.p (gen O k)) c0
    simp only [piK, bcMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] at c1 c2
    have w3 : pullback.fst (piK C) (bcMap (gen O k) s rfl) ≫ C.π
        = (pullback.snd (piK C) (bcMap (gen O k) s rfl) ≫ pullback.fst (s ≫ C.p) (gen O k)) ≫ s := by
      rw [Category.assoc]
      exact c1
    let j : pullback (piK C) (bcMap (gen O k) s rfl) ⟶ pullback C.π s :=
      pullback.lift _ _ w3
    haveI : IsIso i := by
      refine ⟨⟨j, ?_, ?_⟩⟩
      · apply pullback.hom_ext
        · simp only [i, j, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      · apply pullback.hom_ext
        · simp only [i, j, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc]
        · apply pullback.hom_ext
          · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc]
          · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc]
            exact c2
    have key : pullback.lift (H.s g) κ hA = pullback.lift (H.s g) κ0 h0 ≫ i := by
      apply pullback.hom_ext
      · simp only [i, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · apply pullback.hom_ext
        · simp only [i, i0, κ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
        · simp only [i, i0, κ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    rw [key]
    exact fEt_comp_iso _ i m hF
