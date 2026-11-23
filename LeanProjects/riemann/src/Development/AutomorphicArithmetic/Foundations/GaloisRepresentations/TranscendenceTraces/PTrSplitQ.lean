import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_id' (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) :
    pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = (pullHQ l f n i) ∘ₗ (pullHQ l g n i) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ Sigma.desc s' = s' j := fun j => Sigma.ι_desc _ _
  let t : gp Ω ⟶ ∐ (fun _ : Fin m => U) := y ≫ inv (Sigma.desc s')
  obtain ⟨⟨j, u⟩, hu⟩ := (sigmaMk (fun _ : Fin m => U)).surjective (pt t)
  rw [sigmaMk_mk] at hu
  have hr : Set.range t ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨u, by rw [hu, pt_eq]⟩
  let t' := IsOpenImmersion.lift (Sigma.ι (fun _ : Fin m => U) j) t hr
  have ht' : t' ≫ Sigma.ι (fun _ : Fin m => U) j = t := IsOpenImmersion.lift_fac _ _ _
  have h1 : t' ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht']
    simp [t]
  have h2 : t' = x0 := by
    rw [← hy, ← h1, Category.assoc, hs j, Category.comp_id]
  refine ⟨j, by rw [← h2]; exact h1, fun k hk => ?_⟩
  have h3 : (x0 ≫ Sigma.ι (fun _ : Fin m => U) k) ≫ Sigma.desc s' =
      (x0 ≫ Sigma.ι (fun _ : Fin m => U) j) ≫ Sigma.desc s' := by
    rw [Category.assoc, Category.assoc, hι, hι, hk, ← h2, h1]
  have h4 := (cancel_mono (Sigma.desc s')).1 h3
  have h5 : Sigma.ι (fun _ : Fin m => U) k (pt x0) = Sigma.ι (fun _ : Fin m => U) j (pt x0) := by
    rw [← pt_comp, ← pt_comp, h4]
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ k j _ _).1 h5)

private theorem finsum_one_singleton {T : Type*} (A : Set T) (a : T) (h : A = {a}) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 1 := by
  subst h
  simp

private theorem finsum_one_empty {T : Type*} (A : Set T) (h : A = ∅) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 0 := by
  subst h
  simp

private theorem tr_split (hCorr : CorrEqQ) (hId : TrIdQ) (l : ℕ) [Fact l.Prime] (n i : ℤ) {U P : Scheme.{0}}
    (p' : P ⟶ U) [IsFinite p'] (wt : IsWt p' (Wt.const P 1)) (wt1 : IsWt (𝟙 U) (Wt.const U 1))
    (hl : IsUnit (l : Γ(U, ⊤))) {m : ℕ} (s' : Fin m → (U ⟶ P)) (hs : ∀ j, s' j ≫ p' = 𝟙 U)
    (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P)) :
    trHQ l p' (Wt.const P 1) n i = ∑ j, pullHQ l (sch.map (s' j)) n i := by
  classical
  let c : Option (Fin m) → Corr U P := fun o => match o with
    | none => ⟨P, p', 𝟙 P, Wt.const P 1, inferInstance, wt⟩
    | some j => ⟨U, 𝟙 U, s' j, Wt.const U 1, inferInstance, wt1⟩
  let mm : Option (Fin m) → ℤ := fun o => match o with
    | none => 1
    | some _ => -1
  have hcn : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c none).cyc Ω x0 y = if y ≫ p' = x0 then 1 else 0 := by
    intro Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ y ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.2, fun hz => ⟨hz ▸ h, hz⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨h1, rfl⟩
      exact h h1
  have hcs : ∀ (j : Fin m) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c (some j)).cyc Ω x0 y = if x0 ≫ s' j = y then 1 else 0 := by
    intro j Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ x0 ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, hz ▸ h⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨rfl, h1⟩
      exact h h1
  have key := hCorr l n i (𝟙 U) p' (Option (Fin m)) c mm
    (fun a => by cases a with
      | none => simp [c]
      | some j => simp [c, hs j]) hl Set.univ dense_univ
    (fun Ω _ _ x0 y _ => by
      rw [Fintype.sum_option]
      simp only [hcn, hcs, mm]
      by_cases hy : y ≫ p' = x0
      · obtain ⟨j, hj, hu⟩ := existsUnique_sec p' s' hs hiso x0 y hy
        rw [if_pos hy, Finset.sum_eq_single j]
        · simp [hj]
        · intro k _ hk
          rw [if_neg (fun e => hk (hu k e))]
          simp
        · simp
      · rw [if_neg hy]
        simp only [mul_zero, zero_add]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        · simp
        · intro e
          apply hy
          rw [← e, Category.assoc, hs j, Category.comp_id])
  rw [Fintype.sum_option] at key
  have e0 : (c none).opQ l n i = trHQ l p' (Wt.const P 1) n i := by
    change trHQ l p' (Wt.const P 1) n i ∘ₗ pullHQ l (sch.map (𝟙 P)) n i = _
    rw [CategoryTheory.Functor.map_id, pullHQ_id', LinearMap.comp_id]
  have e1 : ∀ j, (c (some j)).opQ l n i = pullHQ l (sch.map (s' j)) n i := by
    intro j
    change trHQ l (𝟙 U) (Wt.const U 1) n i ∘ₗ pullHQ l (sch.map (s' j)) n i = _
    rw [hId l n i U 1 hl]
    simp
  simp only [mm, e0, e1] at key
  simp only [Int.cast_one, one_smul, Int.cast_neg, neg_smul, Finset.sum_neg_distrib] at key
  exact add_neg_eq_zero.1 key

theorem UpperTheory.Gal.TranscendenceTraces.trSplitQ_of :
    TrBCQ → CorrEqQ → TrIdQ → WtLin → WtFlat → MultBasic → TrSplitQ := by
  intro hBC hCorr hId hLin hFlat hMult l _ n i Z S p _ _ hl U x m s hs hiso
  have wtp : IsWt p (Wt.const Z 1) := by
    rw [← hMult.2.2 p]
    exact hFlat p
  have wtp' : IsWt (pullback.snd p x) (Wt.const (pullback p x) 1) := by
    rw [← hMult.2.2 (pullback.snd p x)]
    exact hFlat _
  have hlU : IsUnit (l : Γ(U, ⊤)) := by
    simpa using hl.map x.appTop.hom
  have h1 := hBC l n i (pullback.fst p x) (pullback.snd p x) p x (Wt.const Z 1)
    (IsPullback.of_hasPullback p x) wtp hl
  have h2 := tr_split hCorr hId l n i (pullback.snd p x) wtp' (hLin.2.2 (𝟙 U) 1) hlU
    (fun j => pullback.lift (s j) (𝟙 U) (by rw [hs j, Category.id_comp]))
    (fun j => pullback.lift_snd _ _ _) hiso
  rw [h1]
  change trHQ l (pullback.snd p x) (Wt.const _ 1) n i ∘ₗ _ = _
  rw [h2]
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LinearMap.comp_apply, ← pullHQ_comp', ← CategoryTheory.Functor.map_comp, pullback.lift_fst]
