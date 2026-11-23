import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingCupPullback
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.LHMV

variable {q : ℕ}

private theorem cast_cast' {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

private theorem pull_cast' {E E' : Spc} (s : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E' n i) :
    pull _ s _ _ (x.cast h1 h2) = Ht.cast h1 h2 (pull _ s _ _ x) := by
  subst h1 h2; rfl

private theorem cast_add' {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    (x + y).cast h1 h2 = x.cast h1 h2 + y.cast h1 h2 := by
  subst h1 h2; rfl

private theorem cast_zero' {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

private theorem cup_cast_left {E : Spc} {n i n' i' m j : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) (y : Ht q E m j) :
    cup q (x.cast h1 h2) y = (cup q x y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

private noncomputable def Phi (q : ℕ) {X E : Spc} (π : X ⟶ E) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)) (n i : ℤ)
    (a : ∀ j, Ht q E (n - d j) (i - e j)) : Ht q X n i :=
  ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)

private theorem IsMVd_cast {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) {n n' i i' : ℤ} (h1 : n = n') (h1' : n + 1 = n' + 1) (h2 : i = i')
    (c : Ht q (pullback f g) n i) (x : Ht q E (n + 1) i) (h : IsMVd f g (tw q i) n c x) :
    IsMVd f g (tw q i') n' (c.cast h1 h2) (x.cast h1' h2) := by
  subst h1 h2; exact h

private theorem cast_eq_zero' {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) (h : x.cast h1 h2 = 0) : x = 0 := by
  subst h1 h2; exact h

end UpperTheory.LHMV

private theorem ht_cast_sub' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    (x - y).cast h1 h2 = x.cast h1 h2 - y.cast h1 h2 := by
  subst h1 h2; rfl

private theorem ht_cast_finset_sum (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {ι : Type} (s : Finset ι)
    (x : ι → Ht q E n i) : (∑ j ∈ s, x j).cast h1 h2 = ∑ j ∈ s, (x j).cast h1 h2 := by
  subst h1 h2; rfl

private theorem ht_cast_injective (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i)
    (h : x.cast h1 h2 = y.cast h1 h2) : x = y := by
  subst h1 h2; exact h

private theorem pull_cup_commutative_algebra (q : ℕ) {E E' : Spc} (s : E ⟶ E') {n m i j : ℤ} (x : Ht q E' n i) (y : Ht q E' m j) :
    pull _ s _ _ (cup q x y) = cup q (pull _ s _ _ x) (pull _ s _ _ y) :=
  GlobalTheory.T.cup_hypercohomologyPullback _ _ s _ x y

private theorem lhmv_phi_add (q : ℕ) {X E : Spc} (π : X ⟶ E) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j))
    (n i : ℤ) (a b : ∀ j, Ht q E (n - d j) (i - e j)) :
    UpperTheory.LHMV.Phi q π d e c n i (a + b) = UpperTheory.LHMV.Phi q π d e c n i a + UpperTheory.LHMV.Phi q π d e c n i b := by
  unfold UpperTheory.LHMV.Phi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add, AddMonoidHom.add_apply]
  exact UpperTheory.LHMV.cast_add' _ _ _ _

private theorem lhmv_phi_sub (q : ℕ) {X E : Spc} (π : X ⟶ E) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j))
    (n i : ℤ) (a b : ∀ j, Ht q E (n - d j) (i - e j)) :
    UpperTheory.LHMV.Phi q π d e c n i (a - b) = UpperTheory.LHMV.Phi q π d e c n i a - UpperTheory.LHMV.Phi q π d e c n i b := by
  unfold UpperTheory.LHMV.Phi
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, map_sub, AddMonoidHom.sub_apply]
  exact ht_cast_sub' q _ _ _ _

private theorem lhmv_phi_zero (q : ℕ) {X E : Spc} (π : X ⟶ E) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j))
    (n i : ℤ) : UpperTheory.LHMV.Phi q π d e c n i 0 = 0 := by
  unfold UpperTheory.LHMV.Phi
  simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, UpperTheory.LHMV.cast_zero', Finset.sum_const_zero]

private theorem pull_lhmv_phi_eq_of_square (q : ℕ) {Y Y' B B' : Spc} (p : Y ⟶ B) (p' : Y' ⟶ B') (s : Y' ⟶ Y) (t : B' ⟶ B)
    (h : s ≫ p = p' ≫ t) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q Y (d j) (e j)) (n i : ℤ)
    (a : ∀ j, Ht q B (n - d j) (i - e j)) :
    pull _ s _ _ (UpperTheory.LHMV.Phi q p d e c n i a) =
      UpperTheory.LHMV.Phi q p' d e (fun j => pull _ s _ _ (c j)) n i (fun j => pull _ t _ _ (a j)) := by
  unfold UpperTheory.LHMV.Phi
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [UpperTheory.LHMV.pull_cast', pull_cup_commutative_algebra, ← pull_comp, ← pull_comp, h]

private theorem lh_comp_iso (q : ℕ) {Y Y' B : Spc} (p : Y ⟶ B) (φ : Y' ⟶ Y) (ψ : Y ⟶ Y') (h1 : φ ≫ ψ = 𝟙 Y')
    (h2 : ψ ≫ φ = 𝟙 Y) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q Y (d j) (e j)) (hp : LH q p d e c) :
    LH q (φ ≫ p) d e (fun j => pull _ φ _ _ (c j)) := by
  intro n i
  have hP : Function.Bijective (UpperTheory.LHMV.Phi q p d e c n i) := hp n i
  have hb : Function.Bijective (pull (ZMod q) φ (tw q i) n) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨pull _ ψ _ _ y, ?_⟩⟩
    · have := congrArg (pull (ZMod q) ψ (tw q i) n) hxy
      rwa [← pull_comp, ← pull_comp, h2, pull_id, pull_id] at this
    · rw [← pull_comp, h1, pull_id]
  have key : UpperTheory.LHMV.Phi q (φ ≫ p) d e (fun j => pull _ φ _ _ (c j)) n i =
      (pull (ZMod q) φ (tw q i) n) ∘ UpperTheory.LHMV.Phi q p d e c n i := by
    funext a
    rw [Function.comp_apply, pull_lhmv_phi_eq_of_square q p (φ ≫ p) φ (𝟙 B) (by simp) d e c n i a]
    simp only [pull_id]
  show Function.Bijective (UpperTheory.LHMV.Phi q (φ ≫ p) d e (fun j => pull _ φ _ _ (c j)) n i)
  rw [key]
  exact hb.comp hP

private theorem lerayHirsch_of_mayerVietoris_cover_lemma_10 (q : ℕ) [NeZero q] {U V E X XU XV : Spc} (f : U ⟶ E) (g : V ⟶ E) (π : X ⟶ E)
    (fX : XU ⟶ X) (gX : XV ⟶ X) (pU : XU ⟶ U) (pV : XV ⟶ V) (hu : fX ≫ π = pU ≫ f) (hv : gX ≫ π = pV ≫ g)
    (hE : Cover2 (ZMod q) f g) (hX : Cover2 (ZMod q) fX gX) {m : ℕ} (d e : Fin m → ℤ)
    (c : ∀ j, Ht q X (d j) (e j)) (n i : ℤ) (γ : ∀ j, Ht q (pullback f g) (n - 1 - d j) (i - e j))
    (a : ∀ j, Ht q E (n - d j) (i - e j))
    (hγ : ∀ j, IsMVd f g (tw q (i - e j)) (n - 1 - d j) (γ j) ((a j).cast (by ring) rfl)) :
    IsMVd fX gX (tw q i) (n - 1)
      (UpperTheory.LHMV.Phi q (pullback.map fX gX f g pU pV π hu hv) d e
        (fun j => pull _ (pullback.fst fX gX ≫ fX) _ _ (c j)) (n - 1) i γ)
      ((UpperTheory.LHMV.Phi q π d e c n i a).cast (by ring) rfl) := by
  obtain ⟨P1, _, P3, P4, _, _⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) (n - 1)).1 fX gX hX
  have hterm : ∀ j, IsMVd fX gX (tw q i) (n - 1)
      ((cup q (pull _ (pullback.map fX gX f g pU pV π hu hv) _ _ (γ j))
        (pull _ (pullback.fst fX gX ≫ fX) _ _ (c j))).cast (by ring) (by ring))
      (((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i).cast (by ring) rfl) := by
    intro j
    have h1 := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q (i - e j)) (n - 1 - d j)).2 fX gX f g π pU pV hu hv hX hE _ _ (hγ j)
    have h2 := UpperTheory.mayerVietorisConnecting_cup_pullback q fX gX hX (n - 1 - d j) (d j) (i - e j) (e j) _ _ (c j) h1
    have h3 := UpperTheory.LHMV.IsMVd_cast fX gX (by ring : n - 1 - d j + d j = n - 1) (by ring)
      (by ring : i - e j + e j = i) _ _ h2
    rw [UpperTheory.LHMV.pull_cast', UpperTheory.LHMV.cup_cast_left, UpperTheory.LHMV.cast_cast', UpperTheory.LHMV.cast_cast'] at h3
    rw [UpperTheory.LHMV.cast_cast']
    exact h3
  have h0 : IsMVd fX gX (tw q i) (n - 1) 0 0 := by
    obtain ⟨x, hx⟩ := P1 0
    have : x = 0 := (P4 _ _ hx).2 ⟨0, 0, by simp⟩
    rwa [this] at hx
  have hs := Finset.sum_induction (s := Finset.univ)
    (fun j => (((cup q (pull _ (pullback.map fX gX f g pU pV π hu hv) _ _ (γ j))
        (pull _ (pullback.fst fX gX ≫ fX) _ _ (c j))).cast (by ring) (by ring) : Ht q (pullback fX gX) (n - 1) i),
      (((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i).cast (by ring) rfl :
        Ht q X (n - 1 + 1) i)))
    (fun pr => IsMVd fX gX (tw q i) (n - 1) pr.1 pr.2) (fun _ _ ha hb => P3 _ _ _ _ ha hb) h0
    (fun j _ => hterm j)
  simp only [Prod.fst_sum, Prod.snd_sum] at hs
  unfold UpperTheory.LHMV.Phi
  rw [ht_cast_finset_sum]
  exact hs

private theorem lh_pullback_map_fst_snd_of_lh (q : ℕ) {U V E X : Spc} (f : U ⟶ E) (g : V ⟶ E) (π : X ⟶ E) {m : ℕ}
    (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j))
    (hUV : LH q (pullback.snd π (pullback.fst f g ≫ f)) d e
      (fun j => pull _ (pullback.fst π (pullback.fst f g ≫ f)) _ _ (c j))) :
    LH q (pullback.map (pullback.fst π f) (pullback.fst π g) f g (pullback.snd π f) (pullback.snd π g) π
      pullback.condition pullback.condition) d e
      (fun j => pull _ (pullback.fst (pullback.fst π f) (pullback.fst π g) ≫ pullback.fst π f) _ _ (c j)) := by
  have hφ : (pullback.fst (pullback.fst π f) (pullback.fst π g) ≫ pullback.fst π f) ≫ π =
      pullback.map (pullback.fst π f) (pullback.fst π g) f g (pullback.snd π f) (pullback.snd π g) π
        pullback.condition pullback.condition ≫ (pullback.fst f g ≫ f) := by
    simp only [Category.assoc, pullback.condition (f := π) (g := f), pullback.map, pullback.lift_fst_assoc]
  have hψ1 : pullback.fst π (pullback.fst f g ≫ f) ≫ π =
      (pullback.snd π (pullback.fst f g ≫ f) ≫ pullback.fst f g) ≫ f := by
    rw [pullback.condition (f := π) (g := pullback.fst f g ≫ f), Category.assoc]
  have hψ2 : pullback.fst π (pullback.fst f g ≫ f) ≫ π =
      (pullback.snd π (pullback.fst f g ≫ f) ≫ pullback.snd f g) ≫ g := by
    rw [hψ1, Category.assoc, Category.assoc, ← pullback.condition (f := f) (g := g)]
  have hψ3 : pullback.lift _ _ hψ1 ≫ pullback.fst π f = pullback.lift _ _ hψ2 ≫ pullback.fst π g := by
    rw [pullback.lift_fst, pullback.lift_fst]
  have key := lh_comp_iso q (pullback.snd π (pullback.fst f g ≫ f)) (pullback.lift _ _ hφ)
    (pullback.lift (pullback.lift _ _ hψ1) (pullback.lift _ _ hψ2) hψ3)
    (by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
        · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
      · apply pullback.hom_ext
        · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
          exact pullback.condition
        · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map])
    (by
      apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
      · apply pullback.hom_ext
        · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
        · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map])
    d e _ hUV
  have e1 : pullback.lift _ _ hφ ≫ pullback.snd π (pullback.fst f g ≫ f) =
      pullback.map (pullback.fst π f) (pullback.fst π g) f g (pullback.snd π f) (pullback.snd π g) π
        pullback.condition pullback.condition := pullback.lift_snd _ _ _
  have e2 : ∀ j, pull _ (pullback.lift _ _ hφ) _ _ (pull _ (pullback.fst π (pullback.fst f g ≫ f)) _ _ (c j)) =
      pull _ (pullback.fst (pullback.fst π f) (pullback.fst π g) ≫ pullback.fst π f) _ _ (c j) := by
    intro j; rw [← pull_comp, pullback.lift_fst]
  rw [e1] at key
  simp only [e2] at key
  exact key

private theorem lh_of_cover2_lh_pieces_and_overlap (q : ℕ) [NeZero q] {U V E X XU XV : Spc} (f : U ⟶ E) (g : V ⟶ E) (π : X ⟶ E)
    (fX : XU ⟶ X) (gX : XV ⟶ X) (pU : XU ⟶ U) (pV : XV ⟶ V) (hu : fX ≫ π = pU ≫ f) (hv : gX ≫ π = pV ≫ g)
    {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j))
    (hE : Cover2 (ZMod q) f g) (hX : Cover2 (ZMod q) fX gX)
    (hU : LH q pU d e (fun j => pull _ fX _ _ (c j))) (hV : LH q pV d e (fun j => pull _ gX _ _ (c j)))
    (hW : LH q (pullback.map fX gX f g pU pV π hu hv) d e
      (fun j => pull _ (pullback.fst fX gX ≫ fX) _ _ (c j))) :
    LH q π d e c := by
  have hUb : ∀ n i, Function.Bijective (UpperTheory.LHMV.Phi q pU d e (fun j => pull _ fX _ _ (c j)) n i) :=
    fun n i => hU n i
  have hVb : ∀ n i, Function.Bijective (UpperTheory.LHMV.Phi q pV d e (fun j => pull _ gX _ _ (c j)) n i) :=
    fun n i => hV n i
  have hWb : ∀ n i, Function.Bijective (UpperTheory.LHMV.Phi q (pullback.map fX gX f g pU pV π hu hv) d e
      (fun j => pull _ (pullback.fst fX gX ≫ fX) _ _ (c j)) n i) := fun n i => hW n i
  have rU : ∀ n i a, pull _ fX _ _ (UpperTheory.LHMV.Phi q π d e c n i a) =
      UpperTheory.LHMV.Phi q pU d e (fun j => pull _ fX _ _ (c j)) n i (fun j => pull _ f _ _ (a j)) :=
    fun n i a => pull_lhmv_phi_eq_of_square q π pU fX f hu d e c n i a
  have rV : ∀ n i a, pull _ gX _ _ (UpperTheory.LHMV.Phi q π d e c n i a) =
      UpperTheory.LHMV.Phi q pV d e (fun j => pull _ gX _ _ (c j)) n i (fun j => pull _ g _ _ (a j)) :=
    fun n i a => pull_lhmv_phi_eq_of_square q π pV gX g hv d e c n i a
  have sW1 : pullback.fst fX gX ≫ pU = pullback.map fX gX f g pU pV π hu hv ≫ pullback.fst f g := by
    simp only [pullback.map, pullback.lift_fst]
  have sW2 : pullback.snd fX gX ≫ pV = pullback.map fX gX f g pU pV π hu hv ≫ pullback.snd f g := by
    simp only [pullback.map, pullback.lift_snd]
  have rWU : ∀ n i b, pull _ (pullback.fst fX gX) _ _ (UpperTheory.LHMV.Phi q pU d e (fun j => pull _ fX _ _ (c j)) n i b) =
      UpperTheory.LHMV.Phi q (pullback.map fX gX f g pU pV π hu hv) d e
        (fun j => pull _ (pullback.fst fX gX ≫ fX) _ _ (c j)) n i (fun j => pull _ (pullback.fst f g) _ _ (b j)) := by
    intro n i b
    rw [pull_lhmv_phi_eq_of_square q pU _ _ _ sW1]
    simp only [pull_comp]
  have rWV : ∀ n i b, pull _ (pullback.snd fX gX) _ _ (UpperTheory.LHMV.Phi q pV d e (fun j => pull _ gX _ _ (c j)) n i b) =
      UpperTheory.LHMV.Phi q (pullback.map fX gX f g pU pV π hu hv) d e
        (fun j => pull _ (pullback.fst fX gX ≫ fX) _ _ (c j)) n i (fun j => pull _ (pullback.snd f g) _ _ (b j)) := by
    intro n i b
    rw [pull_lhmv_phi_eq_of_square q pV _ _ _ sW2, pullback.condition (f := fX) (g := gX)]
    simp only [pull_comp]
  intro n i
  change Function.Bijective (UpperTheory.LHMV.Phi q π d e c n i)
  have ker : ∀ a, UpperTheory.LHMV.Phi q π d e c n i a = 0 → a = 0 := by
    intro a ha
    have haU : (fun j => pull _ f _ _ (a j)) = 0 :=
      (hUb n i).1 (by rw [← rU n i a, ha, map_zero, lhmv_phi_zero])
    have haV : (fun j => pull _ g _ _ (a j)) = 0 :=
      (hVb n i).1 (by rw [← rV n i a, ha, map_zero, lhmv_phi_zero])
    have hγ : ∀ j, ∃ γ : Ht q (pullback f g) (n - 1 - d j) (i - e j),
        IsMVd f g (tw q (i - e j)) (n - 1 - d j) γ ((a j).cast (by ring) rfl) := by
      intro j
      obtain ⟨_, _, _, _, P5, _⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q (i - e j)) (n - 1 - d j)).1 f g hE
      have hj1 : pull _ f _ _ (a j) = 0 := congrFun haU j
      have hj2 : pull _ g _ _ (a j) = 0 := congrFun haV j
      apply (P5 _).1
      constructor
      · rw [UpperTheory.LHMV.pull_cast', hj1]
        exact UpperTheory.LHMV.cast_zero' _ _
      · rw [UpperTheory.LHMV.pull_cast', hj2]
        exact UpperTheory.LHMV.cast_zero' _ _
    choose γ hγ using hγ
    have hb := lerayHirsch_of_mayerVietoris_cover_lemma_10 q f g π fX gX pU pV hu hv hE hX d e c n i γ a hγ
    rw [ha, UpperTheory.LHMV.cast_zero'] at hb
    obtain ⟨_, _, _, P4X, _, _⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) (n - 1)).1 fX gX hX
    obtain ⟨a', b', hab⟩ := (P4X _ _ hb).1 rfl
    obtain ⟨α, rfl⟩ := (hUb (n - 1) i).2 a'
    obtain ⟨β, rfl⟩ := (hVb (n - 1) i).2 b'
    rw [rWU, rWV, ← lhmv_phi_sub] at hab
    have hγ' := (hWb (n - 1) i).1 hab
    funext j
    obtain ⟨_, _, _, P4, _, _⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q (i - e j)) (n - 1 - d j)).1 f g hE
    exact UpperTheory.LHMV.cast_eq_zero' _ _ _ ((P4 _ _ (hγ j)).2 ⟨α j, β j, congrFun hγ' j⟩)
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · exact sub_eq_zero.1 (ker (a - b) (by rw [lhmv_phi_sub, hab, sub_self]))
  · obtain ⟨α, hα⟩ := (hUb n i).2 (pull _ fX _ _ y)
    obtain ⟨β, hβ⟩ := (hVb n i).2 (pull _ gX _ _ y)
    have hαβ : (fun j => pull _ (pullback.fst f g) _ _ (α j)) = (fun j => pull _ (pullback.snd f g) _ _ (β j)) := by
      apply (hWb n i).1
      rw [← rWU n i α, ← rWV n i β, hα, hβ, ← pull_comp, ← pull_comp, pullback.condition (f := fX) (g := gX)]
    have hx : ∀ j, ∃ x : Ht q E (n - d j) (i - e j), pull _ f _ _ x = α j ∧ pull _ g _ _ x = β j := by
      intro j
      obtain ⟨_, _, _, _, _, P6⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q (i - e j)) (n - d j)).1 f g hE
      exact (P6 _ _).1 (congrFun hαβ j)
    choose x hx using hx
    have hxα : (fun j => pull _ f _ _ (x j)) = α := funext fun j => (hx j).1
    have hxβ : (fun j => pull _ g _ _ (x j)) = β := funext fun j => (hx j).2
    have hzU : pull _ fX _ _ (y - UpperTheory.LHMV.Phi q π d e c n i x) = 0 := by
      rw [map_sub, rU, hxα, hα, sub_self]
    have hzV : pull _ gX _ _ (y - UpperTheory.LHMV.Phi q π d e c n i x) = 0 := by
      rw [map_sub, rV, hxβ, hβ, sub_self]
    obtain ⟨_, P2X, _, _, P5X, _⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) (n - 1)).1 fX gX hX
    obtain ⟨w, hw⟩ := (P5X ((y - UpperTheory.LHMV.Phi q π d e c n i x).cast (by ring : n = n - 1 + 1) rfl)).1
      ⟨by rw [UpperTheory.LHMV.pull_cast', hzU, UpperTheory.LHMV.cast_zero'],
       by rw [UpperTheory.LHMV.pull_cast', hzV, UpperTheory.LHMV.cast_zero']⟩
    obtain ⟨γ, rfl⟩ := (hWb (n - 1) i).2 w
    have ha' : ∀ j, ∃ a' : Ht q E (n - d j) (i - e j),
        IsMVd f g (tw q (i - e j)) (n - 1 - d j) (γ j) (a'.cast (by ring) rfl) := by
      intro j
      obtain ⟨P1, _, _, _, _, _⟩ := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q (i - e j)) (n - 1 - d j)).1 f g hE
      obtain ⟨x'', hx''⟩ := P1 (γ j)
      refine ⟨(Ht.cast (q := q) (by ring) rfl x'' : Ht q E (n - d j) (i - e j)), ?_⟩
      rw [UpperTheory.LHMV.cast_cast']
      exact hx''
    choose a' ha' using ha'
    have hb := lerayHirsch_of_mayerVietoris_cover_lemma_10 q f g π fX gX pU pV hu hv hE hX d e c n i γ a' ha'
    have heq := ht_cast_injective q _ _ _ _ (P2X _ _ _ hw hb)
    refine ⟨x + a', ?_⟩
    rw [lhmv_phi_add, ← heq]
    abel

theorem UpperTheory.lerayHirsch_of_mayerVietoris_cover :
    ∀ (q : ℕ) [NeZero q] {U V E X : Spc} (f : U ⟶ E) (g : V ⟶ E) (π : X ⟶ E) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)),
        Cover2 (ZMod q) f g → Cover2 (ZMod q) (pullback.fst π f) (pullback.fst π g) →
        LH q (pullback.snd π f) d e (fun j => pull _ (pullback.fst π f) _ _ (c j)) →
        LH q (pullback.snd π g) d e (fun j => pull _ (pullback.fst π g) _ _ (c j)) →
        LH q (pullback.snd π (pullback.fst f g ≫ f)) d e (fun j => pull _ (pullback.fst π (pullback.fst f g ≫ f)) _ _ (c j)) →
        LH q π d e c := by
  intro q _ U V E X f g π m d e c hE hX hU hV hUV
  exact lh_of_cover2_lh_pieces_and_overlap q f g π (pullback.fst π f) (pullback.fst π g) (pullback.snd π f) (pullback.snd π g)
    pullback.condition pullback.condition d e c hE hX hU hV (lh_pullback_map_fst_snd_of_lh q f g π d e c hUV)
