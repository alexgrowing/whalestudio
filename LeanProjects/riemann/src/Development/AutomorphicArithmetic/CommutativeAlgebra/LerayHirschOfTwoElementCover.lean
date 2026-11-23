import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem cast_zero' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht.cast hn hi (0 : Ht q E n i) = 0 := by
  subst hn hi
  rfl

private theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : Ht.cast hn hi x = 0) : x = 0 := by
  subst hn hi
  exact h

private theorem pull_cast' {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem inj_of_LH {q : ℕ} {N : ℕ} (hN : 1 ≤ N) {E X : Spc} (πX : X ⟶ E) (ξX : Ht q X 2 1)
    (hLH : LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j))
    {n i : ℤ} (a : Ht q E n i) (ha : pull _ πX _ _ a = 0) : a = 0 := by
  classical
  obtain ⟨hinj, -⟩ := hLH n i
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin N, (j0 : ℕ) = 0 := ⟨⟨0, hN⟩, rfl⟩
  have e1 : n = n - 2 * (((j0 : ℕ) : ℤ)) := by simp [hj0]
  have e2 : i = i - ((j0 : ℕ) : ℤ) := by simp [hj0]
  let a' : (j : Fin N) → Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ)) :=
    Pi.single (M := fun j : Fin N => Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))) j0 (a.cast e1 e2)
  have hp : ∀ j, pull _ πX _ _ (a' j) = 0 := by
    intro j
    by_cases hj : j = j0
    · subst hj
      simp only [a', Pi.single_eq_same]
      rw [pull_cast', ha, cast_zero']
    · simp only [a', Pi.single_eq_of_ne hj, map_zero]
  have h0 : a' = 0 := hinj (by simp [hp, cast_zero'])
  have h1 := congrFun h0 j0
  simp only [a', Pi.single_eq_same, Pi.zero_apply] at h1
  exact eq_zero_of_cast e1 e2 a h1

theorem UpperTheory.leray_hirsch_of_two_element_cover :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B W₁ W₂ B₁ B₂ : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
            (f₁ : W₁ ⟶ Y) (f₂ : W₂ ⟶ Y) (g₁ : B₁ ⟶ B) (g₂ : B₂ ⟶ B) (b₁ : B₁ ⟶ W₁) (b₂ : B₂ ⟶ W₂)
            (h₁ : g₁ ≫ β = b₁ ≫ f₁) (h₂ : g₂ ≫ β = b₂ ≫ f₂) (_ : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1),
            Inv q X → Cover2 (ZMod q) f₁ f₂ → Cover2 (ZMod q) g₁ g₂ →
            LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
            (∀ i, Eqv _ (f₁ ≫ πY) (tw q i)) → (∀ i, Eqv _ (g₁ ≫ p) (tw q i)) → (∀ i, Eqv _ b₂ (tw q i)) →
            (∀ i, Eqv _ (pullback.map g₁ g₂ f₁ f₂ b₁ b₂ β h₁ h₂) (tw q i)) →
            ∀ (n i : ℤ) (x : Ht q Y n i), pull _ β _ _ x = 0 → x = 0 := by
  intro q _ N hN E X Y B W₁ W₂ B₁ B₂ πX πY p β f₁ f₂ g₁ g₂ b₁ b₂ h₁ h₂ hsq ξX hX hcW hcB hLH hW₁ hB₁ hb₂
    hmap n i x hx
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have MW := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) m).1 f₁ f₂ hcW
  have MB := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) m).1 g₁ g₂ hcB
  have nat := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) m).2 g₁ g₂ f₁ f₂ β b₁ b₂ h₁ h₂ hcB hcW
  have hA : pull _ f₁ _ _ x = 0 := by
    obtain ⟨e, he⟩ := (hW₁ i (m + 1)).2 (pull _ f₁ _ _ x)
    have key : (g₁ ≫ p) ≫ πX = b₁ ≫ (f₁ ≫ πY) := by
      rw [Category.assoc, hsq, ← Category.assoc, h₁, Category.assoc]
    have h0 : pull _ (g₁ ≫ p) _ _ (pull _ πX _ _ e) = 0 := by
      rw [← pull_comp, key, pull_comp, he, ← pull_comp, ← h₁, pull_comp, hx, map_zero]
    have h1 : pull _ πX _ _ e = 0 := (hB₁ i (m + 1)).1 (h0.trans (map_zero _).symm)
    have h2 : e = 0 := inj_of_LH hN πX ξX hLH e h1
    rw [← he, h2, map_zero]
  have hB : pull _ f₂ _ _ x = 0 := by
    apply (hb₂ i (m + 1)).1
    rw [map_zero, ← pull_comp, ← h₂, pull_comp, hx, map_zero]
  obtain ⟨c, hc⟩ := (MW.2.2.2.2.1 x).1 ⟨hA, hB⟩
  have hc' := nat c x hc
  rw [hx] at hc'
  obtain ⟨a, b, hab⟩ := (MB.2.2.2.1 _ _ hc').1 rfl
  obtain ⟨a₀, ha₀⟩ := (hB₁ i m).2 a
  have hfst : pull _ (pullback.fst g₁ g₂) _ _ a =
      pull _ (pullback.snd g₁ g₂) _ _ (pull _ g₂ _ _ (pull _ p _ _ a₀)) := by
    rw [← ha₀]
    simp only [← pull_comp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨w, hw⟩ := (hb₂ i m).2 (pull _ g₂ _ _ (pull _ p _ _ a₀) - b)
  have hm : pullback.map g₁ g₂ f₁ f₂ b₁ b₂ β h₁ h₂ ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ b₂ :=
    pullback.lift_snd _ _ _
  have hcw : c = pull _ (pullback.snd f₁ f₂) _ _ w := by
    apply (hmap i m).1
    rw [hab, hfst, ← map_sub, ← hw, ← pull_comp, ← pull_comp, hm]
  exact (MW.2.2.2.1 c x hc).2 ⟨0, -w, by rw [hcw, map_zero, map_neg, zero_sub, neg_neg]⟩
