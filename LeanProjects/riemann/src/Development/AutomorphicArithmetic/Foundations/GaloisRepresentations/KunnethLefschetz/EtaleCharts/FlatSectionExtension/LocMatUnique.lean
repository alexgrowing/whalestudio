import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TrUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_factor {A W Z : Scheme.{0}} (f : A ⟶ W) (i : W ⟶ Z) (c : A ⟶ Z) (hc : c = f ≫ i)
    {N N'' : Z.Opens} (hle : N'' ≤ N)
    (h : ⊤ ≤ c ⁻¹ᵁ N) (h'' : ⊤ ≤ f ⁻¹ᵁ (i ⁻¹ᵁ N'')) (g : Γ(Z, N)) :
    (c.appLE N ⊤ h).hom g =
      (f.appLE (i ⁻¹ᵁ N'') ⊤ h'').hom ((i.app N'').hom ((Z.presheaf.map (homOfLE hle).op).hom g)) := by
  subst hc
  have h1 : (f ≫ i).appLE N ⊤ h = Z.presheaf.map (homOfLE hle).op ≫ (f ≫ i).appLE N'' ⊤ (by simpa using h'') := by
    rw [Scheme.Hom.map_appLE]
  rw [h1, Scheme.Hom.comp_appLE]
  rfl

private theorem res_isTr {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N N'' : Z.Opens} (hle : N'' ≤ N)
    (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β) (G : Matrix (Fin d) (Fin d) Γ(Z, N)) (hG : IsTr B α β h₁ h₂ G) :
    IsTr B α β (hle.trans h₁) (hle.trans h₂) (G.map (Z.presheaf.map (homOfLE hle).op).hom) := by
  intro m
  have e : ∀ (γ : B.ι) (hγ : N ≤ B.V γ) (l : Fin d), tN B γ (hle.trans hγ) l =
      (Z.presheaf.map (homOfLE hle).op).hom (tN B γ hγ l) := by
    intro γ hγ l
    simp only [tN, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [e β h₂ m, hG m, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, e α h₁ l]
  rfl

private theorem pull_eq {V W Z : Scheme.{0}} (i : W ⟶ Z) (p : V ⟶ W) {U A : V.Opens} (hA : A ≤ U) {N : Z.Opens}
    (hU : ⊤ ≤ (U.ι ≫ p ≫ i) ⁻¹ᵁ N) (hA' : ⊤ ≤ (A.ι ≫ p ≫ i) ⁻¹ᵁ N) (s : Γ(V, ⊤)) (g : Γ(Z, N))
    (hs : U.ι.appTop.hom s = ((U.ι ≫ p ≫ i).appLE N ⊤ hU).hom g) :
    A.ι.appTop.hom s = ((A.ι ≫ p ≫ i).appLE N ⊤ hA').hom g := by
  have e : V.homOfLE hA ≫ U.ι = A.ι := Scheme.homOfLE_ι _ _
  have h1 : A.ι.appTop.hom s = (V.homOfLE hA).appTop.hom (U.ι.appTop.hom s) := by
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  rw [h1, hs]
  have cg : ∀ (f g : (A : Scheme.{0}) ⟶ Z) (_ : f = g) (h : ⊤ ≤ f ⁻¹ᵁ N) (h' : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ h = g.appLE N ⊤ h' := by
    rintro f _ rfl _ _
    rfl
  have h3 : (V.homOfLE hA).appTop = (V.homOfLE hA).appLE ⊤ ⊤ (le_of_eq rfl) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 : (A.ι ≫ p ≫ i).appLE N ⊤ hA' =
      (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (V.homOfLE hA).appTop := by
    rw [h3]
    exact (cg _ _ (by rw [← e, Category.assoc]) _ _).trans
      (Scheme.Hom.appLE_comp_appLE (V.homOfLE hA) (U.ι ≫ p ≫ i) N ⊤ ⊤ hU (le_of_eq rfl)).symm
  rw [h2]
  rfl

private theorem pt_mem {V W Z : Scheme.{0}} (i : W ⟶ Z) (p : V ⟶ W) (U : V.Opens) {N : Z.Opens}
    (y : (U : Scheme.{0})) : (U.ι ≫ p ≫ i) y ∈ N ↔ (p ≫ i) y.1 ∈ N := by
  have : (U.ι ≫ p ≫ i) y = (p ≫ i) y.1 := by
    rw [Scheme.Hom.comp_apply]
    rfl
  rw [this]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β p M' → M = M' := by
  intro K _ W Z Y q i π D d B α β V p M M' hM hM'
  ext m l
  refine sectionExt _ _ fun x => ?_
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hMG⟩ := hM x
  obtain ⟨U', N', hx', hN', h₁', h₂', hU', G', hG', hMG'⟩ := hM' x
  have hzN : (p ≫ i) x ∈ N := (pt_mem i p U ⟨x, hx⟩).1 (hU (show (⟨x, hx⟩ : (U : Scheme.{0})) ∈ (⊤ : (U : Scheme.{0}).Opens) from trivial))
  have hzN' : (p ≫ i) x ∈ N' := (pt_mem i p U' ⟨x, hx'⟩).1 (hU' (show (⟨x, hx'⟩ : (U' : Scheme.{0})) ∈ (⊤ : (U' : Scheme.{0}).Opens) from trivial))
  obtain ⟨N'', hN'', hz, hsub⟩ := exists_isAffineOpen_mem_and_subset (U := N ⊓ N') (x := (p ≫ i) x) ⟨hzN, hzN'⟩
  have hle : N'' ≤ N := fun _ h => (hsub h).1
  have hle' : N'' ≤ N' := fun _ h => (hsub h).2
  let A : V.Opens := U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N''
  have hAU : A ≤ U := fun _ h => h.1.1
  have hAU' : A ≤ U' := fun _ h => h.1.2
  have hxA : x ∈ A := ⟨⟨hx, hx'⟩, hz⟩
  have hAz : ∀ y : (A : Scheme.{0}), (A.ι ≫ p ≫ i) y ∈ N'' := fun y => (pt_mem i p A y).2 y.2.2
  have hAN'' : ⊤ ≤ (A.ι ≫ p) ⁻¹ᵁ (i ⁻¹ᵁ N'') := by
    intro y _
    have := hAz y
    rw [← Category.assoc, Scheme.Hom.comp_apply] at this
    exact this
  have hAN : ⊤ ≤ (A.ι ≫ p ≫ i) ⁻¹ᵁ N := fun y _ => hle (hAz y)
  have hAN' : ⊤ ≤ (A.ι ≫ p ≫ i) ⁻¹ᵁ N' := fun y _ => hle' (hAz y)
  refine ⟨A, hxA, ?_⟩
  have e1 := pull_eq i p hAU hU hAN (M m l) (G m l) (congrFun (congrFun hMG m) l)
  have e2 := pull_eq i p hAU' hU' hAN' (M' m l) (G' m l) (congrFun (congrFun hMG' m) l)
  have t := trUnique B α β hN'' (hle.trans h₁) (hle.trans h₂)
    (G.map (Z.presheaf.map (homOfLE hle).op).hom) (G'.map (Z.presheaf.map (homOfLE hle').op).hom)
    (res_isTr B α β hle h₁ h₂ G hG) (res_isTr B α β hle' h₁' h₂' G' hG') m l
  rw [e1, e2, appLE_factor (A.ι ≫ p) i _ (Category.assoc _ _ _).symm hle hAN hAN'',
    appLE_factor (A.ι ≫ p) i _ (Category.assoc _ _ _).symm hle' hAN' hAN'']
  exact congrArg _ t
