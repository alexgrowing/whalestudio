import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TrExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GlueSection
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appTop_appLE {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (N : C.Opens) (e₁ : ⊤ ≤ g ⁻¹ᵁ N) (e₂ : ⊤ ≤ k ⁻¹ᵁ N) (s : Γ(C, N)) :
    f.appTop.hom ((g.appLE N ⊤ e₁).hom s) = (k.appLE N ⊤ e₂).hom s := by
  subst h
  have e₀ : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h₀ : f.appLE ⊤ ⊤ e₀ = f.appTop := Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  have h := Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ e₁ e₀
  rw [h₀] at h
  rw [← h]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α ⊓ B.V β) → ∃ M : Matrix (Fin d) (Fin d) Γ(V, ⊤), LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p hp
  have hN : ∀ x : V, ∃ N : Z.Opens, IsAffineOpen N ∧ (p ≫ i) x ∈ N ∧ N ≤ B.V α ⊓ B.V β := fun x => by
    obtain ⟨N, h1, h2, h3⟩ := exists_isAffineOpen_mem_and_subset (hp x)
    exact ⟨N, h1, h2, h3⟩
  choose N hNa hNx hNle using hN
  have h₁ : ∀ x, N x ≤ B.V α := fun x => (hNle x).trans inf_le_left
  have h₂ : ∀ x, N x ≤ B.V β := fun x => (hNle x).trans inf_le_right
  choose G hG using fun x => trExists B α β (hNa x) (h₁ x) (h₂ x)
  let U : V → V.Opens := fun x => (p ≫ i) ⁻¹ᵁ N x
  have hxU : ∀ x, x ∈ U x := hNx
  have hU : ∀ x, ⊤ ≤ ((U x).ι ≫ p ≫ i) ⁻¹ᵁ N x := by
    intro x y _
    exact y.2
  let Mx : ∀ x, Matrix (Fin d) (Fin d) Γ((U x : Scheme.{0}), ⊤) := fun x =>
    (G x).map (((U x).ι ≫ p ≫ i).appLE (N x) ⊤ (hU x)).hom
  have hL : ∀ x, LocMat B α β ((U x).ι ≫ p) (Mx x) := by
    intro x y
    have hT : ⊤ ≤ ((⊤ : (U x : Scheme.{0}).Opens).ι ≫ ((U x).ι ≫ p) ≫ i) ⁻¹ᵁ N x := by
      intro z _
      exact z.1.2
    refine ⟨⊤, N x, trivial, hNa x, h₁ x, h₂ x, hT, G x, hG x, ?_⟩
    ext a b
    exact appTop_appLE _ _ _ (by simp) _ _ _ _
  have hglue : ∀ a b, ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = Mx x a b := by
    intro a b
    refine glueSection U hxU (fun x => Mx x a b) ?_
    intro x y S f f' hff
    have n1 := locMatNat B α β f ((U x).ι ≫ p) (Mx x) (hL x)
    have n2 := locMatNat B α β f' ((U y).ι ≫ p) (Mx y) (hL y)
    have e : f ≫ (U x).ι ≫ p = f' ≫ (U y).ι ≫ p := by
      rw [← Category.assoc, hff, Category.assoc]
    rw [e] at n1
    have := locMatUnique B α β _ _ _ n1 n2
    exact congrFun (congrFun this a) b
  choose M hM using hglue
  refine ⟨Matrix.of M, fun x => ⟨U x, N x, hxU x, hNa x, h₁ x, h₂ x, hU x, G x, hG x, ?_⟩⟩
  ext a b
  exact hM a b x
