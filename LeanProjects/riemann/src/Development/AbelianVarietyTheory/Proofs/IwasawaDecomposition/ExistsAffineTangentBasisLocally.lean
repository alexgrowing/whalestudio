import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart sp fB)

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem exists_univChart_pullback {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    ∃ xc : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ (Over.pullback x).obj t.G, IsUnivChart _ n xc ∧
      ∀ cc : Fin n → A, LieLocBasis.vec t x xc cc = (tvec (x := y) cc).left ≫ ψ := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback t.G x)
  refine ⟨fun m => y m ≫ e.hom, gfp_chart_iso e hy, fun cc => ?_⟩
  have key : (tvec (x := fun m => y m ≫ e.hom) cc).left = (tvec (x := y) cc).left ≫ e.hom.left := by
    show (_ ≫ y 1 ≫ e.hom).left = (_ ≫ y 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => y m ≫ e.hom) cc).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ]

theorem isTanBasis_of_chart {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart G₁) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    IsTanBasis t x fun j => (tvec (x := y) (Pi.single j 1)).left ≫ ψ := by
  refine ⟨fun j => ?_, fun S' _ φ w hw => ?_⟩
  · obtain ⟨xc, hx, hv⟩ := exists_univChart_pullback t x h hy
    have h1 := LieLocBasis.vec_tan hx (Pi.single j 1)
    rw [hv] at h1
    exact h1
  let _ : Algebra A S' := φ.toAlgebra
  obtain ⟨y', hy', e'⟩ := LieChart.univChart_baseChange_of_chart (R' := S') G₁ C n y hy
  obtain ⟨xc', hx', hv⟩ := exists_univChart_pullback t (spMap φ ≫ x)
    ((isGrpPullback_pullback G₁ (fB A S')).comp h) hy'
  obtain ⟨cc, rfl⟩ := LieLocBasis.vec_exists hx' w hw
  have hD : (fun j => spMap (dualMap φ) ≫ (tvec (x := y) (Pi.single j 1)).left ≫ ψ) =
      fun j => LieLocBasis.vec t (spMap φ ≫ x) xc' (Pi.single j 1) := by
    funext j
    have h1 : (Pi.single j 1 : Fin n → S') = algebraMap A S' ∘ (Pi.single j 1 : Fin n → A) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    rw [hv, h1, ← Category.assoc (tvec (x := y') _).left, e', Category.assoc]
    rfl
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (LieLocBasis.comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((LieLocBasis.comb_iff hx' _ _ _).1 ha).symm

theorem exists_affine_isTanBasis (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Scheme.{0}) (ρ : S ⟶ X) (z : S) :
    ∃ (V : S.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left)),
      z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e := by
  let G : Over S := (Over.pullback ρ).obj t.G
  have : Smooth G.hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom ρ)
    infer_instance
  obtain ⟨U, hU, V, hV, e, hxU, -, hs, h⟩ :=
    LieChart.exists_isStandardSmooth_section G.hom (η[G]).left (Over.w η[G]) z ⊤ trivial
  let i : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  let G₀ : Over (Spec (CommRingCat.of Γ(S, U))) := (Over.pullback i).obj G
  have hφ₀ : IsGrpPullback G₀ G i (pullback.fst G.hom i) := isGrpPullback_pullback G i
  obtain ⟨C, hC⟩ := LieChart.exists_chart_pullback G hU hV e hs h G₀ _ hφ₀
  obtain ⟨n, y, hy⟩ := LieChart.univChart_of_chart G₀ C hC
  exact ⟨⟨U, hU⟩, n, _, hxU,
    isTanBasis_of_chart t (i ≫ ρ) (hφ₀.comp (isGrpPullback_pullback t.G ρ)) C hy⟩

end GlobalTheory.LineNorm
