import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LetterEigen

theorem prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (u : Fin n → M) (i : Fin n), (∀ j, j ≠ i → u j = 1) → (List.ofFn u).prod = u i
  | 0, _, i, _ => i.elim0
  | n + 1, u, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (motive := fun i => (∀ j, j ≠ i → u j = 1) →
      u 0 * (List.ofFn fun k : Fin n => u k.succ).prod = u i) (fun h => ?_) (fun i h => ?_) i h
    · rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero k)
    · rw [h 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact prod_ofFn_eq_single (fun k : Fin n => u k.succ) i
        (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e)))

theorem left_eq_of_isLieComb_single {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : R) {w : epsR R ⟶ G}
    (hw : IsLieComb (Pi.single i t) v w) : w.left = spMap (epsScaleR t) ≫ (v i).left := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [prod_ofFn_eq_single u i, hu i, Pi.single_eq_same]
  intro j hj
  have h0 := (LieMultiple.isLieComb_one_iff (0 : R) (v j) 1).1
    ((LieMultiple.lieMultiple_calculus R G G (v j) 1 1 0 0).2.2.2.2.2 (hv j))
  apply Over.OverMorphism.ext
  rw [hu j, Pi.single_eq_of_ne hj, h0]

theorem exists_scale_of_eigen {K : Type} [Field K] [NumberField K] {A B : Over (Sp (𝓞 K))} {A' B' : Over (Sp K)}
    [GrpObj A'] [GrpObj B'] {n : ℕ} {v : Fin n → (epsR K ⟶ A')} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : K)
    (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (α : A ⟶ A) (β : B ⟶ B) (F : A ⟶ B) (hF : α ≫ F = F ≫ β)
    {w₁ : epsR K ⟶ A'} (hw₁ : IsLieComb (Pi.single i t) v w₁) (he : (v i).left ≫ φA ≫ α.left = w₁.left ≫ φA)
    {w : epsR K ⟶ B'} (hw : w.left ≫ φB = (v i).left ≫ φA ≫ F.left) :
    ∃ w' : epsR K ⟶ B', IsLieComb ![t] ![w] w' ∧ w.left ≫ φB ≫ β.left = w'.left ≫ φB := by
  have hc : IsLieComb ![t] ![w] (Chart.spMap (Chart.scaleD t) ≫ w) :=
    (LieMultiple.isLieComb_one_iff_comp t w _).2 rfl
  refine ⟨_, hc, ?_⟩
  have hF' : α.left ≫ F.left = F.left ≫ β.left := by
    rw [← Over.comp_left, hF, Over.comp_left]
  rw [(LieMultiple.isLieComb_one_iff t w _).1 hc, Category.assoc, hw, reassoc_of% hw, ← hF', reassoc_of% he,
    left_eq_of_isLieComb_single hv i t hw₁, Category.assoc]

theorem letter_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (b : E →+* ℂ) (i : Fin (L.m b)) (w : epsR o.K₁ ⟶ o.xB.P.A), L.IsLetter (L.e ⟨b, i⟩) w → ∀ a : 𝓞 E, ∃ w' : epsR o.K₁ ⟶ o.xB.P.A, IsLieComb ![labK c o.K₁ b (a : E)] ![w] w' ∧ w.left ≫ o.φB ≫ (o.oa.act a).left = w'.left ≫ o.φB := by
  intro E _ _ _ _ H l c nΨ n' f o La ho L hL b i w hw a
  obtain ⟨-, -, -, -, -, -, -, -, -, hΨ, h', eΨ, e', -⟩ := ho
  have hb := hL.2.1 b i
  unfold LamLetters.IsLetter at hw
  generalize L.src (L.e ⟨b, i⟩) = s at hb hw
  rcases s with q | q
  · obtain ⟨w₁, h₁, h₂⟩ := hΨ a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.xΨ.basis.1 q.2 _ _ _ _ _ _ (eΨ q.1 a) h₁ h₂ hw
  · obtain ⟨w₁, h₁, h₂⟩ := h' a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.x'.basis.1 q.2 _ _ _ _ _ _ (e' q.1 a) h₁ h₂ hw

end GlobalTheory.LamF.LetterEigen
