import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem UpperTheory.Gal.LocalSmoothExtension.homEx_of :
    HomEx := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  have ext'' : ∀ {T : Over S₁} (u v : T ⟶ o₁''.A), u.left ≫ m''.φ = v.left ≫ m''.φ → u = v := by
    intro T u v h
    apply Over.OverMorphism.ext
    exact m''.cart.1.hom_ext h (by rw [Over.w u, Over.w v])
  have p' : ∀ (T : Over S₁) (x : T ⟶ o₁'.A), (pushHom m'.cart T x).left = x.left ≫ m'.φ :=
    fun _ _ => rfl
  have p'' : ∀ (T : Over S₁) (x : T ⟶ o₁''.A), (pushHom m''.cart T x).left = x.left ≫ m''.φ :=
    fun _ _ => rfl
  refine ⟨?_, fun ψ₁ ψ₂ h => ext'' ψ₁ ψ₂ h, ?_⟩
  · intro ψ hψ
    haveI := hψ
    have w : (m'.φ ≫ ψ.left) ≫ o''.A.hom = o₁'.A.hom ≫ f := by
      rw [Category.assoc, Over.w ψ, m'.cart.1.w]
    let ψ₁ : o₁'.A ⟶ o₁''.A :=
      Over.homMk (m''.cart.1.lift (m'.φ ≫ ψ.left) o₁'.A.hom w) (m''.cart.1.lift_snd _ _ w)
    have hψ₁ : ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left := m''.cart.1.lift_fst _ _ w
    refine ⟨ψ₁, ?_, hψ₁⟩
    apply isMonHom_of_mul
    intro T x y
    apply ext''
    have e : ∀ z : T ⟶ o₁'.A, pushHom m''.cart T (z ≫ ψ₁) = pushHom m'.cart T z ≫ ψ := by
      intro z
      apply Over.OverMorphism.ext
      rw [p'', Over.comp_left, Over.comp_left, p', Category.assoc, Category.assoc, hψ₁]
    rw [← p'', ← p'', map_mul, e, e, e, map_mul, mul_comp]
  · intro d
    let e : Over.mk (o₁'.A.hom ≫ f) ⟶ o'.A := pushHom m'.cart o₁'.A (𝟙 o₁'.A)
    have h1 : (𝟙 o₁'.A ^ d).left ≫ m'.φ = (e ^ d).left := by
      rw [← p', map_pow]
    have h2 : m'.φ ≫ (𝟙 o'.A ^ d).left = (e ^ d).left := by
      have : e ≫ 𝟙 o'.A ^ d = e ^ d := by rw [comp_pow, Category.comp_id]
      rw [← this, Over.comp_left, p', Over.id_left, Category.id_comp]
    rw [h1, h2]
