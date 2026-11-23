import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift

theorem dual_eq_sum_of_ker {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P)
    (hx : ∀ c, ρ (x c) = 0) :
    ∃ (n : ℕ) (j : Fin n → R) (d : Fin n → Module.Dual R P), (∀ k, ρ (j k) = 0) ∧
      x = ∑ k, j k • d k := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun k ↦ x (f (Pi.single k 1)), fun k ↦ (LinearMap.proj k) ∘ₗ s, fun k ↦ hx _, ?_⟩
  ext c
  have e1 : s c = ∑ k, s c k • (Pi.single k (1 : R) : Fin n → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have e2 : x c = x (f (s c)) := by rw [← LinearMap.comp_apply f s, hs, LinearMap.id_apply]
  rw [e2, e1, map_sum, map_sum]
  simp [mul_comm]

theorem isAdmissible_reduce : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hs g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h hi hA hg F hF
  obtain ⟨PF, -, PB, -, -⟩ := P
  letI : Algebra R R₁ := ρ.toAlgebra
  have hbc : (AbelianDeRham.bcMor h₂).IsBC := (PB R A g hA hg R₁ A₁ i₂ h₂).1
  obtain ⟨hfin, hproj, -⟩ := PF.prim hA hg

  have hPs : Function.Surjective (redMor h₂).pull := by
    intro c₁
    obtain ⟨z, rfl⟩ := hbc.2 c₁
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul r c =>
      obtain ⟨r', rfl⟩ := hs.surj r
      exact ⟨r' • c, by rw [liftSemi_tmul, LinearMap.map_smulₛₗ]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  have hex : ∀ x : HdR A, ∃ y : HdR A₁, (redMor h₂).Corr x y := fun x ↦ hbc.exists x
  have huniq : ∀ {x : HdR A} {y y' : HdR A₁}, (redMor h₂).Corr x y → (redMor h₂).Corr x y' → y = y' := by
    intro x y y' e e'
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [e c, e' c]
  have hlift : ∀ y : HdR A₁, ∃ x : HdR A, (redMor h₂).Corr x y := by
    intro y
    let l : primDR A →ₗ[R] R₁ :=
      { toFun c := y ((redMor h₂).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₁) l hs.surj
    exact ⟨x, fun c ↦ (LinearMap.congr_fun hx c).symm⟩
  let S : Submodule R (HdR A) → Submodule R₁ (HdR A₁) := fun F ↦
    { carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
      add_mem' := by
        rintro a b ⟨x, hx, ex⟩ ⟨x', hx', ex'⟩
        exact ⟨x + x', F.add_mem hx hx', fun c ↦ by simp [ex c, ex' c]⟩
      zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
      smul_mem' := by
        rintro r₁ y ⟨x, hx, ex⟩
        obtain ⟨r, rfl⟩ := hs.surj r₁
        exact ⟨r • x, F.smul_mem r hx, fun c ↦ by simp [ex c]⟩ }
  have comp : ∀ c, (redMor h₁).pull ((redMor h₂).pull c) = (redMor h).pull c :=
    fun c ↦ GrpMor.pull_pull (redMor h₂) (redMor h₁) (redMor h) (fun r ↦ RingHom.congr_fun hs.comp r) hi c
  obtain ⟨⟨N, hN⟩, hFil⟩ := hF
  refine ⟨S F, ⟨⟨S N, ⟨?_, ?_⟩⟩, fun y ↦ ?_⟩, fun y ↦ Iff.rfl⟩
  · refine Submodule.disjoint_def.2 fun y ⟨f, hf, ef⟩ ⟨n, hn, en⟩ ↦ ?_
    have hx : ∀ c, ρ ((f - n) c) = 0 := fun c ↦ by
      rw [LinearMap.sub_apply, map_sub, ← ef c, ← en c, sub_self]
    obtain ⟨k, j, d, hj, hsum⟩ := dual_eq_sum_of_ker ρ (f - n) hx
    have hfp : f = (Submodule.linearProjOfIsCompl F N hN (f - n) : HdR A) := by
      have e1 : Submodule.linearProjOfIsCompl F N hN f = ⟨f, hf⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hN ⟨f, hf⟩
      have e2 : Submodule.linearProjOfIsCompl F N hN n = 0 :=
        (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN).2 hn
      rw [map_sub, e1, e2, sub_zero]
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [ef c, hfp, hsum]
    simp [map_sum, Submodule.coe_sum, hj]
  · refine codisjoint_iff_le_sup.2 fun y _ ↦ ?_
    obtain ⟨x, ex⟩ := hlift y
    obtain ⟨f, hf, n, hn, rfl⟩ := Submodule.mem_sup.1 (hN.sup_eq_top ▸ Submodule.mem_top : x ∈ F ⊔ N)
    obtain ⟨yf, ef⟩ := hex f
    obtain ⟨yn, en⟩ := hex n
    refine Submodule.mem_sup.2 ⟨yf, ⟨f, hf, ef⟩, yn, ⟨n, hn, en⟩, huniq (fun c ↦ ?_) ex⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, ef c, en c, map_add]
  · rw [hFil y]
    constructor
    · rintro ⟨x, hx, e⟩
      obtain ⟨x₁, e₁⟩ := hex x
      refine ⟨x₁, ⟨x, hx, e₁⟩, fun c₁ ↦ ?_⟩
      obtain ⟨c, rfl⟩ := hPs c₁
      rw [comp, e c, e₁ c]
      exact (RingHom.congr_fun hs.comp _).symm
    · rintro ⟨x₁, ⟨x, hx, e₁⟩, e⟩
      exact ⟨x, hx, fun c ↦ by rw [← comp, e, e₁ c]; exact RingHom.congr_fun hs.comp _⟩

end GlobalTheory.SqLift
