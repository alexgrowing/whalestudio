import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.Cls

section Abstract

variable {S A₀ A₁ A₂ B₀ B₁ B₂ D₀ D₁ D₂ H : Type} [CommRing S]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup H]
  [Module S A₀] [Module S A₁] [Module S A₂] [Module S B₀] [Module S B₁] [Module S B₂]
  [Module S D₀] [Module S D₁] [Module S D₂] [Module S H]

theorem homology_equiv (a₀ : A₀ →ₗ[S] A₁) (a₁ : A₁ →ₗ[S] A₂) (b₀ : B₀ →ₗ[S] B₁)
    (b₁ : B₁ →ₗ[S] B₂) (e₀ : D₀ →ₗ[S] D₁) (e₁ : D₁ →ₗ[S] D₂) (f₀ : A₀ →ₗ[S] B₀)
    (f₁ : A₁ →ₗ[S] B₁) (f₂ : A₂ →ₗ[S] B₂) (t₀ : B₀ →ₗ[S] D₀) (t₁ : B₁ →ₗ[S] D₁)
    (t₂ : B₂ →ₗ[S] D₂) (Z : Submodule S D₁) (q : Z →ₗ[S] H)
    (hZ : Z = LinearMap.ker e₁) (hq : Function.Surjective q)
    (hq0 : ∀ z : Z, q z = 0 ↔ ∃ g, e₀ g = z.1)
    (hf₁ : ∀ y, f₁ (a₀ y) = b₀ (f₀ y)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (ht₁ : ∀ y, t₁ (b₀ y) = e₀ (t₀ y)) (ht₂ : ∀ x, t₂ (b₁ x) = e₁ (t₁ x))
    (ht₀s : Function.Surjective t₀) (ht₁b : Function.Bijective t₁)
    (ht₂i : Function.Injective t₂)
    (hinj : ∀ x, a₁ x = 0 → (∃ y, b₀ y = f₁ x) → ∃ y, a₀ y = x)
    (hsurj : ∀ z, b₁ z = 0 → ∃ x y, a₁ x = 0 ∧ f₁ x - z = b₀ y) :
    ∃ e : Hc a₀ a₁ ≃ₗ[S] H, ∀ (x : A₁) (hx : x ∈ LinearMap.ker a₁),
      ∃ hw : t₁ (f₁ x) ∈ Z, e (Submodule.Quotient.mk ⟨x, hx⟩) = q ⟨_, hw⟩ := by
  have hmem : ∀ x : LinearMap.ker a₁, (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype) x ∈ Z := by
    rintro ⟨x, hx⟩
    rw [hZ, LinearMap.mem_ker]
    have hx' : a₁ x = 0 := hx
    change e₁ (t₁ (f₁ x)) = 0
    rw [← ht₂, ← hf₂, hx', map_zero, map_zero]
  let Φ : LinearMap.ker a₁ →ₗ[S] H :=
    q ∘ₗ (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z hmem
  have hΦ : ∀ x : LinearMap.ker a₁, Φ x = q ⟨t₁ (f₁ x.1), hmem x⟩ := fun x ↦ rfl
  have hs : Function.Surjective Φ := by
    intro c
    obtain ⟨w, rfl⟩ := hq c
    obtain ⟨w₀, hw₀⟩ := ht₁b.2 w.1
    have hker : ∀ d, d ∈ Z → e₁ d = 0 := fun d hd ↦ by
      rw [hZ] at hd
      exact hd
    have hw : e₁ w.1 = 0 := hker _ w.2
    have hd : b₁ w₀ = 0 := ht₂i (by rw [ht₂, hw₀, hw, map_zero])
    obtain ⟨x, y, hx, hxy⟩ := hsurj w₀ hd
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hΦ, ← sub_eq_zero, ← map_sub, hq0]
    refine ⟨t₀ y, ?_⟩
    change e₀ (t₀ y) = t₁ (f₁ x) - w.1
    rw [← ht₁, ← hxy, map_sub, hw₀]
  have hk : (LinearMap.range a₀).comap (LinearMap.ker a₁).subtype = LinearMap.ker Φ := by
    ext ⟨x, hx⟩
    have hx' : a₁ x = 0 := hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_ker]
    rw [hΦ, hq0]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨t₀ (f₀ y), by simp only [← ht₁, hf₁]⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g₀, rfl⟩ := ht₀s g
      refine hinj x hx' ⟨g₀, ht₁b.1 ?_⟩
      rw [ht₁]
      exact hg
  refine ⟨(Submodule.quotEquivOfEq _ _ hk).trans (Φ.quotKerEquivOfSurjective hs), fun x hx ↦ ?_⟩
  exact ⟨hmem ⟨x, hx⟩, rfl⟩

end Abstract

variable {R S C : Type} [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

theorem comparison_degree_one_coboundary (m : BC F F') (x : S ⊗[R] C0 F) :
    th1 m ((d0 F).baseChange S x) = d0 F' (th0 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (g T' - mp F φ (g T)) = m.α T' (g T') - mp F' φ (m.α T (g T))
    rw [map_sub, m.naturality]

theorem comparison_degree_two_coboundary (m : BC F F') (x : S ⊗[R] C1 F) :
    th2 m ((d1 F).baseChange S x) = d1 F' (th1 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th2, th1, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' T'' φ ψ
    change m.α T'' (mp F ψ (g T T' φ) - g T T'' (φ ≫ ψ) + g T' T'' ψ) =
      mp F' ψ (m.α T' (g T T' φ)) - m.α T'' (g T T'' (φ ≫ ψ)) + m.α T'' (g T' T'' ψ)
    rw [map_add, map_sub, m.naturality]

theorem model_comparison_degree_zero_bijective (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)
    (m : BC F F') : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) →
      Function.Bijective (th1 m) → Function.Bijective (th2 m) →
      ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F',
        ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)),
          ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F',
            e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  rintro ⟨-, hc0, hc1, hq⟩ b0 b1 b2
  obtain ⟨-, hq2⟩ := hq (ModuleCat.of R S)
  refine homology_equiv (a₀.baseChange S) (a₁.baseChange S) ((d0 F).baseChange S)
    ((d1 F).baseChange S) (d0 F') (d1 F') (ψ₀.baseChange S) (ψ₁.baseChange S) (ψ₂.baseChange S)
    (th0 m) (th1 m) (th2 m) (Z1 F') (H1.mk F') (commAlgFunctorCocyclesOne_eq_ker F') (H1.mk_surjective F')
    (fun z ↦ H1.mk_eq_zero) ?_ ?_ (comparison_degree_one_coboundary m) (comparison_degree_two_coboundary m) b0.2 b1 b2.1 hq2.1 hq2.2
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc0, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc1, LinearMap.baseChange_comp,
      LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB.Cls
