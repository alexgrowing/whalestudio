import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rTensor_eq_zero_iff_mem_smul {R A A' P : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] (π : A →ₐ[R] A')
    (hπ : Function.Surjective π) (w : A ⊗[R] P) :
    π.toLinearMap.rTensor P w = 0 ↔
      w ∈ (RingHom.ker π) • (⊤ : Submodule A (A ⊗[R] P)) := by
  constructor
  · intro hw
    have hex : Function.Exact ((RingHom.ker π).restrictScalars R).subtype π.toLinearMap := by
      intro a
      constructor
      · intro h
        exact ⟨⟨a, (RingHom.mem_ker (f := π)).mpr h⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact (RingHom.mem_ker (f := π)).mp k.2
    obtain ⟨v, rfl⟩ := ((rTensor_exact P hex hπ) w).mp hw
    clear hw
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul k p =>
      rw [LinearMap.rTensor_tmul, Submodule.coe_subtype]
      have e : (k : A) ⊗ₜ[R] p = (k : A) • ((1 : A) ⊗ₜ[R] p) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e]
      exact Submodule.smul_mem_smul k.2 Submodule.mem_top
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · intro hw
    refine Submodule.smul_induction_on hw (fun k hk x _hx => ?_) ?_
    · clear _hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
        rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
          map_mul, (RingHom.mem_ker (f := π)).mp hk, MulZeroClass.zero_mul, TensorProduct.zero_tmul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]

theorem lTensor_rTensor_apply {R A A' P P' : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (π : A →ₐ[R] A') (f : P →ₗ[R] P') (w : A ⊗[R] P) :
    f.lTensor A' (π.toLinearMap.rTensor P w) = π.toLinearMap.rTensor P' (f.lTensor A w) := by
  induction w with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a p => simp

private theorem lift_of_smallLift_lemma {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A) (t : A) :
    RingHom.ker ((Ideal.Quotient.mkₐ R (Ideal.span {Ideal.Quotient.mk J t})).comp (Ideal.Quotient.mkₐ R J)) =
      J ⊔ Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

theorem lift_of_smallLift : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  intro R P₀ P₁ P₂ A _ _ _ _ _ _ _ _ _ _ a₀ a₁ h01 hS
  intro J t hJ hJt z hz
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  set t' : A ⧸ J := Ideal.Quotient.mk J t with ht'
  set ρ : A →ₐ[R] (A ⧸ J) ⧸ Ideal.span {t'} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {t'})).comp (Ideal.Quotient.mkₐ R J) with hρ
  have hρs : Function.Surjective ρ :=
    (Ideal.Quotient.mkₐ_surjective R _).comp (Ideal.Quotient.mkₐ_surjective R J)
  have hker : RingHom.ker ρ = J ⊔ Ideal.span {t} := lift_of_smallLift_lemma J t
  have hJs : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hkerJ : RingHom.ker (Ideal.Quotient.mkₐ R J) = J := Ideal.Quotient.mkₐ_ker R J
  have ht : ∀ x : A ⧸ J, ¬ IsUnit x → x * t' = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx (hu.map _)
    rw [ht', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hJt x hx'
  set z' := ρ.toLinearMap.rTensor P₁ z with hz'
  have hz2 : (a₁.lTensor A) z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A (A ⊗[R] P₂)) := by
    rwa [LinearMap.baseChange_eq_ltensor] at hz
  have hz0 : a₁.lTensor _ z' = 0 := by
    rw [hz', lTensor_rTensor_apply, rTensor_eq_zero_iff_mem_smul ρ hρs, hker]
    exact hz2
  obtain ⟨xb, y, hx0, hxy⟩ := hS (A ⧸ J) t' ht z' hz0
  obtain ⟨x₁, rfl⟩ := LinearMap.rTensor_surjective P₁ (g := (Ideal.Quotient.mkₐ R J).toLinearMap) hJs xb
  obtain ⟨y₁, rfl⟩ := LinearMap.rTensor_surjective P₀ (g := ρ.toLinearMap) hρs y
  have hcomp : ρ.toLinearMap.rTensor P₁ x₁ = (Ideal.Quotient.mkₐ R (Ideal.span {t'})).toLinearMap.rTensor P₁
      ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor P₁ x₁) := by
    rw [hρ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
  refine ⟨x₁ - a₀.lTensor A y₁, ?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor, map_sub]
    have h0 : a₁.lTensor A (a₀.lTensor A y₁) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h01, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rw [h0, sub_zero, ← hkerJ, ← rTensor_eq_zero_iff_mem_smul _ hJs, ← lTensor_rTensor_apply]
    exact hx0
  · rw [← hker, ← rTensor_eq_zero_iff_mem_smul ρ hρs, map_sub, map_sub, ← lTensor_rTensor_apply, hcomp, ← hz',
      sub_right_comm, hxy, sub_self]

end GlobalTheory.CompanionTheory.PerfVB
