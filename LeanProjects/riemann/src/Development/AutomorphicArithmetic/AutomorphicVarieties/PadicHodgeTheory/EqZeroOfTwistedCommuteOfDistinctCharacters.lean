import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.linearIndependent_distinct_characters {Γ W ι : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    (ρ : Γ →* Module.End ℂ W) (χ : ι → Γ →* ℂˣ) (y : ι → W) (hy : ∀ i, y i ≠ 0)
    (he : ∀ i σ, ρ σ (y i) = (χ i σ : ℂ) • y i) (hχ : Function.Injective χ) :
    LinearIndependent ℂ y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hinj : Function.Injective (fun i => (Units.coeHom ℂ).comp (χ i)) := by
    intro a b hab
    apply hχ
    ext σ
    exact DFunLike.congr_fun hab σ
  have hli := (linearIndependent_monoidHom Γ ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key : ∀ φ : Module.Dual ℂ W, c i * φ (y i) = 0 := by
    intro φ
    refine hli (fun j => c j * φ (y j)) ?_ i
    funext σ
    have h1 : φ (ρ σ (∑ j, c j • y j)) = 0 := by rw [hc, map_zero, map_zero]
    rw [map_sum, map_sum] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, he, map_smul, map_smul]
    simp only [Pi.smul_apply, Function.comp_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul]
    ring
  by_contra hci
  apply hy i
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  exact (mul_eq_zero.mp (key φ)).resolve_left hci

theorem UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters :
    ∀ {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ) (ν : Γ →* ℂˣ) (N : Module.End ℂ W), Module.finrank ℂ W = n → (∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y) → Function.Injective μ → (∀ j k, μ j ≠ μ k * ν) → (∀ σ, ρ σ * N = (ν σ : ℂ) • (N * ρ σ)) → N = 0 := by
  intro Γ W _ _ _ _ n ρ μ ν N hn hy hμ hlink hN
  choose y hy0 hye using hy
  have hli : LinearIndependent ℂ y := UpperTheory.linearIndependent_distinct_characters ρ μ y hy0 hye hμ
  have hNy : ∀ k, N (y k) = 0 := by
    intro k
    by_contra hk
    have h2 : LinearIndependent ℂ (fun o : Option (Fin n) => o.elim (N (y k)) y) := by
      refine UpperTheory.linearIndependent_distinct_characters ρ (fun o : Option (Fin n) => o.elim (μ k * ν) μ) _ ?_ ?_ ?_
      · rintro (_ | j)
        · exact hk
        · exact hy0 j
      · rintro (_ | j) σ
        · have h3 := LinearMap.congr_fun (hN σ) (y k)
          simp only [Module.End.mul_apply, LinearMap.smul_apply, hye, map_smul, smul_smul] at h3
          simp only [Option.elim_none, MonoidHom.mul_apply, Units.val_mul]
          rw [h3, mul_comm]
        · exact hye j σ
      · rintro (_ | a) (_ | b) hab
        · rfl
        · exact absurd hab.symm (hlink b k)
        · exact absurd hab (hlink a k)
        · exact congrArg some (hμ hab)
    have h4 := h2.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hn] at h4
    omega
  have hspan : Submodule.span ℂ (Set.range y) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hn])
  refine LinearMap.ext_on_range hspan fun k => ?_
  rw [hNy k, LinearMap.zero_apply]
