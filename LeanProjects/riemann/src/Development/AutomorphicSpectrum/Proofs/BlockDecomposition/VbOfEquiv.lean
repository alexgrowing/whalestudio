import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallLiftBaseChangeLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGeneralizedInverseOfUnitKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyDataStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComplexUnitElementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComparisonDegreeOneBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelSteinOfComparisonStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapCompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PerfVB

theorem vb_of_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) {g : ℕ} (h : VB R M g) : VB R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv E, Module.Projective.of_equiv E, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E]
  exact h3 p

theorem vb_pure {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [Module.Finite R P₀]
    [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂]
    [Module.Projective R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (hc : a₁ ∘ₗ a₀ = 0) (g : ℕ)
    (e : P₀) (he : a₀ e = 0)
    (hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e))
    (hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g)
    (hL : SmallLift a₀ a₁) : VB R (Hc (a₀.baseChange R) (a₁.baseChange R)) g := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generalized_inverse_of_unit_kernel R P₀ P₁ a₀ e he hE
  obtain ⟨s, hs⟩ := GlobalTheory.T.local_splitting_global_generalized_inverse R P₁ P₂ a₁ (fun m _ => by
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₁) :=
      Module.free_of_flat_of_isLocalRing
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₂) :=
      Module.free_of_flat_of_isLocalRing
    exact GlobalTheory.T.generalized_inverse_of_lift_local _ _ _ _ (GlobalTheory.T.small_lift_base_change_local R P₀ P₁ P₂ _ a₀ a₁ hc hL))
  obtain ⟨j, π, h, h', hπj, haj, hπa, hsum⟩ := GlobalTheory.T.split_complex_homotopy_data R P₀ P₁ P₂ a₀ a₁ t s hc ht hs
  have hP := Module.Projective.of_split j π hπj
  have hsurj : Function.Surjective π := fun x => ⟨j x, by simpa using LinearMap.congr_fun hπj x⟩
  have hF := Module.Finite.of_surjective π hsurj
  obtain ⟨eR⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ R a₀ a₁ j π h h' hc hπj haj hπa hsum
  refine vb_of_equiv (eR.trans (TensorProduct.lid R _)).symm ⟨hF, hP, GlobalTheory.T.constant_fibre_rank_stalk_rank R _ g ?_⟩
  intro k _ _
  obtain ⟨ek⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ k a₀ a₁ j π h h' hc hπj haj hπa hsum
  rw [← ek.finrank_eq]
  exact hG k

theorem small_lift {R C P₀ P₁ P₂ : Type} [CommRing R] [Category.{0} C]
    (hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : C ⥤ CommAlgCat.{0} R)
      (F' : C ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m))
    (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (hM : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂)
    (hs : ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B),
      (∀ x, ¬ IsUnit x → x * t = 0) →
      ∃ (F' : C ⥤ CommAlgCat.{0} B) (_ : BC F F') (F'' : C ⥤ CommAlgCat.{0} (B ⧸ Ideal.span {t}))
        (m : BC F' F''), Function.Surjective m.coef.pull1) : SmallLift a₀ a₁ := by
  intro B _ _ _ t ht z hz
  obtain ⟨F', m0, F'', m, hsurj⟩ := hs B t ht
  obtain ⟨l, hl⟩ := GlobalTheory.T.base_change_map_composition R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m
  obtain ⟨b0', b1', b2'⟩ := hbij B F F' m0
  obtain ⟨b0'', b1'', b2''⟩ := hbij (B ⧸ Ideal.span {t}) F F'' l
  obtain ⟨e', he'⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R B C P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m0 hM b0' b1' b2'
  obtain ⟨e'', he''⟩ :=
    GlobalTheory.T.model_comparison_degree_one_bijective R (B ⧸ Ideal.span {t}) C P₀ P₁ P₂ F F'' a₀ a₁ ψ₀ ψ₁ ψ₂ l hM b0'' b1'' b2''
  have hmk : (Ideal.Quotient.mkₐ R (Ideal.span {t})) = IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t}) := by
    ext b
    rfl
  have hzk : z ∈ (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := LinearMap.mem_ker.2 hz
  obtain ⟨w, hw⟩ := hsurj (e'' (Submodule.Quotient.mk ⟨z, hzk⟩))
  obtain ⟨q, rfl⟩ := e'.surjective w
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hxk : LinearMap.lTensor B a₁ x = 0 := LinearMap.mem_ker.1 hx
  have hxbk : LinearMap.rTensor P₁ (IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t})).toLinearMap x ∈
      (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := by
    rw [LinearMap.mem_ker]
    change LinearMap.lTensor (B ⧸ Ideal.span {t}) a₁ _ = 0
    rw [GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply, hxk, map_zero]
  have key : e'' (Submodule.Quotient.mk ⟨_, hxbk⟩) = e'' (Submodule.Quotient.mk ⟨z, hzk⟩) := by
    rw [← hw]
    obtain ⟨hw1, h1⟩ := he'' _ hxbk
    obtain ⟨hw2, h2⟩ := he' x hx
    rw [h1, h2]
    have hp : ∀ c, m.coef.pull1 (GlobalTheory.CatCoh.H1.mk F' c) = GlobalTheory.CatCoh.H1.mk F'' (m.coef.pullbackOneCocycle c) :=
      fun c => rfl
    rw [hp]
    congr 1
    apply Subtype.ext
    show th1 l _ = c1 m (th1 m0 _)
    rw [← GlobalTheory.T.comparison_degree_one_tower_formula R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m l hl]
    congr 1
    exact GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply _ _ _
  have hq := (Submodule.Quotient.eq _).1 (e''.injective key)
  rw [Submodule.mem_comap] at hq
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hq
  refine ⟨x, y, hxk, ?_⟩
  rw [hmk]
  rw [map_sub, Submodule.subtype_apply, Submodule.subtype_apply] at hy
  exact hy.symm

theorem perfVB : PerfVBSt := by
  unfold MainStatements.Hodge.PerfVBSt MainStatements.Hodge.AllFin
  intro R _ P _ _ F g hPerf hSt hfib hsm
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, ⟨f3, p3⟩, h10, h21, hψ1, hψ2,
    ⟨ψ₃, hψ3⟩, hQ⟩ := hPerf
  have hMod : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ := ⟨h10, hψ1, hψ2, fun M => ⟨(hQ M).1, (hQ M).2.1⟩⟩
  obtain ⟨e, he, hψe⟩ := GlobalTheory.T.model_complex_unit_element R Pᵒᵖ P₀ P₁ P₂ F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod
  have hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
      (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
    intro S _ _ F F' m
    exact GlobalTheory.T.comparison_maps_bijective_finite R S P F F' m
  have hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
    intro k _ _ x hx
    obtain ⟨F', m, hS⟩ := hSt k
    exact GlobalTheory.T.model_stein_of_comparison R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m e hMod (hbij k F F' m).1 hS he hψe x hx
  have hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hm⟩ := hfib k
    obtain ⟨b0, b1, b2⟩ := hbij k F F' m
    obtain ⟨ek, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m hMod b0 b1 b2
    rw [ek.finrank_eq]
    exact hm
  have hL : SmallLift a₀ a₁ := small_lift hbij F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod (fun B _ _ _ t ht => hsm B t ht)
  haveI := f0
  haveI := p0
  haveI := f1
  haveI := p1
  haveI := f2
  haveI := p2
  have hv := vb_pure a₀ a₁ h10 g e he hE hG hL
  obtain ⟨l, -⟩ := GlobalTheory.T.base_change_map_identity R Pᵒᵖ F
  obtain ⟨c0, c1, c2⟩ := hbij R F F l
  obtain ⟨eR, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R R Pᵒᵖ P₀ P₁ P₂ F F a₀ a₁ ψ₀ ψ₁ ψ₂ l hMod c0 c1 c2
  exact vb_of_equiv eR hv

end GlobalTheory.CompanionTheory.PerfVB
