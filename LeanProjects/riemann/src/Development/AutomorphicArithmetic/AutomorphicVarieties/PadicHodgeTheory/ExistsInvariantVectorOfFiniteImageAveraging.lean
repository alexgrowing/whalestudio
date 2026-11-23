import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_finite_image {Γ L D W : Type} [Group Γ] [Field L] [AddCommGroup D] [Module L D]
    [AddCommGroup W] [Module ℂ W] (a : Γ →* Module.End L D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (Γ ⧸ a.ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hn
  push Not at hn
  let := Fintype.ofFinite (Γ ⧸ a.ker)
  let a' : Γ ⧸ a.ker →* Module.End L D := QuotientGroup.lift a.ker a le_rfl
  have ha : ∀ q : Γ ⧸ a.ker, a q.out = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h0 : ∀ x : D, ∑ q : Γ ⧸ a.ker, a' q x = 0 := fun x => by
    by_contra hx
    obtain ⟨g, hg⟩ := hn _ hx
    refine hg ?_
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (g : Γ ⧸ a.ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have h1 : (∑ q : Γ ⧸ a.ker, b q.out) = 0 := by
    refine LinearMap.ext_on_range hs fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [hc, ha]
    rw [← map_sum, h0, map_zero]
  have h2 := LinearMap.congr_fun h1 y
  rw [LinearMap.sum_apply, LinearMap.zero_apply] at h2
  simp only [hi, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h2
  exact hy ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem UpperTheory.exists_invariant_vector_of_finite_image_averaging :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → (∀ y : WDSpace P ι ρ, (∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) ∧ ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1 h2
  refine ⟨?_, fun x hx σ => ?_⟩
  · obtain ⟨y, hy, hi⟩ := h1
    have := compactSpace_Ine (E := F) A
    have : Finite (Ine (F := F) A ⧸ (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker) :=
      Subgroup.quotient_finite_of_isOpen _ (isSmooth_weilD Bw h P ρ hj)
    exact UpperTheory.fixed_vector_descends_finite_image (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h))
      (MonoidHom.comp (wdRho P ι Bw h hj ρ) (ineIncl h))
      (AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)) (span_wdMk P ι ρ)
      (fun g x => wdRho_mk P ι Bw h hj ρ _ x) y hy hi
  · have hc : ∀ (n : ℕ) τ, Commute (phiD P ρ ^ n) (weilD Bw h P ρ τ) := fun n τ => by
      refine Commute.pow_left ?_ n
      rw [weilD_apply]
      refine Commute.mul_right (phiD_actD P ρ _) ?_
      exact Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _
    have hc' : ∀ (n : ℕ) τ, weilD Bw h P ρ τ ((phiD P ρ ^ n) x) = (phiD P ρ ^ n) (weilD Bw h P ρ τ x) :=
      fun n τ => (LinearMap.congr_fun (hc n τ).eq x).symm
    refine sub_eq_zero.mp
      (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L V ρ _ fun n => ?_)
    have h3 := h2 (wdMk P ι ρ ((phiD P ρ ^ n) x)) (fun s => by rw [wdRho_mk, hc', hx]) σ
    rw [wdRho_mk, hc'] at h3
    have h4 := wdMk_add P ι ρ ((phiD P ρ ^ n) (weilD Bw h P ρ σ x - x)) ((phiD P ρ ^ n) x)
    rw [← map_add, sub_add_cancel, h3] at h4
    exact left_eq_add.mp (h4.trans (add_comm _ _))
