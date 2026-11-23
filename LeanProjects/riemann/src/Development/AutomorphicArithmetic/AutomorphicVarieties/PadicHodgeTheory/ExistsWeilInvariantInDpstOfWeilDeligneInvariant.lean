import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_weil_group {Γ I K D W : Type} [Group Γ] [Group I] [Field K] [CharZero K]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (j : I →* Γ) (φ : Γ) (hn : ∀ s, ∃ t, j s * φ = φ * j t) (hg : ∀ σ, ∃ (n : ℤ) (t : I), σ = φ ^ n * j t)
    (a : Γ →* Module.End K D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (I ⧸ (a.comp j).ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hno
  let := Fintype.ofFinite (I ⧸ (a.comp j).ker)
  let a' : I ⧸ (a.comp j).ker →* Module.End K D := QuotientGroup.lift _ (a.comp j) le_rfl
  have ha : ∀ q : I ⧸ (a.comp j).ker, a (j q.out) = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let n : ℕ := Fintype.card (I ⧸ (a.comp j).ker)
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let E : Module.End K D := ∑ q : I ⧸ (a.comp j).ker, a (j q.out)
  let E' : Module.End ℂ W := ∑ q : I ⧸ (a.comp j).ker, b (j q.out)
  have hE : ∀ x s, a (j s) (E x) = E x := fun x s => by
    simp only [E, LinearMap.sum_apply, map_sum, ha]
    refine Fintype.sum_equiv (Equiv.mulLeft (s : I ⧸ (a.comp j).ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have hE1 : ∀ z, (∀ s, a (j s) z = z) → E z = n • z := fun z hz => by
    simp only [E, LinearMap.sum_apply, hz, Finset.sum_const, Finset.card_univ, n]
  have hE2 : E' y = n • y := by
    simp only [E', LinearMap.sum_apply, hi, Finset.sum_const, Finset.card_univ, n]
  have hEE : ∀ x, E' (mk x) = mk (E x) := fun x => by
    simp only [E, E', LinearMap.sum_apply, hc, map_sum]
  have hcan : ∀ z : D, n • z = 0 → z = 0 := fun z hz => by
    rw [← Nat.cast_smul_eq_nsmul K] at hz
    exact (smul_eq_zero.mp hz).resolve_left hn0
  let S : Module.End K D := a φ * E - E + n • 1 - E
  let S' : Module.End ℂ W := b φ * E' - E' + n • 1 - E'
  have hS : ∀ x, S x = a φ (E x) - E x + n • x - E x := fun x => rfl
  have hS' : ∀ x, S' x = b φ (E' x) - E' x + n • x - E' x := fun x => rfl
  have hinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ s, a (j s) (a φ (E x)) = a φ (E x) := fun s => by
      obtain ⟨t, ht⟩ := hn s
      rw [← Module.End.mul_apply, ← map_mul, ht, map_mul, Module.End.mul_apply, hE]
    have h2 := congrArg E hx
    rw [hS, map_sub, map_add, map_sub, map_nsmul, hE1 _ h1, hE1 _ (hE x), map_zero, add_sub_cancel_right,
      ← smul_sub] at h2
    have h3 : a φ (E x) = E x := sub_eq_zero.mp (hcan _ h2)
    have h4 : E x = 0 := by
      by_contra h0
      refine hno ⟨_, h0, fun g => ?_⟩
      obtain ⟨m, t, rfl⟩ := hg g
      rw [map_mul, Module.End.mul_apply, hE]
      exact (GlobalTheory.PstLaws.vecStab a (E x)).zpow_mem h3 m
    rw [hS, h4, map_zero, sub_zero, sub_zero, zero_add] at hx
    exact hcan _ hx
  have hsur := LinearMap.injective_iff_surjective.mp hinj
  have hsur' : Function.Surjective S' := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsur x
    refine ⟨mk z, ?_⟩
    rw [hS, hS', hEE, hc, map_sub, map_add, map_sub, map_nsmul]
  refine hy (LinearMap.injective_iff_surjective.mpr hsur' ?_)
  rw [hS', hE2, map_nsmul, hi, map_zero, sub_self, zero_add, sub_self]

theorem UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → ∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1
  obtain ⟨y, hy, hi⟩ := h1
  let a : ↥(Weil h) →* Module.End ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    { toFun := fun σ => urEnd P ρ (weilD Bw h P ρ σ) (weilD_mulD Bw h P ρ hj σ)
      map_one' := LinearMap.ext fun x => LinearMap.congr_fun (map_one (weilD Bw h P ρ)) ((toUr P ρ).symm x)
      map_mul' := fun σ τ => LinearMap.ext fun x =>
        LinearMap.congr_fun (map_mul (weilD Bw h P ρ) σ τ) ((toUr P ρ).symm x) }
  have := compactSpace_Ine (E := F) A
  have hle : (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker ≤ (a.comp (ineIncl h)).ker := fun s hs =>
    LinearMap.ext fun x => LinearMap.congr_fun (MonoidHom.mem_ker.mp hs) ((toUr P ρ).symm x)
  have : Finite (Ine (F := F) A ⧸ (a.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle (isSmooth_weilD Bw h P ρ hj))
  have hn : ∀ s, ∃ t, ineIncl h s * frob h = frob h * ineIncl h t := fun s => by
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (ineIncl h s * frob h)
    refine ⟨t, ?_⟩
    rw [deg_mul, deg_ineIncl, deg_frob, zero_add, zpow_one] at ht
    exact ht
  obtain ⟨x, hx, hf⟩ := UpperTheory.fixed_vector_descends_weil_group (ineIncl h) (frob h) hn
    (fun σ => ⟨deg σ, exists_eq_zpow_mul (deg_frob (h := h)) σ⟩) a (wdRho P ι Bw h hj ρ)
    ((AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)).comp (toUr P ρ).symm.toAddMonoidHom) (span_wdMk P ι ρ)
    (fun g x => wdRho_mk P ι Bw h hj ρ g ((toUr P ρ).symm x)) y hy hi
  exact ⟨(toUr P ρ).symm x, hx, hf⟩
