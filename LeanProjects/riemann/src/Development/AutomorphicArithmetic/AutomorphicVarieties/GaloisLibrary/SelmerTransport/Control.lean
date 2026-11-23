import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ControlGamma
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem control_lemma {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R Γ M) {C V U : Subgroup Γ} [C.Normal] [V.Normal] [U.Normal]
    (hCV : C ≤ V) (hVU : V ≤ U) (hCU : C ≤ U) {𝒟 : Set (Subgroup Γ)} (h𝒟 : ConjStable 𝒟)
    (H1 : Function.Injective (selRes ρ hCV 𝒟) ∧
      LinearMap.range (selRes ρ hCV 𝒟) = selEig ρ C h𝒟 V 1)
    (H2 : Function.Injective (selRes ρ hVU 𝒟) ∧
      LinearMap.range (selRes ρ hVU 𝒟) = selEig ρ V h𝒟 U 1) :
    Function.Injective (selRes ρ hCU 𝒟) ∧
      LinearMap.range (selRes ρ hCU 𝒟) = selEig ρ C h𝒟 U 1 := by
  have hcomp : ∀ x, selRes ρ hCU 𝒟 x = selRes ρ hCV 𝒟 (selRes ρ hVU 𝒟 x) := by
    intro x
    apply Subtype.ext
    simp only [selRes, LinearMap.restrict_apply]
    exact (resU_resU ρ hCV hVU x.1).symm
  have memE : ∀ (W : Subgroup Γ) [W.Normal] (X : Subgroup Γ) (y : LocSel ρ W 𝒟),
      y ∈ selEig ρ W h𝒟 X 1 ↔ ∀ g : X, selRep ρ W h𝒟 g y = y := by
    intro W _ X y
    simp only [selEig, mem_eig, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MonoidHom.one_apply, Units.val_one, one_smul]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rw [hcomp, hcomp] at hxy
    exact H2.1 (H1.1 hxy)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [memE]
      intro g
      have hx : selRes ρ hVU 𝒟 x ∈ selEig ρ V h𝒟 U 1 := H2.2 ▸ ⟨x, rfl⟩
      rw [memE] at hx
      rw [hcomp, ← selRes_selRep, hx g]
    · intro hy
      rw [memE] at hy
      have hyV : y ∈ LinearMap.range (selRes ρ hCV 𝒟) := by
        rw [H1.2, memE]
        intro g
        exact hy ⟨g, hVU g.2⟩
      obtain ⟨z, rfl⟩ := hyV
      have hz : z ∈ LinearMap.range (selRes ρ hVU 𝒟) := by
        rw [H2.2, memE]
        intro g
        apply H1.1
        rw [selRes_selRep]
        exact hy g
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, hcomp x⟩

private theorem selRes_injective_range_eq_of_le {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R Γ M) {C C' V : Subgroup Γ} [C.Normal] [C'.Normal] [V.Normal]
    (e : C' = C) (h : C ≤ V) (h' : C' ≤ V) {𝒟 : Set (Subgroup Γ)} (h𝒟 : ConjStable 𝒟)
    (H : Function.Injective (selRes ρ h' 𝒟) ∧
      LinearMap.range (selRes ρ h' 𝒟) = selEig ρ C' h𝒟 V 1) :
    Function.Injective (selRes ρ h 𝒟) ∧
      LinearMap.range (selRes ρ h 𝒟) = selEig ρ C h𝒟 V 1 := by
  subst e
  exact H

private theorem zmod_eq_intCast_of_primitiveRoot_pow_eq_selmer {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) (k : ℤ) (h : ζ ^ a.val = ζ ^ k) :
    a = (k : ZMod N) := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ ((a.val : ℤ) - k) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, h, div_self (zpow_ne_zero _ h0)]
  have h2 := (hζ.zpow_eq_one_iff_dvd _).mp h1
  have h3 : (((a.val : ℤ) - k : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  push_cast at h3
  rw [ZMod.natCast_zmod_val] at h3
  exact sub_eq_zero.mp h3

theorem UpperTheory.V.Base.control :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal], IsOpen (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ), U ≤ ψ.ker → n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ U _ hU hl ψ n hψ hn
  by_cases hγ : U ≤ gamU l ⊤
  · exact controlGamma k Ω l O U hU hγ ψ n hψ hn
  have hl2 : l ≠ 2 := hl.resolve_right hγ
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hρ : ReciprocityTheory.Gal.ContAction (twist₂ l (ψ * chiO k Ω l O ^ n)) :=
    (contTw k Ω l).2.2 O ψ n (Subgroup.isOpen_mono hψ hU)
  have hq : qExp l = 1 := by simp [qExp, hl2]
  have hV : gamU l U = U ⊓ ((KStar.TotallyRealRoots.redPow l 1).comp (cycZ k Ω l)).ker := by
    show levU l U (qExp l) = _
    rw [hq]
    simp only [levU, KStar.TotallyRealRoots.princ, MonoidHom.comap_ker]
  have hVγ : gamU l U ≤ gamU l ⊤ := by
    show levU l U (qExp l) ≤ levU l ⊤ (qExp l)
    simp only [levU]
    exact inf_le_inf_right _ le_top
  have hVU : gamU l U ≤ U := levU_le l U (qExp l)
  haveI hVn : (gamU l U).Normal := by
    rw [hV]
    infer_instance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hVopen : IsOpen ((gamU l U : Subgroup (G k Ω)) : Set (G k Ω)) := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
    haveI : FiniteDimensional k (IntermediateField.adjoin k {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    refine Subgroup.isOpen_mono
      (H₁ := U ⊓ (IntermediateField.adjoin k {ζ}).fixingSubgroup) ?_ ?_
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      rw [hV, Subgroup.mem_inf, MonoidHom.mem_ker]
      refine ⟨hg.1, ?_⟩
      have hgz : g ζ = ζ := by
        have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg.2 ζ
          (IntermediateField.mem_adjoin_simple_self k ζ)
        simpa [AlgEquiv.smul_def] using this
      have hs := cyclotomicCharacter.spec l (n := 1)
        (MulSemiringAction.toRingAut (G k Ω) Ω g) ζ hζ.pow_eq_one
      simp only [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
        AlgEquiv.smul_def, hgz] at hs
      have key := zmod_eq_intCast_of_primitiveRoot_pow_eq_selmer hζ _ 1 (by rw [zpow_one]; exact hs.symm)
      apply Units.ext
      simpa [KStar.TotallyRealRoots.redPow, cycZ] using key
    · rw [Subgroup.coe_inf]
      exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hrel : IsOpen ((gamU l U).subgroupOf U : Set U) := by
    rw [Subgroup.coe_subgroupOf]
    exact hVopen.preimage continuous_subtype_val
  have hd : (gamU l U).relIndex U ∣ l - 1 := by
    rw [hV]
    unfold Subgroup.relIndex
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf, MonoidHom.comap_ker,
      Subgroup.index_ker]
    refine (Subgroup.card_subgroup_dvd_card _).trans ?_
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]
  have hunit : IsUnit (((gamU l U).relIndex U : ℕ) : O) := by
    have h2 := hp.two_le
    have hpos : 0 < (gamU l U).relIndex U := Nat.pos_of_dvd_of_pos hd (by omega)
    have hle : (gamU l U).relIndex U ≤ l - 1 := Nat.le_of_dvd (by omega) hd
    have hnd : ¬ l ∣ (gamU l U).relIndex U := fun h => by
      have := Nat.le_of_dvd hpos h
      omega
    have hc : l.Coprime ((gamU l U).relIndex U) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
    have hu : IsUnit (((gamU l U).relIndex U : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc)
    simpa using hu.map (algebraMap ℤ_[l] O)
  have H2 := selUnit O (G k Ω) (QO l O) (twist₂ l (ψ * chiO k Ω l O ^ n)) hρ (gamU l U) U hVU
    hrel hunit (shaFam k Ω l) (conjStable_shaFam k Ω l)
  have HV := controlGamma k Ω l O (gamU l U) hVopen hVγ ψ n (le_trans hVU hψ) hn
  have hCV : cycU l U ≤ gamU l U := by
    have := cycU_le l (gamU l U)
    rwa [show cycU l (gamU l U) = cycU l U from cycU_levU l U (qExp l)] at this
  have H1 := selRes_injective_range_eq_of_le (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_levU l U (qExp l)) hCV
    (cycU_le l (gamU l U)) (conjStable_shaFam k Ω l) HV
  exact control_lemma _ hCV hVU (cycU_le l U) (conjStable_shaFam k Ω l) H1 H2
