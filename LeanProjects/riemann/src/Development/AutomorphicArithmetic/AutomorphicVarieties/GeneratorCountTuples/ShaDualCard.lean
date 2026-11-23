import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

private theorem mapH1_mem_sha {R G M M' I : Type} {Dd : I → Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [∀ i, Group (Dd i)] [∀ i, TopologicalSpace (Dd i)] (φ : ∀ i, Dd i →* G) (hφ : ∀ i, Continuous (φ i))
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (x : H1 ρ) (hx : x ∈ Sha1 ρ φ hφ) :
    mapH1 ρ ρ' u hu he x ∈ Sha1 ρ' φ hφ := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  have key : resH1 ρ' (φ i) (hφ i) (mapH1 ρ ρ' u hu he x) =
      mapH1 (ρ.comp (φ i)) (ρ'.comp (φ i)) u hu (fun g m => he _ m) (resH1 ρ (φ i) (hφ i) x) := by
    induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  rw [key, hx i, map_zero]

private theorem mapH1_comp {R G M M' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (w : M' →ₗ[R] M) (hw : Continuous w)
    (he' : ∀ g m, w (ρ' g m) = ρ g (w m)) (h : ∀ m, w (u m) = m) (x : H1 ρ) :
    mapH1 ρ' ρ w hw he' (mapH1 ρ ρ' u hu he x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => h _))

private theorem card_sha_congr {R G M M' I : Type} {Dd : I → Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [∀ i, Group (Dd i)] [∀ i, TopologicalSpace (Dd i)] (φ : ∀ i, Dd i →* G) (hφ : ∀ i, Continuous (φ i))
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M ≃ₗ[R] M') (hu : Continuous u)
    (hw : Continuous u.symm) (he : ∀ g m, u (ρ g m) = ρ' g (u m)) :
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha1 ρ' φ hφ) := by
  have he' : ∀ g m, u.symm (ρ' g m) = ρ g (u.symm m) := fun g m => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  exact Nat.card_congr
    { toFun := fun x => ⟨_, mapH1_mem_sha φ hφ ρ ρ' u.toLinearMap hu he x.1 x.2⟩
      invFun := fun x => ⟨_, mapH1_mem_sha φ hφ ρ' ρ u.symm.toLinearMap hw he' x.1 x.2⟩
      left_inv := fun x => Subtype.ext (mapH1_comp ρ ρ' u.toLinearMap hu he u.symm.toLinearMap hw he'
        u.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (mapH1_comp ρ' ρ u.symm.toLinearMap hw he' u.toLinearMap hu he
        u.apply_symm_apply x.1) }

theorem UpperTheory.V.K.shaDualCard :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l) (n : ℤ), (∀ g, redChar D.chi 1 g = 1) → Nat.card (Sha1 (zd D n 1) (locFam D.S D.A) (continuous_locFam D.S D.A)) = Nat.card (ShaZm D 1 0) := by
  intro l _ L Ω _ _ _ _ _ D n h
  let ev : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) :=
    { toFun := fun φ => φ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin : ∀ (φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) (m : ZMod (l ^ 1)), φ m = m * φ 1 :=
    fun φ m => by
      have := LinearMap.map_smul (show ZMod (l ^ 1) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) from φ) m 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at this
      exact this
  have hev : Function.Bijective ev := by
    refine ⟨fun φ ψ h => TDual.ext fun m => ?_, fun y => ⟨y • TDual.mk LinearMap.id, ?_⟩⟩
    · rw [hlin φ, hlin ψ]; exact congrArg _ h
    · exact mul_one y
  have hn : ∀ g, redChar (D.chi ^ n) 1 g = 1 := fun g => by
    have : redChar (D.chi ^ n) 1 g = redChar D.chi 1 g ^ n := by
      simp only [redChar, MonoidHom.comp_apply, MonoidHom.zpow_apply, map_zpow]
    rw [this, h, one_zpow]
  refine card_sha_congr _ _ _ (zmTw D 1 0) (LinearEquiv.ofBijective ev hev) continuous_of_discreteTopology
    continuous_of_discreteTopology fun g m => ?_
  have h0 : ∀ x, zmTw D 1 0 g x = x := fun x => by simp [zmTw]
  rw [h0]
  change ((redChar D.chi 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) *
    m (((redChar (D.chi ^ n) 1 g⁻¹ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) * 1) = m 1
  rw [h, hn, Units.val_one, one_mul, one_mul]
