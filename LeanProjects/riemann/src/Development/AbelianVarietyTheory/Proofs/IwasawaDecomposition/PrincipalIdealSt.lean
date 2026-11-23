import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulEqZeroOfCrossed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsModulusTopOfIsTotallyComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdealMapEqTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGaloisOfIsRayFieldTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInTrans

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

theorem GlobalTheory.Published.GlobalArtinReciprocity.principalIdealSt (H : GlobalArtinReciprocity) : PrincipalIdealSt := by
  intro K L _ _ _ _ _ _ h 𝔞
  have hKL := h.1
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  obtain ⟨N, _, _, _, hN⟩ := rayField_iff.1 H.rayClassFieldSt L ⊤ top_ne_bot
  let : Algebra K N := ((algebraMap L N).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := GlobalTheory.RayTopGalois.isGalois_of_isRayField_top K L N hN
  have := hN.1
  have h' := (GlobalTheory.HilbertClass.isRayField_top_iff L).1 h
  have hN' := (GlobalTheory.HilbertClass.isRayField_top_iff N).1 hN
  have hun := GlobalTheory.Mem.UnramTower.unramIn_trans K L N h'.2.1 hN'.2.1
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker = commutator (N ≃ₐ[K] N) := by
    refine le_antisymm ?_ ?_
    · let M := IntermediateField.fixedField (commutator (N ≃ₐ[K] N))
      have : IsAbelianGalois K M := by
        have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun a b => by
          obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) N a
          obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) N b
          rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
            IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩⟩
        exact {}
      obtain ⟨f⟩ := rayClassFieldMaximalSt_holds K L M ⊤ top_ne_bot h.2
        (GlobalTheory.UnramModulus.isModulus_top_of_isTotallyComplex H K M fun 𝔭 => GlobalTheory.RayMaximal.unramIn_of_tower (hun 𝔭))
      intro σ hσ
      rw [← IntermediateField.fixingSubgroup_fixedField (commutator (N ≃ₐ[K] N)), IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      let g : M →ₐ[K] N := (IsScalarTower.toAlgHom K L N).comp f
      have hr : g.fieldRange = M := by
        rw [AlgHom.fieldRange_of_normal]
      obtain ⟨y, rfl⟩ : x ∈ g.fieldRange := hr.symm ▸ hx
      have := σ.restrictNormal_commutes L (f y)
      rw [show σ.restrictNormal L = 1 from hσ] at this
      exact this.symm
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm' _ _
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => rw [Ideal.zero_eq_bot, Ideal.map_bot]; infer_instance
  | h₂ I hI => rw [Ideal.isUnit_iff.1 hI, Ideal.map_top]; infer_instance
  | h₃ I p _ hp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hP : (p.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
      refine (hN'.2.2.2 _ (Ideal.map_ne_bot_of_ne_bot hp.ne_zero)).1 fun χ => ?_
      obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob N 𝔭
      let r : (N ≃ₐ[L] N) →* (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker :=
        { toFun := fun τ => ⟨τ.restrictScalars K, AlgEquiv.ext fun x => (algebraMap L N).injective
            (((τ.restrictScalars K).restrictNormal_commutes L x).trans (τ.commutes x))⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hr : Function.Bijective r := ⟨fun a b e => AlgEquiv.ext fun x => congrArg (fun t => t.1 x) e, fun t =>
        ⟨AlgEquiv.ofRingEquiv (f := t.1.toRingEquiv) fun x => by
          have := t.1.restrictNormal_commutes L x
          rw [show t.1.restrictNormal L = 1 from t.2] at this
          exact this.symm, rfl⟩⟩
      let φ := χ.comp (MulEquiv.ofBijective r hr).symm.toMonoidHom
      have hv := GlobalTheory.FrobTransfer.heckeIdeal_map_eq_transfer K L N 𝔭 (hun 𝔭) σ hσ χ φ fun τ _ => congrArg χ ((MulEquiv.ofBijective r hr).symm_apply_apply τ)
      have key : ∀ (A : Subgroup (N ≃ₐ[K] N)) (_ : A = commutator _) (ψ : A →* ℂˣ), MonoidHom.transfer ψ = 1 := by
        rintro _ rfl ψ
        exact GlobalTheory.TransferCommutator.transfer_eq_one _ _ ψ
      rw [key _ hker φ] at hv
      exact hv
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := ih
    rw [Ideal.map_mul, ha, hb]
    exact ⟨a * b, Ideal.span_singleton_mul_span_singleton a b⟩
