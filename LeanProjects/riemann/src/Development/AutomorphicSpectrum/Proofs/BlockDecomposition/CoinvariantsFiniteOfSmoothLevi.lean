import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import GroundTheory.AutomorphicForms.FiniteLengthLattice

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

theorem hasFiniteLength_coinv_of_ker {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ)
    (π : Representation ℂ G U) (Φ : V →ₗ[ℂ] U) (hint : ∀ g v, Φ (τ (1, g) v) = π g (Φ v))
    (hker : LinearMap.ker Φ = twRel (τ.comp (MonoidHom.inl Γ G)) ψ) (hπ : HasFiniteLength π) :
    HasFiniteLength (coinv τ ψ) := by
  have hle : twRel (τ.comp (MonoidHom.inl Γ G)) ψ ≤ LinearMap.ker Φ := hker.ge
  have hinj : Function.Injective ((twRel (τ.comp (MonoidHom.inl Γ G)) ψ).liftQ Φ hle) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rw [← hker]
    exact hx
  let Ψ : (coinv τ ψ).IntertwiningMap π :=
    { toLinearMap := (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).liftQ Φ hle
      isIntertwining' := fun g => LinearMap.ext fun x => by
        obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        exact hint g f }
  exact GroundTheory.Automorphic.hasFiniteLength_of_injective Ψ hinj hπ

theorem hasFiniteLength_coinv_indSnd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  intro k _ _ _ _ hI Γ W b c d _ _ _ _ _ _ _ _ _ e τ hτ ψ hfin
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ b _ (two e)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two c d)) W :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k c d).symm.toMonoidHom
  let R : Submodule ℂ W := twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ
  have hR : ∀ (m : Levi k (Two c d)) (v : W), v ∈ R → ρ m v ∈ R :=
    fun m v hv => twRel_stable τ ψ _ v hv
  let ρD : Representation ℂ (Levi k (Two c d)) (W ⧸ R) := Representation.quotient ρ R hR
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := R.mkQ, isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective R
  have hρ : IsSmooth ρ := isSmooth_comp hτ _
    ((continuous_apply false).prodMk (continuous_apply true))
  have hρD : IsSmooth ρD := (IsSubquotient.of_surjective q hq).isSmooth hρ
  haveI : FiniteDimensional ℂ (W ⧸ R) := hfin
  have hInd : HasFiniteLength (parInd (two e) ρD) :=
    hI Bool b (Two c d) (two e) (W ⧸ R) ρD hρD
      (FinitenessModel.hasFiniteLength_of_finiteDimensional ρD)
  let σ : Representation ℂ (parab k (two e)) W :=
    (twist ρ (deltaHalf k (Two c d))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : σ.IntertwiningMap ((twist ρD (deltaHalf k (Two c d))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → σ.IntertwiningMap σ := fun γ =>
    { toLinearMap := (ψ γ : ℂ)⁻¹ • τ (γ, 1)
      isIntertwining' := fun p => by
        have h := (compMap (twistMap (actFst τ γ) (deltaHalf k (Two c d))) (leviProj k (two e))).isIntertwining' p
        have h' : τ (γ, 1) ∘ₗ σ p = σ p ∘ₗ τ (γ, 1) := h
        rw [LinearMap.smul_comp, LinearMap.comp_smul, h'] }
  have hT : ∀ γ v, T γ v = (ψ γ : ℂ)⁻¹ • τ (γ, 1) v := fun _ _ => rfl
  have hψ : ∀ γ, (ψ γ : ℂ) ≠ 0 := fun γ => (ψ γ).ne_zero
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : W | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have hxR : x ∈ R := (Submodule.Quotient.mk_eq_zero R).1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y : W | ∃ γ z, y = T γ z - z})).2 ?_ hxR
    rintro _ ⟨γ, v, rfl⟩
    have h : (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) γ v - (ψ γ : ℂ) • v =
        (ψ γ : ℂ) • (T γ v - v) := by
      rw [hT, smul_sub, smul_smul, mul_inv_cancel₀ (hψ γ), one_smul]
      rfl
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL b k) (parab k (two e)) (KO k b) hP
    SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k b) W (W ⧸ R) σ _ hσ
    α Γ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  refine hasFiniteLength_coinv_of_ker (indSnd e τ) ψ (parInd (two e) ρD) Φ.toLinearMap
    (fun g f => ?_) (le_antisymm ?_ ?_) hInd
  · rw [indSnd_inr]
    exact Φ.isIntertwining _ _ g f
  · intro f hf
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl Γ (GL b k))) ψ)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    have h : smIndMap (T γ) z - z = (ψ γ : ℂ)⁻¹ • (indSnd e τ (γ, 1) z - (ψ γ : ℂ) • z) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (hψ γ), one_smul]
      congr 1
      refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      show (ψ γ : ℂ)⁻¹ • τ (γ, 1) (z.1.1 x) = (ψ γ : ℂ)⁻¹ • τ (γ, 1) (z.1.1 (x * 1))
      rw [mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, z, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, f, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have h : τ (γ, 1) (f.1.1 x) - (ψ γ : ℂ) • f.1.1 x ∈ R :=
      Submodule.subset_span ⟨γ, f.1.1 x, rfl⟩
    have h2 := (Submodule.Quotient.mk_eq_zero R).2 h
    show q (τ (γ, 1) (f.1.1 (x * 1)) - (ψ γ : ℂ) • f.1.1 x) = 0
    rw [mul_one]
    exact h2

end GlobalTheory.CompanionTheory.ThetaGLLen
