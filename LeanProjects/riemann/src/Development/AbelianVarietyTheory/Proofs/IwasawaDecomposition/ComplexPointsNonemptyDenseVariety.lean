import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct Topology GlobalTheory.AffinePoints

namespace GlobalTheory.CxPtsDense

open GlobalTheory.CxPts

variable {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) (σ : F →+* ℂ)

theorem exists_param [GeometricallyIntegral p] [LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U)
    {f : Γ(X, U)} (hf : f ≠ 0) :
    ∃ (B : Type) (_ : TopologicalSpace B) (s : B → CxPts p σ), Nonempty B ∧ Continuous s ∧
      ptsIn p σ U ⊆ Set.range s ∧ Dense (s ⁻¹' ptsIn p σ (X.basicOpen f)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F ℂ := σ.toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have : Nontrivial Γ(X, U) := nontrivial_of_ne _ _ hf
  have : NoZeroDivisors (ℂ ⊗[F] Γ(X, U)) :=
    @UnitRigidity.noZeroDivisors_tensor F Γ(X, U) _ _ _ (algX p U).toAlgebra X p _
      hU.fromSpec (inferInstanceAs (IsOpenImmersion hU.fromSpec)) hg ℂ _ _
  have hinj := Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := Γ(X, U))
      (algebraMap F ℂ).injective
  have : Nontrivial (ℂ ⊗[F] Γ(X, U)) := hinj.nontrivial
  have : IsDomain (ℂ ⊗[F] Γ(X, U)) := NoZeroDivisors.to_isDomain _
  let φ (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : Γ(X, U) →+* ℂ :=
    q.toRingHom.comp (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom
  have hφa (q) (a) : φ q a = q (1 ⊗ₜ a) := rfl
  have hφ (q) (a : F) : φ q (algX p U a) = σ a := by
    have : ((1 : ℂ) ⊗ₜ[F] algX p U a) = algebraMap ℂ (ℂ ⊗[F] Γ(X, U)) (σ a) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := F) (A := ℂ) (B := Γ(X, U)) a).symm
    rw [hφa, this, AlgHom.commutes]
    rfl
  let s (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : CxPts p σ := ofHom hU (φ q) (hφ q)
  have hsU (q) : s q ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hsv (q) (a) : ev p σ U a (s q) = q (1 ⊗ₜ a) := ev_ofHom _ _ _ a
  refine ⟨_, inferInstance, s, ?_, ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℂ ⊗[F] Γ(X, U))
    let := Ideal.Quotient.field m
    have : Module.Finite ℂ ((ℂ ⊗[F] Γ(X, U)) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
    exact ⟨(IsAlgClosed.lift (R := ℂ) (S := (ℂ ⊗[F] Γ(X, U)) ⧸ m) (M := ℂ)).comp (Ideal.Quotient.mkₐ ℂ m)⟩
  · refine continuous_iff_continuousAt.2 fun q => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hsU q) (Filter.Eventually.of_forall hsU) fun a => ?_)
    have h : Continuous (ev p σ U a ∘ s) := by
      have : ev p σ U a ∘ s = fun q => q (1 ⊗ₜ a) := funext fun q => hsv q a
      rw [this]
      exact GlobalTheory.AffinePoints.continuous_eval _
    exact h.continuousAt
  · let ψ : Γ(X, U) →ₐ[F] ℂ :=
      { evHom hy with commutes' := fun a => (ev_eq hy _).symm.trans (ev_algX hy a) }
    let q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ :=
      Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) ψ fun _ _ => Commute.all _ _
    refine ⟨q, Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hsU q) hy fun a => ?_)⟩
    refine (hsv q a).trans ?_
    simp only [q, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (ev_eq hy a).symm
  · have hf' : ((1 : ℂ) ⊗ₜ[F] f) ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
    refine (GlobalTheory.AffinePoints.dense_nonvanishing hf').mono fun q hq => ?_
    refine (mem_ptsIn_basicOpen (hsU q) f).2 ?_
    rw [hsv]
    exact hq

theorem exists_ne_zero_basicOpen_le [IsIntegral X] {U W : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) (hW : (W : Set X).Nonempty) :
    ∃ f : Γ(X, U), f ≠ 0 ∧ X.basicOpen f ≤ W := by
  obtain ⟨x, hxU, hxW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen hne hW
  obtain ⟨f, hfW, hf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
  refine ⟨f, ?_, hfW⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hf
  exact hf

theorem nonempty_and_dense_of_geometricallyIntegral [GeometricallyIntegral p] [LocallyOfFiniteType p] :
    Nonempty (CxPts p σ) ∧ ∀ W : X.Opens, (W : Set X).Nonempty → Dense (ptsIn p σ W) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton p
  refine ⟨?_, fun W hW y => ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    obtain ⟨f, hf, -⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ ⟨_, hx⟩
    obtain ⟨B, _, s, ⟨b⟩, -⟩ := exists_param p σ hU hf
    exact ⟨s b⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ)))
    obtain ⟨f, hf, hfW⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ hW
    obtain ⟨B, _, s, -, hs, hr, hd⟩ := exists_param p σ hU hf
    obtain ⟨b, rfl⟩ := hr (mem_ptsIn.2 hx)
    exact closure_mono (ptsIn_mono hfW) (hs.closure_preimage_subset _ (hd b))

theorem nonempty_and_dense : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ),
    Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) :=
  fun _ _ Y σ => nonempty_and_dense_of_geometricallyIntegral Y.str σ

end GlobalTheory.CxPtsDense
