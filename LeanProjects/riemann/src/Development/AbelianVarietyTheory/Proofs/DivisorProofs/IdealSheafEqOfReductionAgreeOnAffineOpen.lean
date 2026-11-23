import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapMulIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatCompleteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdealsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInductionStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg

theorem affineFromSpec_comp_eq_specMap_cst {R : Type} [CommRing R] {W : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    V.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (cst f V.1)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) V.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem comap_idealSheaf_pow_eq {X Y : Scheme.{0}} (g : Y ⟶ X) (K : X.IdealSheafData) (k : ℕ) :
    (K ^ k).comap g = (K.comap g) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Scheme.IdealSheafData.comap_top g
  | succ n ih =>
    rw [pow_succ, pow_succ, GlobalTheory.Principalise.comap_mul_idealSheaf, ih]

theorem isIso_pullbackSnd_restrict_preimage {X Y S : Scheme.{0}} (π : X ⟶ S) (g : Y ⟶ S) (U : S.Opens)
    (h : IsIso (π ∣_ U)) : IsIso (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) := by
  have hEq : pullback.fst π g ⁻¹ᵁ π ⁻¹ᵁ U = pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U := by
    show (pullback.fst π g ≫ π) ⁻¹ᵁ U = (pullback.snd π g ≫ g) ⁻¹ᵁ U
    rw [pullback.condition]
  have L : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U).ι (π ⁻¹ᵁ U).ι (pullback.fst π g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hEq)
  have s := L.paste_vert (IsPullback.of_hasPullback π g)
  have key : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) (π ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict g U)
    · rw [morphismRestrict_ι, morphismRestrict_ι]
      exact s
    · rw [← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        Scheme.Hom.resLE_comp_ι_assoc, pullback.condition]
  exact key.isIso_snd_of_isIso h

theorem ideal_eq_of_reduces_affine : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t →
    ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) →
    ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  intro R _ I W W' _ f π U hπ hU K hK t ht V
  obtain ⟨hbc, hbs, -⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support
  obtain ⟨hbC, hloc⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus
  haveI : IsNoetherianRing Γ(W, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨C, _, φ, hCn, hφ, hC, hfaith⟩ := GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete Γ(W, V.1) (I.map (cst f V.1))
  haveI := hCn
  haveI := hπ
  have hJjac : (I.map (cst f V.1)).map φ ≤ Ideal.jacobson ⊥ := by
    haveI := hC
    exact IsAdicComplete.le_jacobson_bot _
  haveI hφF : Flat (Spec.map (CommRingCat.ofHom φ)) := AlgebraicGeometry.Flat.SpecMap_iff.mpr hφ
  have hOF : Flat V.2.fromSpec :=
    @HasRingHomProperty.of_isOpenImmersion @Flat RingHom.Flat _ _ _ _ RingHom.Flat.containsIdentities
      V.2.isOpenImmersion_fromSpec
  have hgF : Flat (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) :=
    MorphismProperty.comp_mem @Flat _ _ hφF hOF
  have F1 : ∀ X : W.IdealSheafData, X.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((X.ideal V).map φ) := fun X => hloc W V C φ X
  have F2 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).ideal V = (I.map (cst f V.1)) ^ (e + 1) := by
    intro e
    rw [baseIdeal_ideal, Ideal.map_pow]
  have F4 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, F2, Ideal.map_pow]
  have F5 : ∀ e : ℕ, ((t e).ideal V).map φ = ((t (e + 1)).ideal V).map φ ⊔ ((I.map (cst f V.1)).map φ) ^ (e + 1) := by
    intro e
    conv_lhs => rw [ht e]
    rw [← Ideal.map_pow, ← F2 e, ← Ideal.map_sup]
    rfl
  have F6 := GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals C ((I.map (cst f V.1)).map φ) hC (fun e => ((t e).ideal V).map φ) F5
  have F7 : ∀ e : ℕ, (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, ← (hbC C).2, F6 e]
  have F8 : ∀ e : ℕ, (baseIdeal (π ≫ f) (I ^ (e + 1))).comap
      (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) =
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    have hgf : (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom (φ.comp (cst f V.1))) := by
      rw [Category.assoc, affineFromSpec_comp_eq_specMap_cst, ← Spec.map_comp]
      rfl
    rw [hbc, ← Category.assoc, pullback.condition, Category.assoc, hgf, hbs, ← Ideal.map_map,
      Ideal.map_pow, Ideal.map_pow]
  have hKC : ∀ x, x ∉ (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)).support →
      x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U := by
    intro x hx
    refine hK _ (fun h => hx ?_)
    rw [Scheme.IdealSheafData.support_comap]
    exact h
  have hπC : IsProper (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := inferInstance
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction C ((I.map (cst f V.1)).map φ) hJjac _
    (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) _ hπC
    (isIso_pullbackSnd_restrict_preimage π _ U hU) _
    (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ)) hKC
  refine ⟨k₀, fun k hk T' T'' hT' hT'' e => ?_⟩
  have h1 : ∀ e : ℕ, T'.comap (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ⊔
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1))).comap
        (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := by
    intro e
    have hT'e : T' ⊔ baseIdeal (π ≫ f) (I ^ (e + 1)) = (t e).comap π := hT' e
    rw [← F8 e, ← Scheme.IdealSheafData.comap_sup, hT'e, ← F7 e,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  have h2 : ∀ e : ℕ, T''.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⊔
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) ⊔
        (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ^ k := by
    intro e
    have hT''e : T'' ⊔ baseIdeal f (I ^ (e + 1)) = t e ⊔ K ^ k := hT'' e
    rw [← F4 e, ← Scheme.IdealSheafData.comap_sup, hT''e, Scheme.IdealSheafData.comap_sup, F7 e,
      comap_idealSheaf_pow_eq, F4 e]
  have hmain := hk₀ k hk _ _ h1 h2
  have hX : ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).comap
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) := by
    rw [Scheme.IdealSheafData.comap_sup, GlobalTheory.T.idealSheafData_comap_inf_of_flat _ _ _ hgF,
      GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' _ _ π _ (pullback.fst π _) (pullback.snd π _) (IsPullback.of_hasPullback π _) hgF
        inferInstance, hmain, F4 e, F7 e]
  rw [F1, F1] at hX
  have hX' := (hbC C).1.1 hX
  have hle1 : (I.map (cst f V.1)) ^ (e + 1) ≤ ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp le_sup_right V
  have hle2 : (I.map (cst f V.1)) ^ (e + 1) ≤ (t e).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp (ht.baseIdeal_le e) V
  calc ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V
      = ((((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V).map φ).comap φ := (hfaith _ _ hle1).symm
    _ = ((((t e).ideal V)).map φ).comap φ := by rw [hX']
    _ = (t e).ideal V := hfaith _ _ hle2

end GlobalTheory.FormalAlg
