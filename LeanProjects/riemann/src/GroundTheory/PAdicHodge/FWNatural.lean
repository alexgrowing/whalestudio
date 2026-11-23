import Mathlib
import GroundTheory.PAdicHodge.TiltEquiv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p

theorem fontaineTheta_map_inclusion {N N' : IntermediateField K♭ C♭} (h : N ≤ N')
    (u : WittVector p (integerTilt K C p N)) :
    θ (WittVector.map (integerTilt K C p N').subtype
        (WittVector.map (Subring.inclusion (integerTilt_mono h)) u)) =
      θ (WittVector.map (integerTilt K C p N).subtype u) := by
  rw [← wittVector_map_comp]
  rfl

theorem coe_untiltAut_of_le {N N' : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    [FiniteDimensional K♭ N'] (h : N ≤ N') (σ : N ≃ₐ[K♭] N) (σ' : N' ≃ₐ[K♭] N')
    (hσ : ∀ y : N, ((σ' ⟨y, h y.2⟩ : N') : C♭) = ((σ y : N) : C♭)) (x : untiltField K C p N) :
    ((untiltAut N' σ' ⟨x, untiltField_mono h x.2⟩ : untiltField K C p N') : C) =
      ((untiltAut N σ x : untiltField K C p N) : C) := by
  set f : untiltField K C p N →ₐ[K] C := (untiltField K C p N').val.comp
    ((untiltAut N' σ').toAlgHom.comp (IntermediateField.inclusion (untiltField_mono h)))
  set g : untiltField K C p N →ₐ[K] C := (untiltField K C p N).val.comp (untiltAut N σ).toAlgHom
  have hfg : f = g := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    show ((untiltAut N' σ' (IntermediateField.inclusion (untiltField_mono h)
        ⟨y, IntermediateField.subset_adjoin _ _ hy⟩) : untiltField K C p N') : C) =
      ((untiltAut N σ ⟨y, IntermediateField.subset_adjoin _ _ hy⟩ : untiltField K C p N) : C)
    generalize IntermediateField.subset_adjoin K _ hy = hy0
    obtain ⟨z, ⟨u, rfl⟩, rfl⟩ := hy
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono h)) u
    have hz : ((RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype) u : normInteger C) : C) =
        ((θ (WittVector.map (integerTilt K C p N').subtype u') : normInteger C) : C) := by
      rw [fontaineTheta_map_inclusion h]; rfl
    have hcoeff : ∀ n, integerTiltHom N' σ'.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N' σ')
        (u'.coeff n) = Subring.inclusion (integerTilt_mono h)
          (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (u.coeff n)) := by
      intro n
      apply Subtype.ext
      apply IsFractionRing.injective 𝒪C♭ C♭
      rw [algebraMap_integerTiltHom]
      change _ = algebraMap 𝒪C♭ C♭ (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (u.coeff n) : 𝒪C♭)
      rw [algebraMap_integerTiltHom]
      exact hσ ⟨algebraMap 𝒪C♭ C♭ (u.coeff n : 𝒪C♭), (u.coeff n).2⟩
    have hmap : WittVector.map (integerTiltHom N' σ'.toAlgHom
        (norm_tiltAlgEquiv_toAlgHom_apply N' σ')) u' =
        WittVector.map (Subring.inclusion (integerTilt_mono h))
          (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u) :=
      WittVector.ext fun n => by
        simp only [WittVector.map_coeff]; exact hcoeff n
    have hmemN : ((θ (WittVector.map (integerTilt K C p N).subtype u) : normInteger C) : C) ∈
        untiltField K C p N := coe_mem_untiltField ⟨u, rfl⟩
    have hmemN' : ((θ (WittVector.map (integerTilt K C p N').subtype u') : normInteger C) : C) ∈
        untiltField K C p N' := coe_mem_untiltField ⟨u', rfl⟩
    have e1 : IntermediateField.inclusion (untiltField_mono h) ⟨_, hy0⟩ =
        (⟨_, hmemN'⟩ : untiltField K C p N') := Subtype.ext hz
    have e2 : (⟨_, hy0⟩ : untiltField K C p N) = ⟨_, hmemN⟩ := rfl
    rw [e1, e2, coe_untiltAut_fontaineTheta, coe_untiltAut_fontaineTheta, hmap,
      fontaineTheta_map_inclusion h]
  exact congrArg (fun φ : untiltField K C p N →ₐ[K] C => φ x) hfg

theorem untiltAut_apply_of_le {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] (h : M ≤ N)
    (σ : N ≃ₐ[K♭] N) (hσ : ∀ y : N, (y : C♭) ∈ M → σ y = y) (x : untiltField K C p M) :
    untiltAut N σ ⟨x, untiltField_mono h x.2⟩ = ⟨x, untiltField_mono h x.2⟩ := by
  set f : untiltField K C p M →ₐ[K] C := (untiltField K C p N).val.comp
    ((untiltAut N σ).toAlgHom.comp (IntermediateField.inclusion (untiltField_mono h)))
  set g : untiltField K C p M →ₐ[K] C := (untiltField K C p M).val
  have hfg : f = g := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    show ((untiltAut N σ (IntermediateField.inclusion (untiltField_mono h)
        ⟨y, IntermediateField.subset_adjoin _ _ hy⟩) : untiltField K C p N) : C) = y
    generalize IntermediateField.subset_adjoin K _ hy = hy0
    obtain ⟨z, ⟨u, rfl⟩, rfl⟩ := hy
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono h)) u
    have hz : ((RingHom.comp θ (WittVector.map (integerTilt K C p M).subtype) u : normInteger C) : C) =
        ((θ (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) := by
      rw [fontaineTheta_map_inclusion h]; rfl
    have hmemN' : ((θ (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) ∈
        untiltField K C p N := coe_mem_untiltField ⟨u', rfl⟩
    have hcoeff : ∀ n, integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)
        (u'.coeff n) = u'.coeff n := by
      intro n
      apply Subtype.ext
      apply IsFractionRing.injective 𝒪C♭ C♭
      rw [algebraMap_integerTiltHom]
      exact congrArg Subtype.val (hσ ⟨algebraMap 𝒪C♭ C♭ (u'.coeff n : 𝒪C♭), (u'.coeff n).2⟩
        (u.coeff n).2)
    have hmap : WittVector.map (integerTiltHom N σ.toAlgHom
        (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u' = u' :=
      WittVector.ext fun n => by rw [WittVector.map_coeff, hcoeff n]
    have e1 : IntermediateField.inclusion (untiltField_mono h) ⟨_, hy0⟩ =
        (⟨_, hmemN'⟩ : untiltField K C p N) := Subtype.ext hz
    rw [e1, coe_untiltAut_fontaineTheta, hmap]
    exact hz.symm
  exact Subtype.ext (congrArg (fun φ : untiltField K C p M →ₐ[K] C => φ x) hfg)

theorem finiteDimensional_of_le_tilt {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    (h : M ≤ N) : FiniteDimensional K♭ M :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem untiltAut_mem_fixingSubgroup_iff (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] {M : IntermediateField K♭ C♭} (h : M ≤ N) (σ : N ≃ₐ[K♭] N) :
    untiltAut N σ ∈ (IntermediateField.restrict (untiltField_mono (K := K) (p := p) h)).fixingSubgroup ↔
      σ ∈ (IntermediateField.restrict h).fixingSubgroup := by
  classical
  have hMfin : FiniteDimensional K♭ M := finiteDimensional_of_le_tilt h
  obtain ⟨hbij, hgal⟩ := untiltAutHom_bijective (K := K) (C := C) (p := p) N
  set M' := IntermediateField.restrict h
  set L' := IntermediateField.restrict (untiltField_mono (K := K) (p := p) h)
  have hJH : ∀ τ ∈ M'.fixingSubgroup, untiltAut N τ ∈ L'.fixingSubgroup := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
    intro x hx
    have hx' : (x : C) ∈ untiltField K C p M := (IntermediateField.mem_restrict _ x).1 hx
    exact untiltAut_apply_of_le h τ
      (fun y hy => hτ y ((IntermediateField.mem_restrict h y).2 hy)) ⟨x, hx'⟩
  refine ⟨fun hσ => ?_, hJH σ⟩

  have hM'fin : Module.finrank K♭ M' = Module.finrank K♭ M :=
    (IntermediateField.restrictAlgEquiv h).toLinearEquiv.finrank_eq.symm
  have hL'fin : Module.finrank K L' = Module.finrank K (untiltField K C p M) :=
    (IntermediateField.restrictAlgEquiv (untiltField_mono (K := K) (p := p) h)).toLinearEquiv.finrank_eq.symm
  have h1 : Module.finrank K♭ M' * Module.finrank M' N = Module.finrank K♭ N :=
    Module.finrank_mul_finrank K♭ M' N
  have h2 : Module.finrank K L' * Module.finrank L' (untiltField K C p N) =
      Module.finrank K (untiltField K C p N) :=
    Module.finrank_mul_finrank K L' (untiltField K C p N)
  rw [finrank_untiltField, hL'fin, finrank_untiltField, ← hM'fin, ← h1] at h2
  have hpos : 0 < Module.finrank K♭ M' := Module.finrank_pos
  have hdeg : Module.finrank L' (untiltField K C p N) = Module.finrank M' N :=
    Nat.eq_of_mul_eq_mul_left hpos h2
  have hcard : Nat.card L'.fixingSubgroup ≤ Nat.card M'.fixingSubgroup := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank, IsGalois.card_fixingSubgroup_eq_finrank, hdeg]
  set φ : M'.fixingSubgroup → L'.fixingSubgroup := fun τ => ⟨untiltAut N τ, hJH τ τ.2⟩
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (hbij.1 (congrArg Subtype.val hab :))
  obtain ⟨τ, hτ⟩ := (hφ.bijective_of_nat_card_le hcard).2 ⟨untiltAut N σ, hσ⟩
  have : (τ : N ≃ₐ[K♭] N) = σ := hbij.1 (congrArg Subtype.val hτ :)
  exact this ▸ τ.2

end GroundTheory.PAdicHodge
