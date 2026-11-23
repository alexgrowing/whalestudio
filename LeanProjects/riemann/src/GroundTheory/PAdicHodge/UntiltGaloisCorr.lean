import Mathlib
import GroundTheory.PAdicHodge.UntiltGalois
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem ringHom_frobeniusEquiv_symm {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply (frobeniusEquiv S p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]

theorem ringHom_iterate_frobeniusEquiv_symm {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) (n : ℕ) :
    f ((frobeniusEquiv R p).symm^[n] x) = (frobeniusEquiv S p).symm^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ringHom_frobeniusEquiv_symm, ih]

section Injective

theorem untiltPreTiltAut_eq_id (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (h : untiltAut N σ = 1)
    (b : PreTilt (normInteger (untiltField K C p N)) p) : untiltPreTiltAut N σ b = b := by
  have hu : ∀ b : PreTilt (normInteger (untiltField K C p N)) p,
      PreTilt.untilt (untiltPreTiltAut N σ b) = PreTilt.untilt b := by
    intro b
    have := untiltAut_untilt N σ b
    rw [h, AlgEquiv.one_apply] at this
    exact Subtype.ext this.symm
  refine IsPerfectoidField.preTilt_ext p fun n => ?_
  rw [← IsPerfectoidField.mk_untilt_iterate, ← IsPerfectoidField.mk_untilt_iterate,
    ← ringHom_iterate_frobeniusEquiv_symm, hu]

theorem untiltAutHom_injective (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    Function.Injective (untiltAutHom (K := K) (C := C) (p := p) N) := by
  refine (injective_iff_map_eq_one _).2 fun σ h => ?_
  have h' : untiltAut N σ = 1 := h

  have hint : ∀ a : integerTilt K C p N,
      integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) a = a := by
    intro a
    obtain ⟨b, rfl⟩ := (preTiltUntiltEquiv N).surjective a
    rw [← preTiltUntiltEquiv_untiltPreTiltAut, untiltPreTiltAut_eq_id N σ h' b]
  have key : ∀ x : N, ‖(x : C♭)‖ ≤ 1 → σ x = x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := exists_algebraMap_eq_of_mem (p := p) x.2 hx
    apply Subtype.ext
    have := algebraMap_integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) ⟨a, ha⟩
    rw [hint] at this
    have hx' : (⟨algebraMap 𝒪C♭ C♭ a, ha⟩ : N) = x := Subtype.ext hax
    rw [hx'] at this
    exact this.symm.trans hax
  ext x
  rcases le_or_gt ‖(x : C♭)‖ 1 with hx | hx
  · exact congrArg Subtype.val (key x hx)
  · have hx0 : x ≠ 0 := by
      rintro rfl; norm_num at hx
    have := key x⁻¹ (by
      rw [IntermediateField.coe_inv, norm_inv]; exact inv_le_one_of_one_le₀ hx.le)
    rw [map_inv₀] at this
    exact congrArg Subtype.val (inv_injective this)

end Injective

section Galois

theorem untiltAutHom_bijective (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] :
    Function.Bijective (untiltAutHom (K := K) (C := C) (p := p) N) ∧
      IsGalois K (untiltField K C p N) := by
  have hinj := untiltAutHom_injective (K := K) (C := C) (p := p) N
  have h1 : Nat.card (N ≃ₐ[K♭] N) = Module.finrank K (untiltField K C p N) := by
    rw [IsGalois.card_aut_eq_finrank, finrank_untiltField]
  have h2 : Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) ≤
      Module.finrank K (untiltField K C p N) := by
    refine le_trans ?_ (card_algHom_le_finrank K (untiltField K C p N) (untiltField K C p N))
    exact Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective
  have h3 : Nat.card (N ≃ₐ[K♭] N) ≤
      Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) :=
    Nat.card_le_card_of_injective _ hinj
  have heq : Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) =
      Module.finrank K (untiltField K C p N) := le_antisymm h2 (h1 ▸ h3)
  exact ⟨hinj.bijective_of_nat_card_le (by rw [heq, h1]), IsGalois.of_card_aut_eq_finrank _ _ heq⟩

theorem isGalois_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] : IsGalois K (untiltField K C p N) :=
  (untiltAutHom_bijective N).2

end Galois

section Theta

theorem untiltPreTiltMap_symm (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (a : integerTilt K C p N) :
    untiltPreTiltMap N ((preTiltUntiltEquiv N).symm a) = a := by
  rw [← coe_preTiltUntiltEquiv, RingEquiv.apply_symm_apply]

theorem fontaineTheta_map_subtype (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (u : WittVector p (integerTilt K C p N)) :
    ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) := by
  have hu : WittVector.map (integerTilt K C p N).subtype u =
      WittVector.map (untiltPreTiltMap N) (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) := by
    rw [← wittVector_map_comp]
    exact WittVector.ext fun n => (untiltPreTiltMap_symm N (u.coeff n)).symm
  rw [hu, untiltPreTiltMap, fontaineTheta_map_preTiltMap, coe_integerMap]
  rfl

theorem coe_untiltAut_fontaineTheta (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (u : WittVector p (integerTilt K C p N))
    (hu : ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) ∈ untiltField K C p N) :
    ((untiltAut N σ ⟨_, hu⟩ : untiltField K C p N) : C) =
      ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype
        (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u)) :
        normInteger C) : C) := by
  have he : (⟨_, hu⟩ : untiltField K C p N) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) :=
    Subtype.ext (fontaineTheta_map_subtype N u)
  rw [he, untiltAut_coe, untiltIntegerHom_fontaineTheta, fontaineTheta_map_subtype,
    ← wittVector_map_comp, ← wittVector_map_comp]
  congr 3
  ext a
  simp [untiltPreTiltAut]

end Theta

section Correspondence

theorem exists_untiltField_eq_of_le (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] (L : IntermediateField K C) (hL : L ≤ untiltField K C p N) :
    ∃ M : IntermediateField K♭ C♭, M ≤ N ∧ FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  classical
  obtain ⟨hbij, hgal⟩ := untiltAutHom_bijective (K := K) (C := C) (p := p) N
  set F := untiltField K C p N
  set Φ := untiltAutHom (K := K) (C := C) (p := p) N
  set L' : IntermediateField K F := IntermediateField.restrict hL
  set H := L'.fixingSubgroup
  set J := H.comap Φ
  set M0 : IntermediateField K♭ N := IntermediateField.fixedField J
  set M : IntermediateField K♭ C♭ := M0.map N.val
  have hMN : M ≤ N := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hMfin : FiniteDimensional K♭ M :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap M0 N.val).toLinearEquiv
  refine ⟨M, hMN, hMfin, ?_⟩

  have hle : untiltField K C p M ≤ L := by
    rw [untiltField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, ⟨u, rfl⟩, rfl⟩
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono hMN)) u
    have hz : ((RingHom.comp (WittVector.fontaineTheta (normInteger C) p)
        (WittVector.map (integerTilt K C p M).subtype)) u : normInteger C) =
        WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u') := by
      simp only [RingHom.comp_apply, u']
      congr 1
    have hzF : ((WittVector.fontaineTheta (normInteger C) p
        (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) ∈ F :=
      coe_mem_untiltField ⟨u', rfl⟩
    change ((RingHom.comp (WittVector.fontaineTheta (normInteger C) p)
        (WittVector.map (integerTilt K C p M).subtype)) u : C) ∈ L
    rw [hz]
    have hfix : (⟨_, hzF⟩ : F) ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ hτ
      obtain ⟨σ, rfl⟩ := hbij.2 τ
      have hσ : σ ∈ J := hτ
      apply Subtype.ext

      have hcoeff : ∀ n, integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)
          (u'.coeff n) = u'.coeff n := by
        intro n
        set c := u'.coeff n
        have hcM : algebraMap 𝒪C♭ C♭ (c : 𝒪C♭) ∈ M := (u.coeff n).2
        obtain ⟨y, hy, hyc⟩ := hcM
        have hyfix : σ y = y := (IntermediateField.mem_fixedField_iff J y).1 hy σ hσ
        apply Subtype.ext
        apply IsFractionRing.injective 𝒪C♭ C♭
        rw [algebraMap_integerTiltHom]
        have : (⟨algebraMap 𝒪C♭ C♭ (c : 𝒪C♭), c.2⟩ : N) = y := Subtype.ext hyc.symm
        rw [this]
        change ((σ y : N) : C♭) = _
        rw [hyfix]
        exact hyc
      have hmap : WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ))
          u' = u' := WittVector.ext fun n => by rw [WittVector.map_coeff, hcoeff n]
      change ((untiltAut N σ ⟨_, hzF⟩ : F) : C) = _
      rw [coe_untiltAut_fontaineTheta, hmap]
    rw [IsGalois.fixedField_fixingSubgroup] at hfix
    exact (IntermediateField.mem_restrict hL _).1 hfix

  have hL'fin : FiniteDimensional K L' := inferInstance
  have hcard : Nat.card J = Nat.card H := by
    refine Nat.card_congr (Equiv.ofBijective (fun σ : J => (⟨Φ σ, σ.2⟩ : H)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (hbij.1 (congrArg Subtype.val hab))
    · rintro ⟨τ, hτ⟩
      obtain ⟨σ, rfl⟩ := hbij.2 τ
      exact ⟨⟨σ, hτ⟩, rfl⟩
  have hN : Module.finrank K♭ M0 * Nat.card J = Module.finrank K♭ N := by
    rw [← IntermediateField.finrank_fixedField_eq_card, Module.finrank_mul_finrank]
  have hF : Module.finrank K L' * Nat.card H = Module.finrank K F := by
    have h := IntermediateField.finrank_fixedField_eq_card H
    rw [IsGalois.fixedField_fixingSubgroup] at h
    rw [← h, Module.finrank_mul_finrank]
  have hFN : Module.finrank K F = Module.finrank K♭ N := finrank_untiltField N
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hL'M0 : Module.finrank K L' = Module.finrank K♭ M0 := by
    have := hF.trans (hFN.trans hN.symm)
    rw [hcard] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hLL' : Module.finrank K L = Module.finrank K L' :=
    (AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL)).toLinearEquiv.finrank_eq
  have hMM0 : Module.finrank K♭ M = Module.finrank K♭ M0 :=
    (IntermediateField.equivMap M0 N.val).toLinearEquiv.finrank_eq.symm
  have : FiniteDimensional K L :=
    LinearEquiv.finiteDimensional
      (AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL)).toLinearEquiv.symm
  exact IntermediateField.eq_of_le_of_finrank_le hle
    (by rw [finrank_untiltField, hMM0, ← hL'M0, hLL'])

end Correspondence

end GroundTheory.PAdicHodge
