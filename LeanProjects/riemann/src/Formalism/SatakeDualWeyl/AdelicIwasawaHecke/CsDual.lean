import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section CsDual

theorem csDual_hform_add_left {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (u v y : n → A) : hform τ J (u + v) y = hform τ J u y + hform τ J v y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem csDual_hform_zero_left {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (y : n → A) : hform τ J 0 y = 0 := by
  simp [hform]

theorem csDual_hform_smul_left {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (u y : n → A) : hform τ J (a • u) y = τ a * hform τ J u y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csDual_sig_incl (σ : E →ₐ[F] E) (a : E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (ι a) = ι (σ a) := by
  simp [sigR, inclE]

theorem csDual_sig_C (σ : E →ₐ[F] E) (c : 𝓞 F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (levelafC E c) = levelafC E c := by
  simp [sigR, levelafC]

theorem csDual_sig_mem (σ : E →ₐ[F] E) {s : 𝒜} (hs : s ∈ 𝒮) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) s ∈ 𝒮 := by
  have key : ∀ s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F),
      s ∈ (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).comap
        (sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    intro s hs'
    refine (Subring.closure_le.2 ?_) hs'
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨a, ha⟩ := hx
      have hint : IsIntegral ℤ (σ x) := by
        rw [← ha]
        simpa using (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := ℤ) a)).map
          σ.toRingHom.toIntAlgHom
      have e1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (x ⊗ₜ[F] (1 : (FiniteAdeleRing (𝓞 F) F))) = (σ x) ⊗ₜ[F] (1 : (FiniteAdeleRing (𝓞 F) F)) := by
        simp [sigR]
      show sigR σ (FiniteAdeleRing (𝓞 F) F) (x ⊗ₜ[F] (1 : (FiniteAdeleRing (𝓞 F) F))) ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
      rw [e1]
      exact Subring.subset_closure (Or.inl ⟨⟨σ x, IsIntegralClosure.mk' (𝓞 E) _ hint,
        IsIntegralClosure.algebraMap_mk' _ _ _⟩, rfl⟩)
    · have e2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        simp [sigR]
      show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
      rw [e2]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key s hs

end CsDual

section CsDual2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csDual_hform_incl (σ : E →ₐ[F] E) (J : Matrix n n E) (y x : n → E) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) (fun i => ι (y i)) (fun i => ι (x i)) =
      ι (hform (σ : E →+* E) J y x) := by
  simp [hform, csDual_sig_incl, map_sum, map_mul]

theorem csDual_span (σ : E →ₐ[F] E) (J : Matrix n n E) (M : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : ∀ y ∈ M, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (u : n → 𝒜) (hu : u ∈ Submodule.span 𝒮 ((fun y : n → E => fun i => ι (y i)) '' (M : Set (n → E)))) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) u (fun i => ι (x i)) ∈ 𝒮 := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    rw [csDual_hform_incl]
    obtain ⟨w, hw⟩ := hx y hy
    rw [← hw]
    exact Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)
  | zero => rw [csDual_hform_zero_left]; exact zero_mem _
  | add u v _ _ hu hv => rw [csDual_hform_add_left]; exact add_mem hu hv
  | smul a u _ hu =>
    rw [Subring.smul_def, csDual_hform_smul_left]
    exact mul_mem (csDual_sig_mem σ a.2) hu

end CsDual2

section CsDual3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csDual_expand (M : Matrix n n E) (v : n → 𝒜) (a b : 𝒜) (k : n) :
    a * b * ((M.map ι) *ᵥ v) k = ∑ i, (b * ι (M k i)) * (a * v i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem csDual_int_coe (d : 𝓞 F) : IsIntegral ℤ (algebraMap (𝓞 F) E d) := by
  exact IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := ℤ) d)

end CsDual3

theorem dual_lattice_bound_holds (hSpanRecover : Formalism.UG.CS.SpanRecover) : Formalism.UG.CS.DualBound := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hdet hfin hspan
  obtain ⟨c, hc, hlow⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : n × n => (J⁻¹) p.1 p.2)
  have haint : IsIntegral ℤ (algebraMap (𝓞 F) E (c * c) * (m : E)) := by
    refine (csDual_int_coe (c * c)).mul ?_
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E m))
  have ha0 : algebraMap (𝓞 F) E (c * c) * (m : E) ≠ 0 :=
    mul_ne_zero (adelstab_algebraMap_ne_zero (F := F) (E := E) _ (mul_ne_zero hc hc))
      (Int.cast_ne_zero.2 hm0)
  refine ⟨⟨_, haint⟩, ?_, ?_⟩
  · intro h
    apply ha0
    exact congrArg (fun t : 𝓞 E => (t : E)) h
  intro g hg x hx
  have hU : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) *
      (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hg
  obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) :=
    ⟨_, rfl⟩
  have hxz : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) =
      (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z := by
    rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hw : ∀ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ,
      hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) w z ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro w hw
    have hu := (hSpanRecover F E n Λ hfin hspan g ((g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w)).2
      (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
    have := csDual_span σ J (Formalism.UG.CS.globLat g Λ) x hx _ hu
    rwa [hxz, hform_mulVec, hU] at this
  have hi : ∀ i, levelafC E c *
      ((J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ z) i ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro i
    have h1 := hw _ (hlow (Pi.single i (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (fun k => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _))
    have h2 : (fun k => levelafC E c * (Pi.single i (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) : n → _) k) =
        levelafC E c • (Pi.single i (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) : n → _) := by
      funext k; simp [Pi.smul_apply]
    rwa [h2, csDual_hform_smul_left, csDual_sig_C, sf_single] at h1
  have hinv : (J⁻¹).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz2 : (J⁻¹).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) *ᵥ
      ((J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ z) = z := by
    rw [mulVec_mulVec, hinv, one_mulVec]
  have hv : ∀ k, levelafC E c * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (m : E) * z k ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro k
    have := csDual_expand (F := F) (J⁻¹) ((J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ z)
      (levelafC E c) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (m : E)) k
    rw [hz2] at this
    rw [this]
    refine sum_mem fun i _ => mul_mem ?_ (hi i)
    rw [← map_mul]
    exact adelstabL_incl_int (F := F) _ (hm (k, i))
  have hlat := hlow _ hv
  show ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E ⟨_, haint⟩ • x) i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  convert hlat using 1
  have hsm : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
      ((algebraMap (𝓞 E) E ⟨_, haint⟩ • x) i)) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E (c * c) * (m : E)) •
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact map_mul _ _ _
  rw [hsm, mulVec_smul, ← hz]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, adelstab_incl_C]
  ring

end Formalism.UG.P
