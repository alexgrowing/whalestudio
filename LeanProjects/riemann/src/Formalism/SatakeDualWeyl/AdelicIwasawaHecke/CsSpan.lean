import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section CsSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csSpan_approx (hA : Formalism.UG.CS.IntAdApprox) (D : 𝓞 F) (hD : D ≠ 0) {s : 𝒜} (hs : s ∈ 𝒮) :
    ∃ x : E, IsIntegral ℤ x ∧ ∃ w ∈ 𝒮, s = ι x + levelafC E D * w := by
  refine Subring.closure_induction
    (p := fun s _ => ∃ x : E, IsIntegral ℤ x ∧ ∃ w ∈ 𝒮, s = ι x + levelafC E D * w)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · refine ⟨algebraMap (𝓞 E) E e', RingOfIntegers.isIntegral_coe e', 0, zero_mem _, ?_⟩
      simp [inclE]
    · obtain ⟨r, y', hy', hyr⟩ := hA F D hD y hy
      refine ⟨algebraMap (𝓞 F) E r, ?_, (1 : E) ⊗ₜ[F] y', ?_, ?_⟩
      · rw [IsScalarTower.algebraMap_apply (𝓞 F) F E]
        exact (RingOfIntegers.isIntegral_coe r).algebraMap
      · have := levelaf_tmul_mem (F := F) (E := E) 1 hy'
        rwa [map_one] at this
      · rw [adelstab_incl_C]
        simp only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [← TensorProduct.tmul_add, ← hyr]
  · exact ⟨0, isIntegral_zero, 0, zero_mem _, by simp⟩
  · exact ⟨1, isIntegral_one, 0, zero_mem _, by simp⟩
  · rintro a b _ _ ⟨x, hx, w, hw, rfl⟩ ⟨y, hy, w', hw', rfl⟩
    exact ⟨x + y, hx.add hy, w + w', add_mem hw hw', by rw [map_add]; ring⟩
  · rintro a _ ⟨x, hx, w, hw, rfl⟩
    exact ⟨-x, hx.neg, -w, neg_mem hw, by rw [map_neg]; ring⟩
  · rintro a b _ _ ⟨x, hx, w, hw, rfl⟩ ⟨y, hy, w', hw', rfl⟩
    refine ⟨x * y, hx.mul hy, w * ι y + ι x * w' + levelafC E D * w * w', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem hw (adelstabL_incl_int _ hy))
        (mul_mem (adelstabL_incl_int _ hx) hw')) (mul_mem (mul_mem (levelafC_mem D) hw) hw')
    · rw [map_mul]; ring

theorem csSpan_fwd (Λ : Submodule (𝓞 E) (n → E)) (g : GL n 𝒜) (u : n → 𝒜)
    (hu : u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E)))) :
    ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
  let Φ : (n → 𝒜) →ₗ[𝒮] (n → 𝒜) :=
    (Matrix.mulVecLin ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜)).restrictScalars 𝒮
  have hle : Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E))) ≤
      (latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ).comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  exact hle hu

theorem csSpan_back (hA : Formalism.UG.CS.IntAdApprox) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (g : GL n 𝒜) (u : n → 𝒜)
    (hu : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E))) := by
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  obtain ⟨d, hd, c, hc, hg, hg'⟩ := levelaf_exists_denom (F := F) (E := E) g
  have eg := adelstab_entries g d c hc hg
  have eg' := adelstab_entries (g⁻¹) d c hc hg'

  have hint : ∀ i, levelafC E (d * c₂) * u i ∈ 𝒮 := by
    intro i
    set w := ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u with hw
    have hu' : u = (g : Matrix n n 𝒜) *ᵥ w := by
      rw [hw, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [hu', mulVec, dotProduct, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    have : levelafC E (d * c₂) * ((g : Matrix n n 𝒜) i j * w j) =
        (levelafC E d * (g : Matrix n n 𝒜) i j) * (levelafC E c₂ * w j) := by
      rw [levelafC_mul]; ring
    rw [this]
    exact mul_mem (eg i j) (h₂ w hu j)

  have hM : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => levelafC E (c₁ * d) * v i) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
    intro v hv
    have : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => levelafC E (c₁ * d) * v i) =
        fun i => levelafC E c₁ *
          ∑ j, (levelafC E d * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j) * v j := by
      ext i
      rw [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [levelafC_mul]; ring
    rw [this]
    exact h₁ _ fun i => sum_mem fun j _ => mul_mem (eg' i j) (hv j)

  have hD : d * c₂ * (c₁ * d) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hd hc₂) (mul_ne_zero hc₁ hd)
  choose x' hx' w hw hxw using fun i => csSpan_approx hA _ hD (hint i)
  set α := algebraMap (𝓞 F) E (d * c₂) with hα
  have hα0 : α ≠ 0 := adelstab_algebraMap_ne_zero _ (mul_ne_zero hd hc₂)
  have hαu : IsUnit (ι α) := (IsUnit.mk0 α hα0).map ι
  set x : n → E := fun i => x' i / α with hxdef
  have hux : ∀ i, u i = ι (x i) + levelafC E (c₁ * d) * w i := by
    intro i
    apply hαu.mul_left_cancel
    rw [hα, adelstab_incl_C, mul_add, ← adelstab_incl_C, ← hα, ← map_mul, hxdef,
      mul_div_cancel₀ _ hα0, ← mul_assoc, hα, adelstab_incl_C, ← levelafC_mul, ← hxw i]
  have hxmem : x ∈ Formalism.UG.CS.globLat g Λ := by
    show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    have : (fun i => ι (x i)) = u - fun i => levelafC E (c₁ * d) * w i := by
      ext i; rw [Pi.sub_apply, hux i]; ring
    rw [this, mulVec_sub]
    exact sub_mem hu (hM w hw)
  set β := algebraMap (𝓞 F) E (c₁ * d) with hβ
  have hsk : ∀ k, (Pi.single k β : n → E) ∈ Formalism.UG.CS.globLat g Λ := by
    intro k
    show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι ((Pi.single k β : n → E) i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    have : (fun i => ι ((Pi.single k β : n → E) i)) =
        fun i => levelafC E (c₁ * d) * (Pi.single k (1 : 𝒜) : n → 𝒜) i := by
      ext i
      by_cases h : i = k
      · subst h; simp [hβ, adelstab_incl_C, levelafC_mul]
      · simp [h]
    rw [this]
    refine hM _ fun i => ?_
    by_cases h : i = k
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_apply, if_neg h]; exact zero_mem _
  have hdec : u = (fun i => ι (x i)) +
      ∑ k, (⟨w k, hw k⟩ : 𝒮) • (fun i => ι ((Pi.single k β : n → E) i)) := by
    ext i
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single i, hux i]
    · show _ = _ + (_ : 𝒮) • ι ((Pi.single i β : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, hβ, adelstab_incl_C, mul_comm]
    · intro k _ hki
      show (_ : 𝒮) • ι ((Pi.single k β : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [hdec]
  exact add_mem (Submodule.subset_span ⟨x, hxmem, rfl⟩)
    (sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsk k, rfl⟩))

end CsSpan

theorem span_recovery_of_integral_adelic_approx (hIntAdApprox : Formalism.UG.CS.IntAdApprox) : Formalism.UG.CS.SpanRecover := by
  intro F E _ _ _ _ _ n _ _ Λ hfin hspan g u
  exact ⟨csSpan_fwd Λ g u, csSpan_back hIntAdApprox Λ hfin hspan g u⟩

end Formalism.UG.P
