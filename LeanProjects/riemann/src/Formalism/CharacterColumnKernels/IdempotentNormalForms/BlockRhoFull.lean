import Formalism.CharacterColumnKernels.StatementPsi
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKer
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm

open Finset Classical

noncomputable section

namespace Formalism.NG

theorem colPsiKer : StatColPsiKer := by
  intro O A T' G _ _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0
  ext φ
  simp only [LinearMap.mem_ker, kerY, Submodule.mem_iInf]
  constructor
  · intro h
    have hg : ∀ g, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0 := fun g => by
      have := congrArg (fun c : coZ1s (uRep O (M := M) r χ) => (c : G → M) g) h
      exact this
    have key : ∀ (x : A) (hx : x ∈ Submodule.span A (Set.range (ycoc r χ E))),
        φ (Submodule.Quotient.mk (((⟨x, hx⟩ : Ymod r χ E)),
          (0 : (l : ι) → A × (Fin (j l) → A) × A))) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact hg g
      | zero =>
        show φ (Submodule.Quotient.mk 0) = 0
        rw [Submodule.Quotient.mk_zero, map_zero]
      | add x z hx hz ihx ihz =>
        have e : (((⟨x + z, Submodule.add_mem _ hx hz⟩ : Ymod r χ E)),
            (0 : (l : ι) → A × (Fin (j l) → A) × A)) =
            (((⟨x, hx⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) +
            (((⟨z, hz⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) :=
          Prod.ext rfl (add_zero 0).symm
        rw [e, Submodule.Quotient.mk_add, map_add, ihx, ihz, add_zero]
      | smul a x hx ih =>
        have e : (((⟨a • x, Submodule.smul_mem _ a hx⟩ : Ymod r χ E)),
            (0 : (l : ι) → A × (Fin (j l) → A) × A)) =
            a • (((⟨x, hx⟩ : Ymod r χ E)), (0 : (l : ι) → A × (Fin (j l) → A) × A)) :=
          Prod.ext rfl (smul_zero a).symm
        rw [e, Submodule.Quotient.mk_smul, map_smul, ih, smul_zero]
    intro y
    exact key y.1 y.2
  · intro h
    apply Subtype.ext
    funext g
    exact h ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩

theorem cobColumn : StatCobColumn := by
  intro O A T' G _ _ _ _ _ M _ _ _ _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 s t hE hEE hEm hδ hτ
    φ v hv

  let Fl : Ymod r χ E →ₗ[A] M := φ.comp ((colRelJ r χ E e₁ δ D j Kc k0).mkQ.comp
    (LinearMap.inl A (Ymod r χ E) ((l : ι) → A × (Fin (j l) → A) × A)))
  let yg : G → Ymod r χ E := fun g => ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩
  have hF : ∀ g, Fl (yg g) = uElt r χ g • v - v := fun g => congrFun hv g
  have huv : ∀ g, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) * ((((χ g)⁻¹ : T'ˣ) : T') • r g) =
      t g • r g := by
    intro g
    rw [← Algebra.smul_def, smul_smul, mul_assoc, Units.mul_inv, mul_one]
  have hu' : ∀ g, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) * uElt r χ g = t g • r g :=
    fun g => huv g
  have hterm : ∀ g, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) * ycoc r χ E g =
      (t g • r g - algebraMap T' A (t g * ((χ g : T'ˣ) : T'))) * E := by
    intro g
    simp only [ycoc]
    rw [← mul_assoc, mul_sub, mul_one, huv g]
  obtain ⟨y₁, hy₁def⟩ : ∃ y : Ymod r χ E,
      y = ∑ g ∈ s, algebraMap T' A (t g * ((χ g : T'ˣ) : T')) • yg g := ⟨_, rfl⟩
  have hy₁ : ((y₁ : Ymod r χ E) : A) =
      (E - algebraMap T' A (∑ g ∈ s, t g * ((χ g : T'ˣ) : T'))) * E := by
    rw [hy₁def]
    simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, yg, Submodule.coe_mk]
    rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Finset.sum_mul, Finset.sum_sub_distrib, ← hE,
      ← map_sum]
  have hFy : Fl y₁ = -(δO • v) := by
    rw [hy₁def, map_sum]
    have hgen : ∀ g ∈ s, Fl (algebraMap T' A (t g * ((χ g : T'ˣ) : T')) • yg g) =
        (t g • r g) • v - (t g * ((χ g : T'ˣ) : T')) • v := by
      intro g _
      rw [map_smul, hF g, smul_sub, smul_smul, hu' g, algebraMap_smul]
    rw [Finset.sum_congr rfl hgen, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
      ← hE, hEm, hτ, zero_sub]
  have alg : ∀ (a b : A), E * E = a * E → E * b = b * E → a * b = b * a →
      E * ((E - b) * E) = a * ((E - b) * E) := by
    intro a b hEE' hc hab
    have h1 : E * ((E - b) * E) = a * (a * E) - b * (a * E) := by
      calc E * ((E - b) * E) = (E * E) * E - (E * b) * E := by noncomm_ring
        _ = (a * E) * E - (b * E) * E := by rw [hEE', hc]
        _ = a * (E * E) - b * (E * E) := by noncomm_ring
        _ = a * (a * E) - b * (a * E) := by rw [hEE']
    have h2 : a * ((E - b) * E) = a * (a * E) - b * (a * E) := by
      calc a * ((E - b) * E) = a * (E * E) - (a * b) * E := by noncomm_ring
        _ = a * (a * E) - (b * a) * E := by rw [hEE', hab]
        _ = a * (a * E) - b * (a * E) := by noncomm_ring
    rw [h1, h2]
  have hEE' : E * E = algebraMap T' A δ * E := by rw [hEE, Algebra.smul_def]
  have hyE := alg (algebraMap T' A δ) (algebraMap T' A (∑ g ∈ s, t g * ((χ g : T'ˣ) : T')))
    hEE' (Algebra.commutes _ E).symm (by rw [← map_mul, ← map_mul, mul_comm])
  have h1 : Fl (E • y₁) = 0 := by rw [map_smul, hEm]
  have h2 : E • y₁ = algebraMap T' A δ • y₁ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_eq_mul]
    rw [hy₁]
    exact hyE
  have h3 : Fl (algebraMap T' A δ • y₁) = -((δO * δO) • v) := by
    rw [map_smul, hFy, algebraMap_smul, hδ, smul_neg, smul_smul]
  rw [h2, h3] at h1
  exact neg_eq_zero.mp h1

theorem blockRhoFull : BlockRhoFull₂ := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0
    ℓ sE tE hE hEE hEm hk0 hδ hτ hiso hloc
  exact blockRhoColumn O A T' G d r χ E e₁ δ δO ι ι' colIdx hinj D j e' Kc k0 ℓ hEm hk0
    (fun m => by rw [algebraMap_smul]; exact hδ m) hiso hloc (uRep O (M := d → KO O) r χ)
    (colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0)
    (colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0)
    (fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEm hδ hτ h v hv)

end Formalism.NG
