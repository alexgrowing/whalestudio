import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleAtPlace

open Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def idem (w₀ : InfinitePlace F) : AF F :=
  ((Pi.single w₀ 1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem idem_fst_apply (w₀ w : InfinitePlace F) :
    (idem w₀).1 w = (Pi.single w₀ 1 : InfiniteAdeleRing F) w := rfl

theorem idem_mul_self (w₀ : InfinitePlace F) : idem w₀ * idem w₀ = idem w₀ := by
  refine Prod.ext ?_ ?_
  · funext v
    show (Pi.single w₀ 1 : InfiniteAdeleRing F) v * (Pi.single w₀ 1 : InfiniteAdeleRing F) v = (Pi.single w₀ 1 : InfiniteAdeleRing F) v
    by_cases h : v = w₀
    · subst h; simp
    · simp [Pi.single_apply, h]
  · show (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    simp

theorem idem_mul_one_sub (w₀ : InfinitePlace F) : idem w₀ * (1 - idem w₀) = 0 := by
  rw [mul_sub, mul_one, idem_mul_self, sub_self]

theorem one_sub_mul_idem (w₀ : InfinitePlace F) : (1 - idem w₀) * idem w₀ = 0 := by
  rw [sub_mul, one_mul, idem_mul_self, sub_self]

theorem one_sub_mul_one_sub (w₀ : InfinitePlace F) : (1 - idem w₀) * (1 - idem w₀) = 1 - idem w₀ := by
  rw [mul_sub, mul_one, one_sub_mul_idem, sub_zero]

def tv (w₀ : InfinitePlace F) (ξ : E) : AE F E :=
  idem w₀ ⊗ₜ[F] ξ + (1 - idem w₀) ⊗ₜ[F] (1 : E)

theorem tv_mul (w₀ : InfinitePlace F) (ξ η : E) : tv w₀ ξ * tv w₀ η = tv w₀ (ξ * η) := by
  simp only [tv, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, idem_mul_self, idem_mul_one_sub,
    one_sub_mul_idem, one_sub_mul_one_sub, TensorProduct.zero_tmul, add_zero, zero_add, mul_one]

theorem tv_one (w₀ : InfinitePlace F) : tv (E := E) w₀ 1 = 1 := by
  rw [tv, ← TensorProduct.add_tmul, add_sub_cancel, Algebra.TensorProduct.one_def]

def tU (w₀ : InfinitePlace F) (ξ : E) (hξ : ξ ≠ 0) : (AE F E)ˣ where
  val := tv w₀ ξ
  inv := tv w₀ ξ⁻¹
  val_inv := by rw [tv_mul, mul_inv_cancel₀ hξ, tv_one]
  inv_val := by rw [tv_mul, inv_mul_cancel₀ hξ, tv_one]

theorem tv_sub_one (w₀ : InfinitePlace F) (ξ : E) : tv w₀ ξ - 1 = idem w₀ ⊗ₜ[F] (ξ - 1) := by
  rw [← tv_one (E := E) w₀, tv, tv, TensorProduct.tmul_sub]
  abel

theorem at_tv (w₀ : InfinitePlace F) (ξ : E) : At (evI F) (tv w₀ ξ - 1) := by
  intro u hu
  have h1 : u.1 = 0 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [tv_sub_one, TensorProduct.smul_tmul']
  have : u • idem w₀ = 0 := by
    rw [smul_eq_mul]
    refine Prod.ext ?_ ?_
    · show u.1 * (idem w₀).1 = 0
      rw [h1, zero_mul]
    · show u.2 * 0 = 0
      rw [mul_zero]
  rw [this, TensorProduct.zero_tmul]

theorem piInf_tv {w : InfinitePlace F} (τ : EmbOver E w) (w₀ : InfinitePlace F) (ξ : E) :
    piInf τ (tv w₀ ξ) = if w = w₀ then (τ : E →+* ℂ) ξ else 1 := by
  have he : ∀ a : AF F, ∀ x : E, piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * (τ : E →+* ℂ) x := by
    intro a x
    show infEmb τ (compInf F E w (a ⊗ₜ[F] x)) = _
    rw [compInf]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rw [infEmb_tmul]
    rfl
  rw [tv, map_add, he, he]
  have h1 : (1 - idem w₀ : AF F).1 w = 1 - (idem w₀).1 w := rfl
  rw [h1, idem_fst_apply]
  by_cases h : w = w₀
  · subst h; simp
  · simp [Pi.single_apply, h]

end GlobalTheory.IdeleAtPlace

open Classical GlobalTheory.IdeleAtPlace in
theorem GlobalTheory.IdeleAtPlace.exists_idele_char_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (w₀ : InfinitePlace F) (ξ : E), ξ ≠ 0 → ∃ t : (AE F E)ˣ, ∀ (χ : Chr F E) (m : InfinitePlace F → ℤ), HasExp emb χ m → (χ t : ℂ) = ((emb w₀).1 ξ / (‖(emb w₀).1 ξ‖ : ℂ)) ^ m w₀ := by
  intro F E _ _ _ _ _ σ _ emb w₀ ξ hξ
  refine ⟨tU w₀ ξ hξ, fun χ m hχ => ?_⟩
  rw [hχ (tU w₀ ξ hξ) (at_tv w₀ ξ)]
  show ∏ w, (piInf (emb w) (tv w₀ ξ) / ((‖piInf (emb w) (tv w₀ ξ)‖ : ℝ) : ℂ)) ^ m w = _
  rw [Finset.prod_eq_single w₀]
  · rw [piInf_tv, if_pos rfl]
  · intro w _ hw
    rw [piInf_tv, if_neg hw]
    simp
  · intro h; exact absurd (Finset.mem_univ w₀) h

end
