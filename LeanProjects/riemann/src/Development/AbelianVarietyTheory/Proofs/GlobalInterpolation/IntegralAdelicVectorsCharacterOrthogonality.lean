import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem Bd_add_left_AF (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem Bd_rat_rat (a : Fin N → F) (η ξ : Fin N → F) :
    Bd (AF F) a (rat η) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) := by
  simp only [Bd, rat, map_sum, map_mul, Algebra.algebraMap_self, RingHom.id_apply]

theorem charOrth : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  intro F _ _ N ψ lam ν a hC D hD _ ξ hξ
  haveI := hC.2.2.2.1.1
  have hmem : ∀ u : Fin N → AF F, u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) →
      ∃ η, u = rat η := by
    let φ : (Fin N → F) →+ (Fin N → AF F) :=
      AddMonoidHom.mk' rat (fun x y => by funext l; simp only [rat, Pi.add_apply, map_add])
    intro u hu
    have hle : AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ≤ φ.range :=
      (AddSubgroup.closure_le _).mpr (by rintro _ ⟨η, rfl⟩; exact ⟨η, rfl⟩)
    obtain ⟨η, hη⟩ := hle hu
    exact ⟨η, hη.symm⟩
  haveI : (muV N ν).IsAddLeftInvariant := by unfold muV; infer_instance
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) := by
    have hs : (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) :
        Set (Fin N → AF F)).Countable :=
      (Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun u hu => by
        obtain ⟨η, rfl⟩ := hmem u hu
        exact ⟨η, rfl⟩
    exact hs.to_subtype
  obtain ⟨_, ⟨_, _, hF, x, hx⟩, _, _, ha⟩ := hC
  have hadd : ∀ u v : Fin N → AF F, ψ (Bd (AF F) a (u + v) (rat ξ)) =
      ψ (Bd (AF F) a u (rat ξ)) * ψ (Bd (AF F) a v (rat ξ)) := fun u v => by
    rw [Bd_add_left_AF, AddChar.map_add_eq_mul]
  have hper : ∀ g ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))),
      ∀ u, ψ (Bd (AF F) a (g + u) (rat ξ)) = ψ (Bd (AF F) a u (rat ξ)) := by
    intro g hg u
    obtain ⟨η, rfl⟩ := hmem g hg
    rw [hadd, Bd_rat_rat, hF, one_mul]
  obtain ⟨l, hl⟩ : ∃ l, ξ l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hξ (funext h)
  have hc : (2 * a l * ξ l) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ha l)) hl
  set u₀ : Fin N → AF F := Pi.single l (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) with hu₀def
  have hu₀ : ψ (Bd (AF F) a u₀ (rat ξ)) = ψ x := by
    congr 1
    simp only [Bd, rat]
    rw [Finset.sum_eq_single l]
    · rw [hu₀def, Pi.single_eq_same]
      have e : algebraMap F (AF F) (2 * a l) * (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) *
          algebraMap F (AF F) (ξ l) = algebraMap F (AF F) (2 * a l * ξ l * (2 * a l * ξ l)⁻¹) * x := by
        simp only [map_mul]; ring
      rw [e, mul_inv_cancel₀ hc, map_one, one_mul]
    · intro b _ hb
      rw [hu₀def, Pi.single_eq_of_ne hb]
      simp
    · intro h; exact absurd (Finset.mem_univ l) h
  have hD' := hD.vadd_of_comm u₀
  have h1 := hD.setIntegral_eq hD' (f := fun u => ψ (Bd (AF F) a u (rat ξ))) (fun g s => by
    show ψ (Bd (AF F) a ((g : Fin N → AF F) + s) (rat ξ)) = _
    exact hper g g.2 s)
  have h2 := (measurePreserving_add_left (muV N ν) u₀).setIntegral_image_emb
    (measurableEmbedding_addLeft u₀) (fun u => ψ (Bd (AF F) a u (rat ξ))) D
  have e : u₀ +ᵥ D = (fun s => u₀ + s) '' D := rfl
  rw [e, h2] at h1
  simp only [hadd, hu₀] at h1
  rw [integral_const_mul] at h1
  have hx1 : (1 : ℂ) - ψ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : ((1 : ℂ) - ψ x) * ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hx1

end GlobalTheory.SWQ
