import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

noncomputable def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq_evIHom {F : Type} [Field F] [NumberField F] (a : AF F) : evI F a = evIHom F a := rfl

theorem trace_evI_heis {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {κ : Type} [Fintype κ]
    (x a b : κ → AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ b + ⅟(2 : AF F) * a ⬝ᵥ b)) =
      trP F κ (locV x) (locV b) + trP F κ (locV a) (locV b) / 2 := by
  have hdot : ∀ y : κ → AF F, evIHom F (y ⬝ᵥ b) = ∑ i, locV y i * locV b i := by
    intro y
    simp only [dotProduct, map_sum, map_mul, locV, evI_eq_evIHom]
  have h2 : ∀ t : AF F, evIHom F (⅟(2 : AF F) * t) = (1 / 2 : ℝ) • evIHom F t := by
    intro t
    have h : (2 : ℝ) • evIHom F (⅟(2 : AF F) * t) = evIHom F t := by
      rw [two_smul, ← map_add, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [← h, smul_smul]
    norm_num
  rw [evI_eq_evIHom, map_add, h2, hdot, hdot, map_add, map_smul, trP, trP, smul_eq_mul]
  ring

theorem acts_rho_of_at_inf : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F} {κ : Type} [Fintype κ]
      (dc : Darboux Bf κ) (w : W'), At (evI F) w → ∀ f f₁ : SInf F κ,
      ⇑f₁ = schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) ⇑f → Acts (evI F) (dc.rho ψ w) ⇑f ⇑f₁ := by
  intro F _ _ ψ hψ W' _ _ Bf κ _ dc w hw f f₁ hf r hr
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr.1 x _ ha, hf, hloc, schrF]
  exact (mul_assoc _ _ _).symm

end GlobalTheory.ArchUniq
