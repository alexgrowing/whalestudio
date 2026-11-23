import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem darbouxLift_fst (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F) :
    (liftA F ξ).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ := rfl

theorem darbouxLift_snd (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F) :
    (liftA F ξ).2 = 0 := rfl

theorem darbouxLift_evI (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F) :
    evI F (liftA F ξ) = ξ := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (liftA F ξ).1 = ξ
  rw [darbouxLift_fst]; exact RingEquiv.apply_symm_apply _ _

theorem darbouxLift_mul_eq_zero (F : Type) [Field F] [NumberField F] (u : AF F) (hu : evI F u = 0)
    (ξ : mixedEmbedding.mixedSpace F) : u * liftA F ξ = 0 := by
  have h1 : u.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
  refine Prod.ext ?_ ?_
  · show u.1 * (liftA F ξ).1 = 0
    rw [h1, zero_mul]
  · show u.2 * (liftA F ξ).2 = 0
    rw [darbouxLift_snd, mul_zero]

theorem exists_darboux_lift : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V]
    {B : V → V → AF F} (d : Darboux B κ) (p q : κ → mixedEmbedding.mixedSpace F),
    ∃ w : V, At (evI F) w ∧ arch F (d.e w).1 = p ∧ arch F (d.e w).2 = q := by
  intro F _ _ κ _ V _ _ B d p q
  refine ⟨d.e.symm (fun i => liftA F (p i), fun i => liftA F (q i)), ?_, ?_, ?_⟩
  · intro u hu
    rw [← LinearEquiv.map_smul]
    have : u • ((fun i => liftA F (p i), fun i => liftA F (q i)) : (κ → AF F) × (κ → AF F)) = 0 := by
      refine Prod.ext ?_ ?_ <;> funext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] <;> exact darbouxLift_mul_eq_zero F u hu _
    rw [this, map_zero]
  · funext i
    simp only [LinearEquiv.apply_symm_apply, arch]
    exact darbouxLift_evI F (p i)
  · funext i
    simp only [LinearEquiv.apply_symm_apply, arch]
    exact darbouxLift_evI F (q i)

end GlobalTheory.ArchSch
