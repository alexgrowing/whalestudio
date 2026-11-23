import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchSch

theorem darboux_rho_acts_sch {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V]
    [Module (AF F) V] {B : V → V → AF F} (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (z : V)
    (hz : At (evI F) z) (f g : SInf F κ)
    (hg : ⇑g = sch (trP F κ) (arch F (d.e z).1) (arch F (d.e z).2) ⇑f) :
    Acts (evI F) (d.rho ψ z) ⇑f ⇑g := by
  obtain ⟨e, he⟩ : ∃ e : AF F →+* mixedEmbedding.mixedSpace F, ∀ a, evI F a = e a :=
    ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _), fun _ => rfl⟩
  have hab : ∀ u : AF F, evI F u = 0 → u • (d.e z).1 = 0 ∧ u • (d.e z).2 = 0 := by
    intro u hu
    have h0 : u • d.e z = 0 := by rw [← LinearEquiv.map_smul, hz u hu, map_zero]
    exact ⟨by simpa using congrArg Prod.fst h0, by simpa using congrArg Prod.snd h0⟩
  intro r hr
  funext x
  have hra : r (x + (d.e z).1) = r x := hr.1 x _ (fun u hu => (hab u hu).1)
  have ht : At (evI F) (x ⬝ᵥ (d.e z).2 + ⅟(2 : AF F) * ((d.e z).1 ⬝ᵥ (d.e z).2)) := by
    intro u hu
    have hb0 := (hab u hu).2
    rw [smul_eq_mul, mul_add, mul_left_comm, ← smul_eq_mul u (x ⬝ᵥ _), ← smul_eq_mul u ((d.e z).1 ⬝ᵥ _),
      ← dotProduct_smul, ← dotProduct_smul, hb0]
    simp
  have hpsi := hψ.2.2 _ ht
  have h2 : e (⅟(2 : AF F)) + e (⅟(2 : AF F)) = 1 := by rw [← map_add, invOf_two_add_invOf_two, map_one]
  have hT : ∀ S : mixedEmbedding.mixedSpace F, Algebra.trace ℝ _ (e (⅟(2 : AF F)) * S) =
      Algebra.trace ℝ _ S / 2 := by
    intro S
    have : Algebra.trace ℝ _ (e (⅟(2 : AF F)) * S) + Algebra.trace ℝ _ (e (⅟(2 : AF F)) * S) =
        Algebra.trace ℝ _ S := by rw [← map_add, ← add_mul, h2, one_mul]
    linarith
  have hx : (fun i => evI F ((x + (d.e z).1) i)) = (fun i => evI F (x i)) + fun i => evI F ((d.e z).1 i) := by
    funext i; simp [he]
  simp only [Darboux.rho, schr, tens, hg, sch, ech, mixedTracePairing_apply, arch]
  rw [hpsi, hra, hx]
  simp only [he, map_add, map_mul, dotProduct, map_sum, hT]
  rw [show arch F (d.e z).1 = fun i => e ((d.e z).1 i) from funext fun i => he _]
  ring

end GlobalTheory.ArchSch
