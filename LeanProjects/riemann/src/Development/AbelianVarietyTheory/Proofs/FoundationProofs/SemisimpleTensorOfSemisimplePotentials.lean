import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVBStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivialStatement

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.Comp

theorem lift_mem_lam {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (P : FreeAlgebra E Letter) :
    ∀ p ∈ H3.abelian₂ X l E,
      (FreeAlgebra.lift E (X.opV N l E) P p.1, FreeAlgebra.lift E (opL E N l) P p.2) ∈ H3.abelian₂ X l E := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro p hp
    convert (H3.abelian₂ X l E).smul_mem r hp using 1
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  | grade1 T =>
    intro p hp
    simpa using GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T p hp
  | mul a b ha hb =>
    intro p hp
    simpa using ha _ (hb p hp)
  | add a b ha hb =>
    intro p hp
    simpa using (H3.abelian₂ X l E).add_mem (ha p hp) (hb p hp)

theorem ssbb_of_ssPotB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ ι lam hSS
  haveI : CharZero E := RingHom.charZero ι.toRingHom
  obtain ⟨P, hPA, hP1, hP⟩ := GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv N l w ι lam hSS
  refine ⟨P, hPA, hP1, fun x hx T hT => ?_⟩
  obtain ⟨G, hG, hxG⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB ε X N l w (GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer ε X hε hj N l w hl2 hN hNl hw) x hx
  have h1 := lift_mem_lam ε X N l P (x, G) hxG
  have h2 := GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T _ h1
  have h3 := (H3.abelian₂ X l E).sub_mem h2 ((H3.abelian₂ X l E).smul_mem (lam T) h1)
  have h4 : ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        (FreeAlgebra.lift E (X.opV N l E) P x),
      (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
        (FreeAlgebra.lift E (opL E N l) P G)) ∈ H3.abelian₂ X l E := by
    simpa using h3
  exact GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial ε X hε hj N l w (by omega) inferInstance _ _ h4 (hP G hG T hT)

end GlobalTheory.KZ.Comp
