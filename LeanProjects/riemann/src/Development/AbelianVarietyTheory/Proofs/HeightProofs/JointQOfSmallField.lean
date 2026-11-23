import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowMemRatOneSupCongOne

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem exists_xiOK_of_root (D : D7) (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (h : Complex.exp (2 * Real.pi * Complex.I / (xiOrd D.host (D.host.g 0 * D.host.g 1 * p) : ℕ)) ∈ FO D) :
    ∃ xi, XiOK D p xi := by
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    exacts [D.host.pde_prime.pos, D.host.pde'_prime.pos]
  have hN : 0 < D.host.g 0 * D.host.g 1 * p :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp0
  obtain ⟨xi, m, hm, a1, a2, a3, a4, -⟩ := GlobalTheory.NormOneChar.exists_xi D p hp
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 * p : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN.ne'
  have : Finite (𝓞 D.host.E ⧸ Ideal.span {((D.host.g 0 * D.host.g 1 * p : ℕ) : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have ho : 0 < xiOrd D.host (D.host.g 0 * D.host.g 1 * p) :=
    Nat.mul_pos (Nat.mul_pos two_pos (classNumber_pos _)) Nat.card_pos
  refine ⟨xi, a1, a2, a3, ⟨m, hm, a4⟩, fun x hn => GlobalTheory.NormOneChar.mem_of_pow_eq_one ho h ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg Units.val (GlobalTheory.NormOneChar.tame_pow_eq_one D _ xi hN a1 a2 x hn)

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩

set_option maxHeartbeats 4000000 in

theorem jointQ_of_small_field : ∀ (X : Stages) (F : IntermediateField ℚ ℂ), Rich X.B.toPre F → (∀ L : ℝ, HostSz X.B.host L → Sz F (poR X.B.R L) (poR X.B.R L)) → (∀ z, z ∈ F ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z) → JointQ X.toD7 := by
  intro X F hR hS hF
  obtain rfl : F = FO X.toD7 := SetLike.ext fun z => (hF z).trans (mem_FO_assembled_iff X z).symm
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hp0 : 0 < p := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_prime.pos, X.B.host.pde'_prime.pos]
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rcases hp with rfl | rfl
      exacts [hR.roots _ (by simp), hR.roots _ (by simp)]
    · exact curveOver_of_weberSet X.toD7 _
        (Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0) (hR.host _)
        fun L hL => hR.weber L hL p (by simpa using hp)
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), exists_xiOK_of_root _ _ (Or.inl rfl) ?_,
    exists_xiOK_of_root _ _ (Or.inr rfl) ?_, hS⟩
  · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde)) (by simp)
  · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde')) (by simp)

end GlobalTheory.FieldSize
