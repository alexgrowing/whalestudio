import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOneMemOfIsRayFieldIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContainsRayFieldSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AtMember

open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem odd_of_mem_levelPrimes (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) : Odd p := by
  have h := (P.level_cond p hp).2
  have h2 : (2 : ℕ) ∣ P.host.QS * P.host.q * P.host.d := ((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans P.host.tower_dvd).mul_right _).mul_right _)
  rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd p h2, h]

set_option maxHeartbeats 4000000 in

theorem fieldTies_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre),
    X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  intro hR X f δ hx
  have := GlobalTheory.Mem.FieldsEx.host_cplx X.B.toPre
  have hFO : FO X.toD7 = X.B.KsC := SetLike.ext fun z => (mem_FO_assembled_iff X z).trans (X.B.mem_KsC).symm
  have hxe : X.B.KsC = Fld.listField δ f := hx
  obtain ⟨hray, -, hchar, -⟩ := Base.KsExact.lower hx
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hpl : p ∈ X.B.host.levelPrimes := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_level.1, X.B.host.pde_level.2]
    have hpp : p.Prime := (X.B.toPre.level_cond p hpl).1
    have hdvd : X.B.host.g 0 * X.B.host.g 1 * p ∣ Fld.modulus X.B.toPre := by
      rcases hp with rfl | rfl
      · exact dvd_mul_right _ _
      · exact ⟨X.B.host.pde, by unfold Fld.modulus; ring⟩
    have hpd : p ∣ Fld.modulus X.B.toPre := (dvd_mul_left p _).trans hdvd
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rw [hFO]
      exact hray (GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn X.B.host.E X.B.host.φ₀ (Fld.modulus X.B.toPre) p δ.ray (Fld.modulus_ne_zero _) hpd δ.isRay)
    · have hn0 : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
        Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hpp.pos
      refine GlobalTheory.FieldSize.curveOver_of_weberSet X.toD7 _ hn0 ?_ fun L hL => ?_
      · rw [hFO]
        exact X.B.imField_le_KsC ⟨_, rfl⟩
      · have hodd : Odd (X.B.host.g 0 * X.B.host.g 1 * p) :=
          ((odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 0)).mul
            (odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 1))).mul (odd_of_mem_levelPrimes X.B.toPre hpl)
        have h3 : 3 ≤ X.B.host.g 0 * X.B.host.g 1 * p := by
          have a := (X.B.host.g_prime 0).two_le
          have b := (X.B.host.g_prime 1).two_le
          have c := hpp.two_le
          have := Nat.mul_le_mul (Nat.mul_le_mul a b) c
          omega
        rw [hFO]
        exact (GlobalTheory.FieldSize.WeberRay.weberSet_subset_ray X.B.toPre δ L hL _ hodd h3 hdvd).trans fun z hz => hray hz
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), fun x => ?_, fun x => ?_, fun L hL => ?_⟩
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del X.B.KsC f.isDel.fin
      ((le_sup_right.trans (le_sup_left.trans le_sup_left)).trans hchar) x
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del' X.B.KsC f.isDel'.fin ((le_sup_right.trans le_sup_left).trans hchar) x
  · have hle : FO X.toD7 ≤ δ.Om := by
      rw [hFO, hxe]
      exact GlobalTheory.Mem.FieldsEx.listField_le_Om δ f
    exact GlobalTheory.FieldSize.sz_mono_and_of_le.2 _ _ _ _ hle (GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial hR X.B.toPre δ L hL)

end GlobalTheory.AtMember

end
