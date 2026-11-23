import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProduStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansion
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZmChar

theorem ch_mul {M : ℕ} (χ : DirichletCharacter ℂ M) (x y : ℤ) : ch χ (x * y) = ch χ x * ch χ y := by
  simp [ch]

theorem ch_add_dvd {M : ℕ} (χ : DirichletCharacter ℂ M) (K : ℕ) (h : M ∣ K) (x : ℤ) : ch χ (x + K) = ch χ x := by
  obtain ⟨t, rfl⟩ := h
  simp [ch, ZMod.natCast_self]

theorem ch_zero {M : ℕ} [Fact (1 < M)] (χ : DirichletCharacter ℂ M) : ch χ 0 = 0 := by
  simp only [ch, Int.cast_zero]
  exact MulChar.map_nonunit χ not_isUnit_zero

theorem inv_apply_neg_one {M : ℕ} (χ : DirichletCharacter ℂ M) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : ZMod M) = -1 := by simpa using Ring.inverse_unit (-1 : (ZMod M)ˣ)
  rw [this]

theorem isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d (M : ℤ)) : IsUnit (d : ZMod M) := by
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod M) hab
  push_cast at this
  simp [ZMod.natCast_self] at this
  exact isUnit_iff_exists_inv.2 ⟨a, by rw [mul_comm]; exact this⟩

theorem mul_inv_unit {M : ℕ} (χ : DirichletCharacter ℂ M) (d : ℤ) (h : IsUnit (d : ZMod M)) : ch χ d * ch χ⁻¹ d = 1 := by
  show χ (d : ZMod M) * χ⁻¹ (d : ZMod M) = 1
  rw [← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply h

end GlobalTheory.EisM.ZmChar

namespace GlobalTheory.EisM.ZmChar

theorem cop_dvd {d : ℤ} {A B : ℕ} (h : IsCoprime d (B : ℤ)) (hAB : A ∣ B) : IsCoprime d (A : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hAB)

end GlobalTheory.EisM.ZmChar

open GlobalTheory.EisM.ZmChar in

theorem GlobalTheory.zm_char_mf : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  intro k j N l m ε u θ ν ψ hjk hN hl hm hlN hu hmul hε hpar1 hpar2
  have hl1 : 1 < l ^ m := Nat.one_lt_pow (by omega) hl.one_lt
  haveI : Fact (1 < l ^ m) := ⟨hl1⟩
  have hlm : 0 < l ^ m := by omega
  have hup : ∀ K : ℕ, N ∣ K → ∀ x, u (x + K) = u x := by
    intro K hK x
    obtain ⟨t, rfl⟩ := hK
    have e : ((N * t : ℕ) : ℤ) = (t : ℤ) * N := by push_cast; ring
    rw [e]
    exact (Function.Periodic.nat_mul (show Function.Periodic u (N : ℤ) from hu) t) x
  obtain ⟨c, hE1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (k - 1 - j) (N * l ^ m) 1 (fun x => u x * ch ψ x) (fun _ => 1)
    (fun d => ch θ⁻¹ d * ch ψ d) (fun _ => 1) (by omega) (by positivity) one_pos (by simp [ch_zero])
    (fun x => by rw [hup _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) (fun _ => rfl)
    (fun d hd => by
      have hdN : IsCoprime d (N : ℤ) := cop_dvd hd (by simp)
      refine ⟨fun x => ?_, fun x => by ring⟩
      rw [hmul d x hdN, ch_mul]
      ring)
    (by simp only [ch, Int.cast_neg, Int.cast_one, mul_one]; rw [inv_apply_neg_one, mul_comm, hpar1])
  obtain ⟨c', hE2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (j + 1) (l ^ m) N (ch ψ⁻¹) (ch ν) (ch ψ⁻¹) (ch ν) (by omega) hlm hN
    (ch_zero _) (ch_add_dvd _ _ dvd_rfl) (ch_add_dvd _ _ dvd_rfl)
    (fun d _ => ⟨fun x => by rw [ch_mul, mul_comm], fun x => by rw [ch_mul, mul_comm]⟩)
    (by simp only [ch, Int.cast_neg, Int.cast_one]; rw [inv_apply_neg_one, hpar2])
  have hD1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (k - 1 - j) (N * l ^ m * 1) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self l (by omega)) _) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
      ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)]) hE1).2
  have hD2 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (j + 1) (l ^ m * N) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) hE2).2
  have hD1' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD1
  have hD2' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD2
  have P := GlobalTheory.EisM.mul_main.2 _ _ _ _ _ _ _ hD1' hD2'
  rw [GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product k l j u (ch ν) (ch ψ) (ch ψ⁻¹) c c' hjk]
  have hk : k - 1 - j + (j + 1) = k := by omega
  rw [hk] at P
  refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 (ch ε) _ (fun d hd => ?_) P
  have hU := mul_inv_unit ψ d (isUnit_of_coprime d (cop_dvd hd (dvd_mul_of_dvd_right (pow_dvd_pow l (by omega)) _)))
  subst hε
  simp only [ch, MulChar.mul_apply] at hU ⊢
  linear_combination (θ⁻¹ (d : ZMod N) * ν (d : ZMod N)) * hU
