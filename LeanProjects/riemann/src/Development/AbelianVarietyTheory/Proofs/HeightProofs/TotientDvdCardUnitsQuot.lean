import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem totient_dvd_card_units_quot (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : 0 < N) :
    N.totient ∣ Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ := by
  have : NeZero N := ⟨hN.ne'⟩
  have hc : CharP (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) N := by
    refine ⟨fun m => ?_⟩
    have h1 : Ideal.comap (algebraMap ℤ (𝓞 E)) (Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(N : ℤ)})) =
        Ideal.span {(N : ℤ)} := Ideal.comap_map_eq_self_of_faithfullyFlat _
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at h1
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})), Ideal.Quotient.eq_zero_iff_mem,
      ← Int.natCast_dvd_natCast, ← Ideal.mem_span_singleton (x := (m : ℤ)), ← h1, Ideal.mem_comap, map_natCast]
  have hi : Function.Injective (ZMod.castHom (dvd_refl N) (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})) :=
    ZMod.castHom_injective _
  have := Subgroup.card_dvd_of_injective _ (Units.map_injective
    (f := (ZMod.castHom (dvd_refl N) (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})).toMonoidHom) hi)
  rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at this

set_option maxHeartbeats 4000000 in

theorem fieldOK0_and_zeta_mem : ∀ (X : Stages) (F : IntermediateField ℚ ℂ), Rich X.B.toPre F → (∀ z, z ∈ F ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z) → ∀ p : ℕ, (p = X.toD7.host.pde ∨ p = X.toD7.host.pde') → FieldOK0 X.toD7 p ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber X.toD7.host.E) ∈ FO X.toD7 := by
  intro X F hR hF p hp'
  obtain rfl : F = FO X.toD7 := SetLike.ext fun z => (hF z).trans (mem_FO_assembled_iff X z).symm
  have hp : p = X.B.host.pde ∨ p = X.B.host.pde' := hp'
  have hp0 : p.Prime := by
    rcases hp with rfl | rfl
    exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
  have key : FieldOK0 X.toD7 p := by
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rcases hp with rfl | rfl
      exacts [hR.roots _ (by simp), hR.roots _ (by simp)]
    · exact curveOver_of_weberSet X.toD7 _
        (Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0.pos) (hR.host _)
        fun L hL => hR.weber L hL p (by simpa using hp)
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key, ?_⟩
  have hN : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
    Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0.pos
  have hroot : Complex.exp (2 * Real.pi * Complex.I /
      (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * p) : ℕ)) ∈ FO X.toD7 := by
    rcases hp with rfl | rfl
    · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde)) (by simp)
    · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde')) (by simp)
  have hI : Ideal.span {((X.B.host.g 0 * X.B.host.g 1 * p : ℕ) : 𝓞 X.B.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN.ne'
  have : Finite (𝓞 X.B.host.E ⧸ Ideal.span {((X.B.host.g 0 * X.B.host.g 1 * p : ℕ) : 𝓞 X.B.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have ho : 0 < xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * p) :=
    Nat.mul_pos (Nat.mul_pos two_pos (classNumber_pos _)) Nat.card_pos
  have h15 : 15 ∣ p - 1 := by
    have := X.B.host.pde_mod
    rcases hp with rfl | rfl <;> omega
  have hd : 15 * classNumber X.B.host.E ∣ xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * p) := by
    have h1 := (h15.trans ((Nat.totient_prime hp0).symm.dvd.trans
      (Nat.totient_dvd_of_dvd (Dvd.intro_left _ rfl)))).trans (totient_dvd_card_units_quot X.B.host.E _ hN)
    rw [mul_comm]
    exact Nat.mul_dvd_mul (Dvd.intro_left _ rfl) h1
  refine GlobalTheory.NormOneChar.mem_of_pow_eq_one ho hroot ?_
  obtain ⟨c, hc⟩ := hd
  have hh : 15 * classNumber X.B.host.E ≠ 0 := mul_ne_zero (by norm_num) (classNumber_ne_zero _)
  rw [hc, pow_mul]
  have := (Complex.isPrimitiveRoot_exp _ hh).pow_eq_one
  change (Complex.exp (2 * Real.pi * Complex.I / (15 * classNumber X.B.host.E : ℕ)) ^ _) ^ c = 1
  rw [this, one_pow]

end GlobalTheory.FieldSize
