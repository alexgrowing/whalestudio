import Mathlib
import GroundTheory.PAdicHodge.BdRAlg
import GroundTheory.PAdicHodge.FactorizationFactorialLe
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Acris :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.ACris.ACris ℂ_[l] l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Ainf :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.AInf ℂ_[l] l

noncomputable def UpperTheory.Reformulated.B.Qi53.zA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → ℤ_[l] →+* UpperTheory.Reformulated.B.Qi53.Acris l :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi53.Ainf l) (UpperTheory.Reformulated.B.Qi53.Acris l)).comp
        (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt l)

theorem UpperTheory.Reformulated.B.Qi53.zA_smul.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {N : Type u_1} [inst_1 : AddCommGroup N]
      [inst_2 : _root_.Module (UpperTheory.Reformulated.B.Qi53.Acris l) N] (n : ℕ),
      (∀ (y : N), (↑l : UpperTheory.Reformulated.B.Qi53.Acris l) ^ n • y = (0 : N)) →
        ∀ (z : ℤ_[l]) (y : N),
          (UpperTheory.Reformulated.B.Qi53.zA l : ℤ_[l] → UpperTheory.Reformulated.B.Qi53.Acris l) z • y =
            ((PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) z).val • y := by
  intro l _ N _ _ n h z y
  have hz : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := by
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime l).ne_zero⟩
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  obtain ⟨w, hw⟩ := hz
  have hz' : z = (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by
    rw [← hw]; ring
  generalize (PadicInt.toZModPow n z).val = m at hz' ⊢
  rw [hz', map_add, map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_smul, h, add_zero,
    Nat.cast_smul_eq_nsmul]
