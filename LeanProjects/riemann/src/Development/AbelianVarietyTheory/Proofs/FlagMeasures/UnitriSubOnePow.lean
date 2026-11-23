import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsCharIdemOfIsSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev.LevelIdem

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

theorem unitri_sub_one_pow {k : Type} [Field k] {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h1 : ∀ a, M a a = 1) (h2 : ∀ a b, b < a → M a b = 0) : (M - 1) ^ N = 0 := by
  have ht : (M - 1).BlockTriangular id := by
    intro a b hab
    have hab' : b < a := hab
    rw [Matrix.sub_apply, h2 a b hab', Matrix.one_apply_ne hab'.ne', sub_zero]
  have h := Matrix.aeval_self_charpoly (M - 1)
  rw [Matrix.charpoly_of_isUpperTriangular _ ht] at h
  simpa [h1] using h

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem spec_of_eps (L : Lev g N) (χ : GG g N → ℂ) (hp : IsProj (eps L.Mem χ)) (a : MonoidAlgebra ℂ (GG g N))
    (ha : ∀ x, a.coeff x = eps L.Mem χ x) :
    a * a = a ∧ IsSA a ∧ ∀ q, a.coeff q ≠ 0 → ((q : Matrix (Fin N) (Fin N) (ZMod g)) - 1) ^ N = 0 := by
  have e : a = alg (eps L.Mem χ) := by
    ext x
    rw [coeff_alg, ha]
  refine ⟨by rw [e, ← alg_conv, hp.1], fun q => ?_, fun q hq => ?_⟩
  · rw [ha, ha, hp.2]
    rfl
  · rw [ha] at hq
    have hm : L.Mem q := by
      by_contra hc
      exact hq (if_neg hc)
    exact unitri_sub_one_pow _ hm.1.1 hm.1.2

theorem spec_eDat (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (b : Bool) (s k : ℕ) (h : s + k < N)
    (H : ∀ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) x,
      (eDat g N P φ ψ).coeff x = (levOfChar ψ hψ N b s k h).e x) (ψ : AddChar (ZMod g) ℂ) :
    eDat g N P φ ψ * eDat g N P φ ψ = eDat g N P φ ψ ∧ IsSA (eDat g N P φ ψ) ∧
      ∀ q, (eDat g N P φ ψ).coeff q ≠ 0 → ((q : Matrix (Fin N) (Fin N) (ZMod g)) - 1) ^ N = 0 := by
  by_cases hψ : ψ = 1
  swap
  · exact spec_of_eps _ _ (isProj_e _) _ (H ψ hψ)
  subst hψ
  have h0 : (ZMod.stdAddChar (N := g)) ≠ 1 := (levStandard g N b s k h).hψ
  set L := levOfChar ZMod.stdAddChar h0 N b s k h with hL
  haveI : Nonempty {u // L.Mem u} := ⟨⟨1, mem_one L⟩⟩
  have hc : (Nat.card {u // L.Mem u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (fun u : GG g N => P u.val) = L.Mem := by
    funext x
    have hx := H _ h0 x
    rw [coeff_eDat, Lev.e] at hx
    unfold eps at hx
    refine propext ⟨fun h1 => ?_, fun h1 => ?_⟩
    · by_contra h2
      haveI : Nonempty {u : GG g N // P u.val} := ⟨⟨x, h1⟩⟩
      have hc' : (Nat.card {u : GG g N // P u.val} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
      rw [if_pos h1, if_neg h2] at hx
      refine div_ne_zero (inv_ne_zero fun h3 => ?_) hc' hx
      have := AddChar.norm_apply (ZMod.stdAddChar (N := g)) (φ x.val)
      beta_reduce at h3
      rw [h3] at this
      simp at this
    · by_contra h2
      rw [if_neg h2, if_pos h1] at hx
      exact div_ne_zero (inv_ne_zero (chi_ne L x)) hc hx.symm
  refine spec_of_eps L (fun _ => 1) (GlobalTheory.BadShare.EpsProj.isProj_eps (mem_one L) (fun _ _ => mem_mul L) rfl (fun _ _ _ _ => by simp)) _
    fun x => ?_
  rw [coeff_eDat, hP]
  rfl

theorem eUk_eJk_spec : ∀ (D : D7) (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), a = eUk D k ψ₀ ∨ a = eJk D k ψ₀ → a * a = a ∧ IsSA a ∧ ∀ q, a.coeff q ≠ 0 → ((q : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) - 1) ^ D.R.r = 0 := by
  intro D k ψ a ha
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hN : D.R.r = D.R.k + 2 * (D.R.m / 2 - 1) + 1 := by
    have := dimS_eq D.R
    unfold Ranks.rS at this
    omega
  have h : (D.R.m / 2 - 1) + D.R.k < D.R.r := by omega
  rcases ha with rfl | rfl
  · exact spec_eDat _ _ false _ _ h (fun ψ hψ x => coeff_eU ψ hψ _ _ h x) ψ
  · exact spec_eDat _ _ true _ _ h (fun ψ hψ x => coeff_eJ ψ hψ _ _ hN h x) ψ

end GlobalTheory.RowLev.LevelIdem
