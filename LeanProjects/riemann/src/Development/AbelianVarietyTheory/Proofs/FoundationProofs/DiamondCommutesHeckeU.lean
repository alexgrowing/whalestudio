import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ.DiamU

theorem isDiam_sgD_of_coprime' {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := (Nat.coprime_zero_right d).1 hd
    subst h1
    exact Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem upper_mul_eq {N l d : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (hl : 0 < l) (j k : ℕ)
    (hk : (k : ZMod l) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod l) =
      (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod l)) :
    ∃ s : SL(2, ℤ), IsDiam N l d s ∧
      !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (s : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (k : ℤ); 0, (l : ℤ)] := by
  obtain ⟨h0, hd⟩ := hσ
  rw [Subgroup.mem_inf] at h0
  have hcN := CongruenceSubgroup.Gamma0_mem.1 h0.1
  have hcl := CongruenceSubgroup.Gamma0_mem.1 h0.2
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [en] at hd
  have hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk hcl ⊢
    rw [hcl]
    linear_combination -hk
  obtain ⟨q, hq⟩ := hdiv
  set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef
  have hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)] := by
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq
  have hS : S.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, σ.det_coe] at h
    simp only [Matrix.det_fin_two_of] at h
    have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
    have : ((l : ℤ)) * 1 = S.det * (l : ℤ) := by linarith
    exact (mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))
  refine ⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod l) = 0
    rw [Int.cast_mul, hcl, mul_zero]
  · simp only [en]
    simp [hSdef]
    rw [hcN]; simpa using hd

private def res (l : ℕ) (x : ℤ) : ℕ := (x % (l : ℤ)).toNat

private theorem res_lt {l : ℕ} (hl : 0 < l) (x : ℤ) : res l x < l := by
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  unfold res; omega

private theorem res_cast {l : ℕ} (hl : 0 < l) (x : ℤ) : ((res l x : ℕ) : ZMod l) = (x : ZMod l) := by
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  rw [← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]

private theorem res_eq {l : ℕ} (hl : 0 < l) {x : ℤ} {j : ℕ} (hj : j < l) (h : (x : ZMod l) = j) : res l x = j := by
  rw [← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)] at h
  exact h

theorem act_sgD_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) =
      X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ ε X N l _ w d hd _ b hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hσ := isDiam_sgD_of_coprime' hl.ne' hd
  have hcl := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2
  have hdet := (sgD N l d).det_coe
  rw [Matrix.det_fin_two] at hdet
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using hl
  have key := fun j k => upper_mul_eq hσ hl j k
  generalize hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key
  generalize hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key
  generalize hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key
  have hae : (A : ZMod l) * E = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  simp only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A))
    (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_
  · intro j hj
    refine res_eq hl (Finset.mem_range.1 hj) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((j : ZMod l) + (B + j * E) * A) * hae
  · intro k hk
    refine res_eq hl (Finset.mem_range.1 hk) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((k : ZMod l) + (k * A - B) * E) * hae
  · intro j _
    obtain ⟨s, hs, hM⟩ := key j (res l ((B + j * E) * E)) (by
      rw [res_cast hl]
      push_cast
      linear_combination ((B : ZMod l) + j * E) * hae)
    rw [Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _),
      X.act_isDiam_eq hb hs]

end GlobalTheory.KZ.DiamU
