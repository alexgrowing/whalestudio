import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulFam_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l),
    ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  intro N l _ hl _ γ
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp γ.2
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  rw [CongruenceSubgroup.Gamma0_mem] at hγ0
  obtain ⟨ha1, hd1, hcN⟩ := hγ1
  set a : ℤ := mat γ 0 0 with ha
  set b : ℤ := mat γ 0 1 with hb
  set c : ℤ := mat γ 1 0 with hc
  set d : ℤ := mat γ 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := (γ : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at h
    exact h
  have hmat : mat γ = !![a, b; c, d] := Matrix.eta_fin_two _
  have hcl : (c : ZMod l) = 0 := hγ0
  have hcN' : (c : ZMod N) = 0 := hcN
  have ha1' : (a : ZMod N) = 1 := ha1
  have hd1' : (d : ZMod N) = 1 := hd1
  have had : (d : ZMod l) * a = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  let f : Fin l → Fin l := fun i => ⟨(((b + (i : ℕ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩
  have hf : ∀ i, (((f i : ℕ) : ℤ) : ZMod l) = (((b + (i : ℕ) * d) * d : ℤ) : ZMod l) := by
    intro i
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  have hinj : Function.Injective f := by
    intro i i' h
    have h2 := congrArg (fun x : Fin l => (((x : ℕ) : ℤ) : ZMod l)) h
    simp only [hf] at h2
    push_cast at h2
    have h3 : ((i : ℕ) : ZMod l) = ((i' : ℕ) : ZMod l) := by
      linear_combination (a * a) * h2 - ((i : ℕ) - (i' : ℕ) : ZMod l) * (d * a + 1) * had
    have h4 := congrArg ZMod.val h3
    rw [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt i'.2] at h4
    exact Fin.ext h4
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  set j : ℤ := ((f i : ℕ) : ℤ) with hj
  set x : ℤ := ((i : ℕ) : ℤ) with hx
  have hdvd : (l : ℤ) ∣ b + x * d - j * (a + x * c) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp
    have hj' := hf i
    rw [← hj] at hj'
    have hxc : (x : ZMod l) = ((i : ℕ) : ZMod l) := by rw [hx, Int.cast_natCast]
    push_cast
    rw [hj', hcl, hxc]
    push_cast
    linear_combination (-(b : ZMod l) - x * d) * had + (d : ZMod l) * (d * a - 1) * hxc
  obtain ⟨e, he⟩ := hdvd
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a + x * c, e; l * c, d - j * c]
  have hMdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨M, hMdet⟩
  have hg : g ∈ Lev N l := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · show ((a + x * c : ℤ) : ZMod N) = 1
        push_cast; rw [ha1', hcN']; ring
      · show ((d - j * c : ℤ) : ZMod N) = 1
        push_cast; rw [hd1', hcN']; ring
      · show (((l : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast; rw [hcN']; ring
    · rw [CongruenceSubgroup.Gamma0_mem]
      show (((l : ℤ) * c : ℤ) : ZMod l) = 0
      push_cast; simp
  refine ⟨⟨g, hg⟩, ?_⟩
  show ulFam l i * mat γ = M * ulFam l (f i)
  rw [hmat]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [ulFam, M, Matrix.mul_apply, Fin.sum_univ_two, ← hj, ← hx] <;>
    first | ring1 | linear_combination he

end GlobalTheory.HeckeFamilyMatrices
