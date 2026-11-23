import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.inertia_d :
    ∀ {φ : Frame} (H : HostAx φ), (∀ x, x ∈ (arith H.toHostRaw).inertia H.d ↔ x = 0 ∨ x = sgc0) ∧
      ((arith H.toHostRaw).frob H.d).1.2 = 1 ∧
      ∀ i : ℕ, ∃! g : E0 × φ.A, g - i • (arith H.toHostRaw).frob H.d ∈ (arith H.toHostRaw).inertia H.d ∧ ¬ InPhi g := by
  intro φ H
  have hS := hostFactsS φ H
  have hI : ∀ x, x ∈ (arith H.toHostRaw).inertia H.d ↔ x = 0 ∨ x = sgc0 := hS.inertia_d
  refine ⟨hI, ?_, ?_⟩
  · have hd := H.toHostRaw.d_prime
    have hm : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
    have hN : H.condN = H.d ^ 1 * (H.QS * H.q) := by
      simp only [HostRaw.condN, pow_one]; ring
    haveI : NeZero H.condN := ⟨by simp only [HostRaw.condN]; exact Nat.mul_ne_zero hm hd.ne_zero⟩
    obtain ⟨-, h2⟩ := parts_of_eq hd hN H.d_not_dvd_QSq hm
    obtain ⟨h1, -⟩ := frobUnit_modEq (N := H.condN) hd
    rw [h2] at h1
    have hart := H.der.ps_d (frobUnit H.condN H.d) h1
    show Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (H.art (frobUnit H.condN H.d)).1.1) = 1
    rw [sgn2_toAdd_eq_ite, hart]
    decide
  · intro i
    set F := (arith H.toHostRaw).frob H.d
    rcases zmod_two_eq_zero_or_eq_one (i • F).1.1 with h | h
    · refine ⟨i • F + sgc0, ⟨?_, ?_⟩, ?_⟩
      · rw [hI]; right; abel
      · simp only [InPhi, sgc0, Prod.fst_add, h]; decide
      · rintro g ⟨hg, hg'⟩
        rw [hI] at hg
        rcases hg with hg | hg
        · exfalso; apply hg'
          have : g = i • F := sub_eq_zero.mp hg
          simp only [InPhi, this, h]
        · exact (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _)
    · refine ⟨i • F, ⟨?_, ?_⟩, ?_⟩
      · rw [hI]; left; simp
      · simp only [InPhi, h]; decide
      · rintro g ⟨hg, hg'⟩
        rw [hI] at hg
        rcases hg with hg | hg
        · exact sub_eq_zero.mp hg
        · exfalso; apply hg'
          have : g = i • F + sgc0 := (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _)
          simp only [InPhi, this, sgc0, Prod.fst_add, h]; decide
