import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.CellDec.lastRow_sub_notMem_latt : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  intro E _ _ m T ϖ hϖ J hJ g hg l w hlw hmem
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hwT : w ∉ T := fun h => by rw [l.2 w h] at hlw; simp at hlw
  set a := l.1 w (Fin.last m) with ha
  set K := GlobalTheory.CellDec.compV E (m+1) w k with hKdef
  have hK : K ∈ GlobalTheory.LFun.KGL w (m+1) := GlobalTheory.CellDec.mem_US.1 hk w hwT
  obtain ⟨-, hK2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have hU := (GlobalTheory.SmGL.mem_unipB _).1 (GlobalTheory.CellDec.compV_mem_unipB w hu)
  have hent : ∀ i, (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
      ((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i := by
    intro i
    have h1 : (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
        (GlobalTheory.CellDec.compV E (m+1) w (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k))).val (Fin.last m) i := rfl
    rw [h1, map_mul, map_mul, GlobalTheory.CellDec.compV_tl, Units.val_mul, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hU.2, one_mul]
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hb : ∀ i, Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i -
      (if i = Fin.last m then 1 else 0)) ≤ 1 := by
    intro i
    have h2 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hmem i) w
    rw [hJ w hwT, neg_zero, WithZero.exp_zero] at h2
    convert h2 using 2
    rw [← hent i]
    by_cases hi : i = Fin.last m
    · subst hi; simp
    · simp [hi]
  have hϖv : Valued.v ((ϖ w : w.adicCompletion E)) = WithZero.exp (-1 : ℤ) := hϖ w
  have hrow : ∀ i, Valued.v (K.val (Fin.last m) i) < 1 := by
    intro i
    have hle : Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) ≤ 1 := by
      by_cases hi : i = Fin.last m
      · have := hb i
        rw [if_pos hi] at this
        calc _ = Valued.v ((((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i - 1) + 1) := by
              rw [sub_add_cancel]
          _ ≤ max _ _ := Valuation.map_add _ _ _
          _ ≤ 1 := max_le this (by simp)
      · simpa [hi] using hb i
    have e : K.val (Fin.last m) i = ((ϖ w ^ (-a) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
        (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) := by
      rw [← mul_assoc, ← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
    rw [e, Valuation.map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖv, ← WithZero.exp_zsmul]
    have hlt : WithZero.exp ((-a) • (-1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; simp; omega
    calc _ ≤ WithZero.exp ((-a) • (-1 : ℤ)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  have hone : ∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m) = 1 := by
    have := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) (w.adicCompletion E) => M (Fin.last m) (Fin.last m))
      (Units.mul_inv K)
    simpa [Matrix.mul_apply] using this
  have hlt : Valued.v (∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Valuation.map_mul]
    have hj : Valued.v ((K⁻¹).val j (Fin.last m)) ≤ 1 := hK2 j (Fin.last m)
    calc _ ≤ Valued.v (K.val (Fin.last m) j) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hrow j
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt
