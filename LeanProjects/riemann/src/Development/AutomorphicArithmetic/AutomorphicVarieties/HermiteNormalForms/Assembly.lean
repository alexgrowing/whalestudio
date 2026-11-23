import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Orbnum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TupExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsBoundOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumT

open NumberField Matrix UpperTheory.V

namespace UpperTheory.V.KT

theorem sx_exact (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (Sx L N) (Sx.face L N) m := by
  obtain ⟨h1, h2, h3⟩ := ConeExtensionAcyclic.acyc_simp (good L N)
  exact KH.tupExact _ _ h1 (by rw [h2]; exact Set.univ_nonempty) h3 m

theorem orbBound_mono (L : Type) [Field L] [NumberField L] (N : ℕ) {p p' : ℕ} (h : p ≤ p') :
    orbBound L N p ≤ orbBound L N p' := by
  unfold orbBound
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ?_)
  exact Nat.mul_le_mul_left _ (by omega)

theorem tors_le (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N m : ℕ) :
    KH.TorsLe (K.HGL L N m) (KH.bound m (orbBound L N m) (3 ^ (dd L N * N)) (m + 2)) :=
  KH.mainFace (Gm L N) (Sx L N) (Sx.face L N) Sx.face_smul m _ _ (Nat.one_le_pow _ _ (by norm_num))
    (sx_exact L N m)
    (fun p hp => ⟨(orb L N p).1, (orb L N p).2.trans (orbBound_mono L N hp)⟩)
    (fun p _ => stab L N p)

theorem torsBound : K.TorsBound (2 * 24 + 1) := by
  refine KH.torsBound_of 24 (by norm_num) fun L _ _ hL e he => ?_
  haveI := hL
  refine ⟨_, _, Nat.one_le_pow _ _ (by norm_num), ?_, ?_, tors_le L (4 * e + 4) (2 * e)⟩
  · have h := orbnum L (4 * e + 4) (2 * e) (by omega)
    have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
    have hD : 1 ≤ absD L := Int.natAbs_pos.2 (discr_ne_zero L)
    have hd : 1 ≤ dd L (4 * e + 4) := Nat.mul_pos hn (by omega)
    have hT : 1 ≤ 2 * absD L * dd L (4 * e + 4) := Nat.mul_pos (by omega) hd
    have h2 : orbBound L (4 * e + 4) (2 * e) ≤ (2 * absD L * dd L (4 * e + 4)) ^
        (24 * (2 * e) * dd L (4 * e + 4) ^ 3 * (4 * e + 4)) :=
      h.trans (Nat.pow_le_pow_right hT (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))))
    have hT' : (0 : ℝ) < ((2 * absD L * dd L (4 * e + 4) : ℕ) : ℝ) := by exact_mod_cast hT
    refine (Nat.cast_le.2 h2).trans (le_of_eq ?_)
    rw [Nat.cast_pow, ← Real.exp_log hT', ← Real.exp_nat_mul]
    unfold K.tBound
    congr 1
    simp only [dd, absD]
    push_cast
    ring
  · have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
    have h3 : (3 : ℝ) ≤ Real.exp 24 := by have := Real.add_one_le_exp (24 : ℝ); linarith
    have h1 : dd L (4 * e + 4) * (4 * e + 4) ≤ dd L (4 * e + 4) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hn)
    calc ((3 ^ (dd L (4 * e + 4) * (4 * e + 4)) : ℕ) : ℝ)
        ≤ ((3 ^ (dd L (4 * e + 4) ^ 2) : ℕ) : ℝ) :=
          Nat.cast_le.2 (Nat.pow_le_pow_right (by norm_num) h1)
      _ ≤ Real.exp 24 ^ (dd L (4 * e + 4) ^ 2) := by
          rw [Nat.cast_pow]; exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast h3) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; simp only [dd]; push_cast; ring

theorem torsBoundPow : ∃ C : ℝ, K.TorsBoundPow C := by
  obtain ⟨C, hC⟩ := K.numT (2 * 24 + 1)
  refine ⟨C, fun L _ _ hL e he => ?_⟩
  obtain ⟨h1, h2⟩ := torsBound L hL e he
  exact ⟨h1, h2.trans (hC e _ _ he Module.finrank_pos (Int.natAbs_pos.2 (discr_ne_zero L)))⟩

end UpperTheory.V.KT
