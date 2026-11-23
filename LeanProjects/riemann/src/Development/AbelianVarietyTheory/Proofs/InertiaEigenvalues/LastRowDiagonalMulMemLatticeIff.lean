import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.CellDec.RowPos
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_val (v : HeightOneSpectrum (𝓞 E)) (x : GA E n) (i j : Fin n) :
    (compV E n v x).val i j = pLoc E v (pFin E (x.val i j)) := rfl

theorem row_unip_mul {R : Type} [CommRing R] {m : ℕ} {U : GL (Fin (m + 1)) R}
    (hU : U ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (K : GL (Fin (m + 1)) R) (i : Fin (m + 1)) :
    (U * K).val (Fin.last m) i = K.val (Fin.last m) i := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hU
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro j _ hj
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sub_single_apply {m : ℕ} (y : Fin (m + 1) → Af E) (i : Fin (m + 1)) (v : HeightOneSpectrum (𝓞 E)) :
    (((y - Pi.single (Fin.last m) (1 : Af E)) : Fin (m + 1) → Af E) i) v = y i v - if i = Fin.last m then 1 else 0 := by
  change pLoc E v ((y - Pi.single (Fin.last m) (1 : Af E) : Fin (m + 1) → Af E) i) = pLoc E v (y i) - _
  rw [Pi.sub_apply, map_sub]
  congr 1
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]

theorem val_sub_ite_le_one {v : HeightOneSpectrum (𝓞 E)} {x : v.adicCompletion E} (hx : Valued.v x ≤ 1) (p : Prop)
    [Decidable p] : Valued.v (x - if p then 1 else 0) ≤ 1 := by
  refine (Valuation.map_sub _ _ _).trans (max_le hx ?_)
  split_ifs
  · rw [map_one]
  · rw [map_zero]; exact zero_le'

end GlobalTheory.CellDec.RowPos

open GlobalTheory.CellDec GlobalTheory.CellDec.RowPos in

theorem GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  intro E _ _ m T ϖ hϖ J hJ g hg l hl
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hgv : ∀ v i, (pFin E ((u * k).val (Fin.last m) i)) v = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i
    change pLoc E v _ = _
    rw [← compV_val, map_mul, row_unip_mul (compV_mem_unipB v hu)]
  have htv : ∀ v i, (pFin E ((tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) v =
      ((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
        (pFin E ((u * k).val (Fin.last m) i)) v := by
    intro v i
    change pLoc E v _ = _ * pLoc E v _
    rw [← compV_val, ← compV_val, map_mul (compV E (m + 1) v), compV_tl, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul]
  refine forall_congr' fun i => ?_
  rw [GroundTheory.Global.mem_idealFiniteAdeles, GroundTheory.Global.mem_idealFiniteAdeles]
  refine forall_congr' fun v => ?_
  rw [sub_single_apply, sub_single_apply]
  beta_reduce
  rw [htv]
  by_cases hv : v ∈ T
  · rw [l.2 v hv]
    simp
  · rw [hJ v hv]
    have hK := (GlobalTheory.AdelicU.mem_GLint_iff.1 (mem_US.1 hk v hv)).1 (Fin.last m) i
    have hK' : Valued.v ((compV E (m + 1) v k).val (Fin.last m) i) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hK
    have hϖ1 : Valued.v ((ϖ v : v.adicCompletion E)) ≤ 1 := by
      rw [hϖ v]; exact le_of_lt (by decide)
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hl v)
    have hp : Valued.v (((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)) ≤ 1 := by
      rw [ha, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' hϖ1 a
    rw [hgv, neg_zero, WithZero.exp_zero]
    refine ⟨fun _ => val_sub_ite_le_one hK' _, fun _ => val_sub_ite_le_one ?_ _⟩
    rw [map_mul]
    exact mul_le_one' hp hK'
