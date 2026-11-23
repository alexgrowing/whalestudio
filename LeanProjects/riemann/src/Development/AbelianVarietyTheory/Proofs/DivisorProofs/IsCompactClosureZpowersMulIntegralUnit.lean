import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.IntCpt

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem entries_le_one (hint : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (g : GLw m w) (x : B.A) (hx : ∀ y ∈ GlobalTheory.TwLat.lat e b g, x * y ∈ GlobalTheory.TwLat.lat e b g) (i j : Fin m) :
    Valued.v (((g⁻¹).val * GlobalTheory.TwLat.mulMat e b x * g.val) i j) ≤ 1 := by
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b x * g.val := ⟨_, rfl⟩
  rw [← hY]
  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b x * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, x * Lv.col e b g.val j = ∑ l, e.symm (Y l j) • Lv.col e b g.val l := by
    intro j
    rw [Lv.mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [Lv.repr_sum_smul_col, Lv.repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hmem : x * Lv.col e b g.val j ∈ GlobalTheory.TwLat.lat e b g := hx _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
  have ho' : ∑ l, algebraMap K.O K.E (o l) • Lv.col e b g.val l = ∑ l, e.symm (Y l j) • Lv.col e b g.val l := by
    rw [← hgcol j, ← ho]
    exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
  have := congrFun (Lv.sum_smul_col_inj e b g _ _ ho') i
  have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
  rw [this, RingEquiv.apply_symm_apply] at hi
  exact hi

theorem isCompact_intGL :
    IsCompact {h : GLw m w | (∀ i j, Valued.v (h.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((h⁻¹).val i j) ≤ 1} := by
  have hO : IsCompact ((w.adicCompletionIntegers E).toSubring : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  have := GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint (n := Fin m) _ hO
  rw [GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at this
  convert this using 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ValuationSubring.mem_toSubring, mem_adicCompletionIntegers]

def unitsIn (R : Subalgebra K.O B.A) : Subgroup B.Aˣ where
  carrier := {u | (u : B.A) ∈ R ∧ ((u⁻¹ : B.Aˣ) : B.A) ∈ R}
  one_mem' := by simp [R.one_mem]
  mul_mem' := by
    intro u v hu hv
    refine ⟨by simpa using R.mul_mem hu.1 hv.1, ?_⟩
    rw [_root_.mul_inv_rev, Units.val_mul]
    exact R.mul_mem hv.2 hu.2
  inv_mem' := by
    intro u hu
    exact ⟨hu.2, by simpa using hu.1⟩

end GlobalTheory.TwLat.IntCpt

namespace GlobalTheory.TwLat

open IsDedekindDomain.HeightOneSpectrum

theorem isCompact_closure_zpowers_mulU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A → IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) := by
  intro E _ _ _ hU w hw K e hc hint hval B m b a ha
  let R : Subalgebra K.O B.A := Algebra.adjoin K.O {(a : B.A), ((a⁻¹ : B.Aˣ) : B.A)}
  haveI : Module.Finite K.O R := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha.1
    · exact ha.2
  let L : Submodule K.O B.A := (Submodule.span R (Set.range b)).restrictScalars K.O
  have hLfg : L.FG := Submodule.FG.restrictScalars (Submodule.fg_span (Set.finite_range b))
  have hbL : ∀ i, b i ∈ L := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hLsp : Submodule.span K.E (L : Set B.A) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hbL i)
  have hLst : ∀ x ∈ R, ∀ y ∈ L, x * y ∈ L := by
    intro x hx y hy
    exact (Submodule.span R (Set.range b)).smul_mem (⟨x, hx⟩ : R) hy
  obtain ⟨g, hg⟩ := GlobalTheory.TwLat.exists_GLw_lat_eq E hU w hw K e hc hint hval B m b L ⟨hLfg, hLsp⟩
  have haH : a ∈ IntCpt.unitsIn R :=
    ⟨Algebra.subset_adjoin (Set.mem_insert _ _), Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩
  let S : Set (GLw m w) := {h | (∀ i j, Valued.v (h.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((h⁻¹).val i j) ≤ 1}
  have hC : IsCompact ((fun h => g * h * g⁻¹) '' S) :=
    (IntCpt.isCompact_intGL (w := w) (m := m)).image (by fun_prop)
  have hsub : (Subgroup.zpowers (mulU e b a) : Set (GLw m w)) ⊆ (fun h => g * h * g⁻¹) '' S := by
    rintro _ ⟨k, rfl⟩
    have hu : a ^ k ∈ IntCpt.unitsIn R := zpow_mem haH k
    refine ⟨g⁻¹ * mulU e b (a ^ k) * g, ⟨?_, ?_⟩, ?_⟩
    · intro i j
      have := IntCpt.entries_le_one e b hint g _ (hg ▸ hLst _ hu.1) i j
      rw [Units.val_mul, Units.val_mul, mulU_val]
      exact this
    · intro i j
      have := IntCpt.entries_le_one e b hint g _ (hg ▸ hLst _ hu.2) i j
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv (mulU e b), ← mul_assoc, Units.val_mul,
        Units.val_mul, mulU_val]
      exact this
    · show g * (g⁻¹ * mulU e b (a ^ k) * g) * g⁻¹ = mulU e b a ^ k
      rw [map_zpow]
      group
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

end GlobalTheory.TwLat
