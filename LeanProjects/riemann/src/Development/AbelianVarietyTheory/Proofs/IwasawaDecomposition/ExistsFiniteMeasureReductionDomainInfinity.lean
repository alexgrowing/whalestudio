import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarInfiniteGLLtTopOfInfiniteGLHaarMeasureLtTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTopStatement

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.GLInfReduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def entries (y : Matrix (Fin a) (Fin a) (Cinf E)) : GlobalTheory.FlagMeas.MatInf E a := fun w i k => y i k w

def dn (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∏ w, ‖(y.det) w‖ ^ 2

theorem detNorm_entries (y : Matrix (Fin a) (Fin a) (Cinf E)) :
    GlobalTheory.FlagMeas.detNorm E a (entries y) = dn y := by
  unfold GlobalTheory.FlagMeas.detNorm dn
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of (entries y w) = (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix y := by
    ext i k; rfl
  rw [this, ← RingHom.map_det]; rfl

theorem entries_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : entries (g * y) = entries g * entries y := by
  funext w i k
  change (g * y) i k w = (Matrix.of (entries g w) * Matrix.of (entries y w)) i k
  simp [Matrix.mul_apply, Finset.sum_apply, entries]

theorem dn_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : dn (g * y) = dn g * dn y := by
  simp [dn, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]

theorem dn_pos (y : GL (Fin a) (Cinf E)) : 0 < dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := by
  refine Finset.prod_pos fun w _ => ?_
  have h : (y : Matrix (Fin a) (Fin a) (Cinf E)).det * ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h' := congrFun h w
  have hne : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 := left_ne_zero_of_mul_eq_one h'
  positivity

end GlobalTheory.GLInfReduction

open GlobalTheory.GLInfReduction in

theorem GlobalTheory.GLInfReduction.exists_cover_of_finite_measure (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)) (hΛ : Submodule.IsLattice E Λ)
    [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure] :
    ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E,
      (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧
      ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨Set.univ, ?_, fun y => ⟨1, by simp, 0, trivial⟩⟩
    haveI : Subsingleton (GL (Fin 0) (Cinf E)) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Finite (GL (Fin 0) (Cinf E)) := Finite.of_subsingleton
    exact isCompact_univ.measure_lt_top
  set r := Fintype.card (InfinitePlace E) with hr_def
  have hr : 0 < r := Fintype.card_pos
  set N : ℕ := 2 * a * r with hN_def
  have hN : 0 < N := by positivity
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'

  have hslab := GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top E inferInstance a ha Λ hΛ
  simp only [GlobalTheory.FlagMeas.covol, iInf_lt_iff] at hslab
  obtain ⟨D, hDm, hcov, hDlt⟩ := hslab
  have hD' := GlobalTheory.T.haar_infiniteGL_lt_top_of_infiniteGLHaarMeasure_lt_top E a ν D hDm hDlt
  set S : Set (GL (Fin a) (Cinf E)) := {y | entries (y : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D} with hS
  have hS' : ν S < ⊤ := hD'

  let c : ℝ → GL (Fin a) (Cinf E) := fun t => GeneralLinearGroup.map (pInf E) (splitCentre E a t)
  have hc_val : ∀ t : ℝ, (c t : Matrix (Fin a) (Fin a) (Cinf E)) =
      Matrix.scalar (Fin a) (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := by
    intro t
    simp only [c, splitCentre, pInf_infGL]
    rfl
  have hc_dn : ∀ t : ℝ, dn (c t : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (N * t) := by
    intro t
    rw [hc_val, dn]
    simp only [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Pi.pow_apply, norm_pow, Complex.norm_exp_ofReal]
    rw [← hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hN_def]
    congr 1; push_cast; ring
  have hcomm : ∀ t g, c t * g = g * c t := by
    intro t g
    have := congrArg (GeneralLinearGroup.map (pInf E)) (splitCentre_comm (E := E) (a := a) t (infGL E a g))
    simpa [map_mul] using this
  have hcint : ∀ n : ℤ, GeneralLinearGroup.map (pInf E) (splitCentre E a 1 ^ n) = c n := by
    intro n; simp only [c, splitCentre_intCast]
  refine ⟨⋃ k ∈ Finset.range N, (fun h => c (-(k : ℝ) / N) * h) ⁻¹' S, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_
    refine ENNReal.sum_lt_top.2 fun k _ => ?_
    rw [measure_preimage_mul]
    exact hS'
  · intro y
    set L := Real.log (dn (y : Matrix (Fin a) (Fin a) (Cinf E)))
    have hL : Real.exp L = dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := Real.exp_log (dn_pos y)
    set m := ⌊L⌋
    set q := m / (N : ℤ)
    set ρ := m % (N : ℤ)
    have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hρN : ρ < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    have hm : ρ + N * q = m := by simp only [ρ, q]; rw [Int.emod_def]; ring
    set k := ρ.toNat
    have hk : (k : ℤ) = ρ := Int.toNat_of_nonneg hρ0
    have hkN : k < N := by omega
    set x := c (-(k : ℝ) / N) * (c ((-q : ℤ) : ℝ) * y)
    have hx : dn (x : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (L - m) := by
      simp only [x, Units.val_mul, dn_mul, hc_dn, ← hL, ← Real.exp_add]
      congr 1
      have hmR : (ρ : ℝ) + N * q = m := by exact_mod_cast hm
      have hkR : (k : ℝ) = ρ := by exact_mod_cast hk
      rw [← hmR, hkR]; push_cast; field_simp; ring
    have hxS : 1 ≤ GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
        GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) < Real.exp 1 := by
      rw [detNorm_entries, hx]
      constructor
      · exact Real.one_le_exp (by linarith [Int.floor_le L])
      · exact Real.exp_lt_exp.2 (by linarith [Int.lt_floor_add_one L])
    obtain ⟨g, ⟨γ, hγΛ, hgγ⟩, hgD⟩ := hcov _ hxS
    refine ⟨γ, hγΛ, -q, ?_⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k, hkN, ?_⟩
    set R := GeneralLinearGroup.map (pInf E) (ratGL E a γ)
    have hR : entries (R : Matrix (Fin a) (Fin a) (Cinf E)) = g := by
      funext w i j
      rw [hgγ w i j]
      exact pInf_algebraMap (γ i j) w
    have e1 : c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) = R * x := by
      rw [map_mul, hcint, ← mul_assoc, ← mul_assoc, hcomm, mul_assoc, mul_assoc]
    change entries ((c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) :
      GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D
    rw [e1, Units.val_mul, entries_mul, hR]
    exact hgD
