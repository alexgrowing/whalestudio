import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBirationalRatioClosure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef

noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

theorem pointIdeal_rat {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] (y : (Σ b, ι b) → Ω) :
    pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have hcomp : ∀ F : MRing ι, pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
    intro F
    simp only [pointConeMap, mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have key : ∀ G : MvPolynomial (Σ b, ι b) ℚ, ∃ n : ℕ, 0 < n ∧ ∃ F : MRing ι,
      MvPolynomial.map (Int.castRingHom ℚ) F = (n : MvPolynomial (Σ b, ι b) ℚ) * G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a =>
      refine ⟨a.den, a.pos, C a.num, ?_⟩
      rw [map_C, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul, Rat.den_mul_eq_num]
      rfl
    | add p q hp hq =>
      obtain ⟨n, hn, F, hF⟩ := hp
      obtain ⟨n', hn', F', hF'⟩ := hq
      refine ⟨n * n', Nat.mul_pos hn hn', C (n' : ℤ) * F + C (n : ℤ) * F', ?_⟩
      rw [map_add, map_mul, map_mul, hF, hF', map_C, map_C]
      simp only [eq_intCast, Int.cast_natCast, map_natCast, Nat.cast_mul]
      ring
    | mul_X p j hp =>
      obtain ⟨n, hn, F, hF⟩ := hp
      exact ⟨n, hn, F * X j, by rw [map_mul, map_X, hF, mul_assoc]⟩
  apply le_antisymm
  · intro G hG
    obtain ⟨n, hn, F, hF⟩ := key G
    have hG0 : pointConeMap ℚ y G = 0 := hG
    have hFker : F ∈ mCoordIdeal y := by
      show mConeMap y F = 0
      rw [← hcomp, hF, map_mul, hG0, mul_zero]
    have hGeq : G = C ((n : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hn.ne'), C_1, one_mul]
    rw [hGeq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFker)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    show pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = 0
    rw [hcomp]
    exact hF

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem pointIdeal_map {R Ω₂ Ω : Type} [CommRing R] [Field Ω₂] [Field Ω] [Algebra R Ω₂] [Algebra R Ω] (i : Ω₂ →ₐ[R] Ω)
    (y : (Σ b, ι b) → Ω₂) : pointIdeal R (fun x => i (y x)) = pointIdeal R y := by
  have h : (MvPolynomial.mapAlgHom i).comp (pointConeMap R y) = pointConeMap R (fun x => i (y x)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap]
  ext F
  change pointConeMap R (fun x => i (y x)) F = 0 ↔ pointConeMap R y F = 0
  rw [← h, AlgHom.comp_apply]
  constructor
  · intro h0
    apply MvPolynomial.map_injective (i : Ω₂ →+* Ω) i.toRingHom.injective
    rw [map_zero]
    exact h0
  · intro h0
    rw [h0, map_zero]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (b : K) :
    ∃ j, y ⟨b, j⟩ ≠ 0 := by
  obtain ⟨j, hj⟩ := h.2.1.2.2 b
  refine ⟨j, fun h0 => hj ?_⟩
  show mConeMap y (X ⟨b, j⟩) = 0
  simp [mConeMap, h0]

theorem range_le_fnField {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] (i : Ω₂ →+* Ω) {y : (Σ b, ι b) → Ω₂} (hb : Birational y)
    (hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0) (k : Type) [Field k] [Algebra k Ω] :
    i.fieldRange ≤ (fnField k fun x => i (y x)).toSubfield := by
  choose c hc using hy
  have htop := BirationalRatioClosure.full K ι Ω₂ y c hb hc
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) := htop ▸ Subfield.mem_top s
  have hle : Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) ≤
      (fnField k fun x => i (y x)).toSubfield.comap i := by
    rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    show i (y p / y ⟨p.1, c p.1⟩) ∈ (fnField k fun x => i (y x)).toSubfield
    rw [map_div₀]
    exact IntermediateField.subset_adjoin k _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  exact hle hs

private theorem finiteDimensional_of_subfield_le {Ω : Type} [Field Ω] (S T : Subfield Ω) (h : S ≤ T) [FiniteDimensional S Ω] :
    FiniteDimensional T Ω := by
  letI : Algebra S T := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower S T Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite S T Ω

private theorem trdeg_eq_of_finrank_fieldRange_pos {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] [Algebra ℚ Ω₂] [Algebra ℚ Ω] (i : Ω₂ →+* Ω)
    (d : ℕ) (hZ : Algebra.trdeg ℤ Ω₂ = d) (hfin : 0 < Module.finrank i.fieldRange Ω) :
    Algebra.trdeg ℚ Ω = d := by
  have hQ : Algebra.trdeg ℚ Ω₂ = d := by
    haveI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h := _root_.trdeg_add_eq ℤ ℚ (A := Ω₂)
    rw [_root_.trdeg_eq_zero, zero_add, hZ] at h
    exact h
  letI : Algebra Ω₂ Ω := i.toAlgebra
  haveI : IsScalarTower ℚ Ω₂ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : Algebra Ω₂ i.fieldRange := i.rangeRestrictField.toAlgebra
  haveI : IsScalarTower Ω₂ i.fieldRange Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  haveI : Module.Finite Ω₂ i.fieldRange := by
    refine Module.Finite.of_surjective (Algebra.linearMap Ω₂ i.fieldRange) ?_
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := RingHom.mem_fieldRange.1 hz
    exact ⟨x, Subtype.ext rfl⟩
  haveI : Module.Finite Ω₂ Ω := Module.Finite.trans i.fieldRange Ω
  have h := _root_.trdeg_add_eq ℚ Ω₂ (A := Ω)
  rw [_root_.trdeg_eq_zero (R := Ω₂) (A := Ω), add_zero, hQ] at h
  exact h.symm

theorem numMap : NumMap := by
  intro Ω₂ _ _ Ω _ _ i K _ ι _ y d hb har hfin
  have hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0 := ne_of_arith har
  have hiy : ∀ b, ∃ j, i (y ⟨b, j⟩) ≠ 0 := fun b => by
    obtain ⟨j, hj⟩ := hy b
    exact ⟨j, (map_ne_zero i).2 hj⟩
  haveI : FiniteDimensional i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  have hFD : ∀ (k : Type) [Field k] [Algebra k Ω], FiniteDimensional (fnField k fun x => i (y x)) Ω := by
    intro k _ _
    haveI := finiteDimensional_of_subfield_le i.fieldRange _ (range_le_fnField i hb hy k)
    exact this
  have heq : (fnField ℚ fun x => i (y x)).toSubfield = i.fieldRange := by
    refine le_antisymm ?_ (range_le_fnField i hb hy ℚ)
    rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨p, p', _, rfl⟩)
    · exact RingHom.mem_fieldRange.2 ⟨algebraMap ℚ Ω₂ q, by simp⟩
    · exact RingHom.mem_fieldRange.2 ⟨y p / y p', by rw [map_div₀]⟩
  have hrank : Module.finrank (fnField ℚ fun x => i (y x)) Ω = Module.finrank i.fieldRange Ω := by
    rw [show Module.finrank (fnField ℚ fun x => i (y x)) Ω =
      Module.finrank (fnField ℚ fun x => i (y x)).toSubfield Ω from rfl, heq]
  have hpi : pointIdeal ℚ (fun x => i (y x)) = pointIdeal ℚ y := pointIdeal_map i.toRatAlgHom y
  refine ⟨⟨hiy, hFD ℚ, trdeg_eq_of_finrank_fieldRange_pos i d (FnFieldTrdeg.full K ι Ω₂ y d hb har) hfin⟩, hFD, fun a => ?_, fun a => ?_⟩
  · simp only [num, inum]
    rw [hrank, hpi]
  · simp only [inum, GroundTheory.Heights₂.Heights.HilbertSamuel.genDeg]
    rw [pointIdeal_rat]

end SheetDecomposition
