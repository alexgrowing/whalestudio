import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertRIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SectionQuotientFinite

variable {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')

omit [Fintype T] in

theorem mem_blockFnField_of_mem_chartRingZ (t : T) {b : K'} (hb : b ∈ chartRingZ y (fun _ => t)) :
    b ∈ blockFnField y := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_int_mul_coord_mem : ∃ D : ℤ, D ≠ 0 ∧ ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K' := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := K') (Finset.univ.image fun t => y ⟨(), t⟩)
  refine ⟨D, hD0, fun t => ?_⟩
  have h := hD (y ⟨(), t⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rw [zsmul_eq_mul] at h
  exact h

theorem int_mul_mem_of_mem_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) {D : ℤ}
    (hD : ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K') {m : K'} (hm : m ∈ sectionMod y) :
    (D : K') * m ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' ((D : K') * m) ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' _ hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hmt : m / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
    SectionIndexNormAlt.mem_chartLat_iff.mp hm t hyt
  have h1 : v.valuation K' (m / y ⟨(), t⟩) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp
      (CurveAffineCharts.mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _)) hmt)
  have h2 : v.valuation K' ((D : K') * y ⟨(), t⟩) ≤ 1 := by
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K', algebraMap (𝓞 K') K' r = (D : K') * y ⟨(), t⟩ :=
      ⟨⟨_, hD t⟩, rfl⟩
    rw [← hr]
    exact HeightOneSpectrum.valuation_le_one v r
  have e : (D : K') * m = m / y ⟨(), t⟩ * ((D : K') * y ⟨(), t⟩) := by
    field_simp
  rw [e, map_mul]
  exact mul_le_one' h1 h2

theorem fg_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) : AddGroup.FG (sectionMod y) := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_coord_mem y
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : sectionMod y →+ integralClosure ℤ K' :=
    { toFun := fun m => ⟨(D : K') * m, int_mul_mem_of_mem_sectionMod y hy hD m.2⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun a b => Subtype.ext (mul_add _ _ _) }
  have hinj : Function.Injective f := fun a b h => by
    have h' : (D : K') * a = (D : K') * b := congrArg (fun z : integralClosure ℤ K' => (z : K')) h
    exact Subtype.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD0) h')
  have hfin : Module.Finite ℤ (sectionMod y) := Module.Finite.of_injective f.toIntLinearMap hinj
  exact Module.Finite.iff_addGroup_fg.mp hfin

omit [NumberField K'] in

theorem aeval_ne_zero {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]

theorem exists_nat_mul_mem_span (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {m : K'} (hm : m ∈ sectionMod y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * m ∈ Submodule.span (curveRing y) {aeval y s} := by
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := aeval_ne_zero y hs hsP
  obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
  have hmt : m / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.mem_chartLat_iff.mp hm t ht)
  have hxt : x / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.aeval_div_mem hs t)
  have hq : m / x ∈ blockFnField y := by
    have e : m / x = (m / y ⟨(), t⟩) / (x / y ⟨(), t⟩) := by
      field_simp
    rw [e]
    exact div_mem hmt hxt
  obtain ⟨n, hn, hnq⟩ := CurveAffineCharts.exists_nat_mul_mem_curveRing y hq
  refine ⟨n, hn, Submodule.mem_span_singleton.mpr ⟨⟨_, hnq⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

theorem isTorsion (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) (q : sectionQuot y (aeval y s)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • q = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hy hs hsP m.2
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end SectionQuotientFinite

open SectionQuotientFinite in

theorem SectionQuotFinite.closed : SectionQuotFinite.Statement := by
  intro T _ K' _ _ y s hy hs hsP
  have hfg : AddGroup.FG (sectionQuot y (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := fg_sectionMod y hy)
  let _ : Module ℤ (sectionQuot y (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (sectionQuot y (aeval y s)) := Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨n, hn, hnq⟩ := isTorsion y hy hs hsP q
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • q = 0
  rw [natCast_zsmul]
  exact hnq

theorem SectionQuotFinite.proof (_hC : CurveCharts.Statement) : SectionQuotFinite.Statement :=
  SectionQuotFinite.closed

end

end GroundTheory.Heights₂.Heights
