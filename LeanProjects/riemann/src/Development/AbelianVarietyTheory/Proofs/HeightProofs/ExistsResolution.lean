import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.SymplHAddRight

open NumberField

namespace GlobalTheory.ExtensionResolution

section General

variable {R K W : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

theorem exists_smul_mem (L : Submodule R W) (hL : Submodule.span K (L : Set W) = ⊤) (v : W) :
    ∃ c : R, c ≠ 0 ∧ c • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set W) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, smul_comm a b x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem b hx) (L.smul_mem a hy)
  | smul k x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap R K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have e : (d * a) • ((algebraMap R K n / algebraMap R K d) • x) = n • (a • x) := by
      rw [← algebraMap_smul K (d * a), ← algebraMap_smul K n, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact L.smul_mem n hx

theorem exists_extension (L : Submodule R W) (hL : Submodule.span K (L : Set W) = ⊤)
    (f : L →ₗ[R] R) : ∃ F : W →ₗ[K] K, ∀ x : L, F x = algebraMap R K (f x) := by
  have hloc : IsLocalizedModule (nonZeroDivisors R) L.subtype := by
    refine ⟨fun s => ?_, fun v => ?_, fun {x y} h => ⟨1, by simpa using h⟩⟩
    · have hs : algebraMap R K s ≠ 0 := by
        simpa using nonZeroDivisors.ne_zero s.2
      rw [Module.End.isUnit_iff]
      constructor
      · intro x y h
        have h' : (algebraMap R K s) • x = (algebraMap R K s) • y := by
          simpa using h
        exact smul_right_injective W hs h'
      · intro y
        refine ⟨(algebraMap R K s)⁻¹ • y, ?_⟩
        change (s : R) • ((algebraMap R K s)⁻¹ • y) = y
        rw [← algebraMap_smul K (s : R), smul_smul, mul_inv_cancel₀ hs, one_smul]
    · obtain ⟨c, hc, hv⟩ := exists_smul_mem L hL v
      exact ⟨⟨⟨_, hv⟩, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩⟩, rfl⟩
  let g : L →ₗ[R] K := (Algebra.linearMap R K).comp f
  let F₀ : W →ₗ[R] K := IsLocalizedModule.lift (nonZeroDivisors R) L.subtype g
    (IsLocalizedModule.map_units (Algebra.linearMap R K))
  refine ⟨F₀.extendScalarsOfIsLocalization (nonZeroDivisors R) K, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors R) L.subtype g
    (IsLocalizedModule.map_units (Algebra.linearMap R K)) x

end General

theorem star_mem_one {E : Type} [Field E] [NumberField E] [StarRing E] (a : 𝓞 E) :
    star (algebraMap (𝓞 E) E a) ∈ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_one]
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 E) E a)) :=
    IsIntegral.map ((starRingEnd E).toIntAlgHom) a.isIntegral_coe
  exact ⟨⟨_, hi⟩, rfl⟩

end GlobalTheory.ExtensionResolution
