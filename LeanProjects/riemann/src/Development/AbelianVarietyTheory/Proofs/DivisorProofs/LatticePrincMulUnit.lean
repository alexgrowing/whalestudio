import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.ClassInv

theorem finPart_unit {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hχ : IsValChar φ s κ 𝔣 Q χ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits (condQ 𝔣 Q)) : finPart χ u = 1 := by
  refine OrderUnits.finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hu
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

theorem lamInf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (α : Eˣ) :
    lamInf φ (2 * s) κ α =
      ((χ.inf α : ℂˣ) : ℂ) * (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) := by
  have hN : (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) = ∏ i, (φ i α * starRingEnd ℂ (φ i α)) ^ s := by
    rw [← TermUnit.prod_norm_sq hφ (α : E), ← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
  rw [hN, (hasInfRatio_iff χ φ _).1 h α]
  unfold lamInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : φ i α ≠ 0 := by simp
  have h2 : starRingEnd ℂ (φ i α) ≠ 0 := by simp
  have h3 : ((κ i : ℤ) + s) = ((κ i + s : ℕ) : ℤ) := by push_cast; ring
  rw [h3, zpow_natCast, div_pow, inv_pow]
  field_simp
  ring

theorem lattice_princ_mul_unit {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} (y : (Af E)ˣ) (α : Eˣ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom α * y * u) = (fun x => (α : E) * x) '' lattice c y := by
  rw [lattice_mul_unit _ hu]
  ext x
  constructor
  · intro hx
    refine ⟨(α : E)⁻¹ * x, (mul_mem_lattice_princ c y α _).1 ?_, by simp⟩
    simpa using hx
  · rintro ⟨z, hz, rfl⟩
    exact (mul_mem_lattice_princ c y α z).2 hz

theorem classInvariance : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ (s : ℕ) (L : Set E), Homothety φ (2 * s) L) → ∀ s : ℕ, ClassInvariance φ s := by
  intro E _ _ _ I _ _ φ hφ hH s 𝔣 Q κ χ _ _ hχ y y' S S' hq hS hS'
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := lattice_princ_mul_unit (c := condQ 𝔣 Q) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 := (hH s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := finPart_unit hχ hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, lamInf_eq hφ hχ.2.2.1 α]
  unfold lamFin
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInv
