import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.ExistsNeZeroMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL

noncomputable section

namespace PIW.ClassFinD.Icf

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

def IsIntU (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1

theorem latI_ne_bot (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : latI b ≠ ⊥ := by
  obtain ⟨r, hr, hmem⟩ := exists_ne_zero_mem b
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hr hmem

def latticeIdealNonzero (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : nonZeroDivisors (Ideal (𝓞 F)) :=
  ⟨latI b, mem_nonZeroDivisors_of_ne_zero (latI_ne_bot b)⟩

def cls (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : ClassGroup (𝓞 F) := ClassGroup.mk0 (latticeIdealNonzero b)

theorem val_eq_of_cls (b b0 : (FiniteAdeleRing (𝓞 F) F)ˣ) (hb : IsIntU b) (hb0 : IsIntU b0)
    (h : cls b = cls b0) : ∃ x y : 𝓞 F, x ≠ 0 ∧ y ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) =
        v.intValuation y * Valued.v ((b0 : FiniteAdeleRing (𝓞 F) F) v) := by
  unfold cls at h
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨x, y, hx, hy, fun v => le_antisymm ?_ ?_⟩
  · exact val_le_of_le b b0 hb (le_of_eq hxy) v
  · exact val_le_of_le b0 b hb0 (le_of_eq hxy.symm) v

end PIW.ClassFinD.Icf

namespace PIW.ClassFinD

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Icf

theorem idele_class_finite : IdeleClassFin := by
  intro F _ _
  classical
  let rep : ClassGroup (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ := fun κ =>
    if h : ∃ b : (FiniteAdeleRing (𝓞 F) F)ˣ, IsIntU b ∧ cls b = κ then h.choose else 1
  refine ⟨Finset.univ.image rep, fun a => ?_⟩
  obtain ⟨r, hr, hra⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den (a : FiniteAdeleRing (𝓞 F) F)
  have hrF : algebraMap (𝓞 F) F r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr
  let ur : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) (Units.mk0 _ hrF)
  let b := ur * a
  have hbw : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) =
      w.intValuation r * Valued.v ((a : FiniteAdeleRing (𝓞 F) F) w) := by
    intro w
    rw [Units.val_mul, v_mul]
    congr 1
    exact v_algR r w
  have hb : IsIntU b := by
    intro w
    have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r * (a : FiniteAdeleRing (𝓞 F) F)) w) ≤ 1 :=
      hra w
    rw [v_mul, v_algR] at h1
    rw [hbw w]
    exact h1
  have hex : ∃ b' : (FiniteAdeleRing (𝓞 F) F)ˣ, IsIntU b' ∧ cls b' = cls b := ⟨b, hb, rfl⟩
  have hb0 : IsIntU (rep (cls b)) ∧ cls (rep (cls b)) = cls b := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨x, y, hx, hy, hv⟩ := val_eq_of_cls b (rep (cls b)) hb hb0.1 hb0.2.symm
  have hxF : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hx
  have hyF : algebraMap (𝓞 F) F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hy
  let f : Fˣ := Units.mk0 (algebraMap (𝓞 F) F y / (algebraMap (𝓞 F) F x * algebraMap (𝓞 F) F r))
    (div_ne_zero hyF (mul_ne_zero hxF hrF))
  let uf : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) f
  let e : (FiniteAdeleRing (𝓞 F) F)ˣ := (uf * rep (cls b))⁻¹ * a
  have hE : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((e : FiniteAdeleRing (𝓞 F) F) w) = 1 := by
    intro w
    have hX : w.intValuation x ≠ 0 := by
      rw [← valuation_of_algebraMap (K := F)]; exact (Valuation.ne_zero_iff _).2 hxF
    have hY : w.intValuation y ≠ 0 := by
      rw [← valuation_of_algebraMap (K := F)]; exact (Valuation.ne_zero_iff _).2 hyF
    have hR : w.intValuation r ≠ 0 := by
      rw [← valuation_of_algebraMap (K := F)]; exact (Valuation.ne_zero_iff _).2 hrF
    have hUF : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) =
        w.intValuation y / (w.intValuation x * w.intValuation r) := by
      have : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) =
          w.valuation F (algebraMap (𝓞 F) F y / (algebraMap (𝓞 F) F x * algebraMap (𝓞 F) F r)) :=
        v_algF _ w
      rw [this, map_div₀, map_mul, valuation_of_algebraMap, valuation_of_algebraMap, valuation_of_algebraMap]
    have hV : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) *
        Valued.v (((rep (cls b)) : FiniteAdeleRing (𝓞 F) F) w) = Valued.v ((a : FiniteAdeleRing (𝓞 F) F) w) := by
      rw [hUF, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hX hR), ← hv w, hbw w]
      ac_rfl
    have hV0 : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := v_unit_ne uf w
    have hB0 : Valued.v (((rep (cls b)) : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := v_unit_ne _ w
    rw [Units.val_mul, v_mul, v_inv, Units.val_mul, v_mul, hV, inv_mul_cancel₀ (v_unit_ne a w)]
  refine ⟨f, rep (cls b), Finset.mem_image.2 ⟨cls b, Finset.mem_univ _, rfl⟩, e, ?_, ?_, ?_⟩
  · intro w
    exact (hE w).le
  · intro w
    have : Valued.v (((e⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w) = 1 := by
      rw [v_inv, hE w, inv_one]
    exact this.le
  · exact (mul_inv_cancel_left (uf * rep (cls b)) a).symm

end PIW.ClassFinD

end
