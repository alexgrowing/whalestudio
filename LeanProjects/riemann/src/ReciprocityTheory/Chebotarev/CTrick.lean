import ReciprocityTheory.Chebotarev.Ucoord
import ReciprocityTheory.Chebotarev.ChebyshevLambdaSubPsiBounded

open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

noncomputable def mulDvdEquiv (c : NZIdeal E) : NZIdeal E ≃ {a : NZIdeal E // c.1 ∣ a.1} :=
  Equiv.ofBijective (fun b => ⟨⟨c.1 * b.1, mul_ne_zero c.2 b.2⟩, dvd_mul_right _ _⟩) (by
    constructor
    · intro b b' h
      have h1 : c.1 * b.1 = c.1 * b'.1 := congrArg (fun x => x.1.1) h
      exact Subtype.ext (mul_left_cancel₀ c.2 h1)
    · rintro ⟨a, ⟨b, hb⟩⟩
      have hb0 : b ≠ ⊥ := by
        rintro rfl
        exact a.2 (by rw [hb]; simp)
      exact ⟨⟨b, hb0⟩, Subtype.ext (Subtype.ext hb.symm)⟩)

theorem mulDvdEquiv_apply (c b : NZIdeal E) : (mulDvdEquiv c b).1.1 = c.1 * b.1 := rfl

theorem tsum_dvd_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a : NZIdeal E, (if c.1 ∣ a.1 then
        χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) else 0) =
      χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)) * Lser E χ s := by
  set g : NZIdeal E → ℂ := fun a =>
    χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) with hg
  have h1 : (∑' a : NZIdeal E, (if c.1 ∣ a.1 then g a else 0)) =
      ∑' a : {a : NZIdeal E // c.1 ∣ a.1}, g a.1 := by
    rw [show (∑' a : {a : NZIdeal E // c.1 ∣ a.1}, g a.1) =
      ∑' a : ({a : NZIdeal E | c.1 ∣ a.1} : Set (NZIdeal E)), g a.1 from rfl, tsum_subtype]
    exact tsum_congr (fun a => by simp [Set.indicator_apply])
  rw [h1, ← (mulDvdEquiv c).tsum_eq, Lser, ← tsum_mul_left]
  refine tsum_congr (fun b => ?_)
  simp only [hg]
  rw [mulDvdEquiv_apply]
  simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem tsum_eq_sum_cls (F : NZIdeal E → ℂ) (hF : Summable F) :
    ∑' a : NZIdeal E, F a = ∑ C : ClassGroup (𝓞 E), ∑' a : NZIdeal E, (if cls a = C then F a else 0) := by
  rw [← Summable.tsum_finsetSum (fun C _ => ?_)]
  · refine tsum_congr (fun a => ?_)
    rw [Finset.sum_ite_eq]
    simp
  · have := hF.indicator {a | cls a = C}
    refine this.congr (fun a => ?_)
    simp [Set.indicator_apply]

theorem exists_cls_eq (C : ClassGroup (𝓞 E)) : ∃ b : NZIdeal E, cls b = C := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
  exact ⟨⟨I.1, nonZeroDivisors.ne_zero I.2⟩, hI⟩

end ReciprocityTheory.Cheb
