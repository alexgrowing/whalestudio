import ReciprocityTheory.Chebotarev.UnitPart
import ReciprocityTheory.Chebotarev.DiscreteTopologyLatOf

open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem nzIdeal_ne_zero (a : NZIdeal E) : a.1 ≠ 0 := by
  intro h; exact a.2 (by rw [h]; rfl)

theorem cls_mul_eq_one_iff (a b : NZIdeal E) :
    cls a * cls b = 1 ↔ Submodule.IsPrincipal (a.1 * b.1) := by
  have hab : a.1 * b.1 ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (nzIdeal_ne_zero a) (nzIdeal_ne_zero b))
  rw [← ClassGroup.mk0_eq_one_iff hab]
  unfold cls
  rw [← map_mul]
  rfl

theorem norm_embZ_ne_zero {g : 𝓞 E} (hg : g ≠ 0) : mixedEmbedding.norm (embZ g) ≠ 0 := by
  rw [norm_embZ]
  have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
  exact abs_ne_zero.2 (Int.cast_ne_zero.2 this)

theorem uphi_embZ_zero : uphi (embZ (0 : 𝓞 E)) = 0 := by
  apply uphi_of_norm_eq_zero
  rw [norm_embZ]; simp

theorem tsum_class_eq_latSum (b : NZIdeal E) (H : Ideal (𝓞 E) → ℂ)
    (hH : Summable fun a : NZIdeal E => H (a.1 * b.1)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then H (a.1 * b.1) else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ *
        ∑' α : b.1, ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)}) := by
  set S : Set (NZIdeal E) := {a | cls a * cls b = 1} with hS
  have hP : ∀ a : S, ∃ g : 𝓞 E, Ideal.span {g} = a.1.1 * b.1 := by
    intro a
    rcases ((cls_mul_eq_one_iff a.1 b).1 a.2) with ⟨g, hg⟩
    exact ⟨g, hg.symm⟩
  choose gen hgen using hP
  have gen_mem : ∀ a, gen a ∈ b.1 := fun a => by
    rw [← Ideal.span_singleton_le_iff_mem, hgen]; exact Ideal.mul_le_inf.trans inf_le_right
  have gen_ne : ∀ a, gen a ≠ 0 := fun a h => by
    have := hgen a
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (nzIdeal_ne_zero a.1) (nzIdeal_ne_zero b) (by rw [← this]; rfl)
  have hb0 : b.1 ≠ 0 := nzIdeal_ne_zero b
  let Ψ : S × (𝓞 E)ˣ → b.1 := fun p => ⟨(p.2 : 𝓞 E) * gen p.1, b.1.mul_mem_left _ (gen_mem p.1)⟩
  have hspan : ∀ p : S × (𝓞 E)ˣ, Ideal.span {((Ψ p : b.1) : 𝓞 E)} = p.1.1.1 * b.1 := fun p => by
    show Ideal.span {(p.2 : 𝓞 E) * gen p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.isUnit, hgen]
  have hinj : Function.Injective Ψ := by
    rintro ⟨a, u⟩ ⟨a', u'⟩ h
    have h1 : a.1.1 * b.1 = a'.1.1 * b.1 := by
      rw [← hspan (a, u), ← hspan (a', u'), h]
    have h2 : a = a' := Subtype.ext (Subtype.ext (mul_right_cancel₀ hb0 h1))
    subst h2
    have h3 : (u : 𝓞 E) * gen a = u' * gen a := congrArg Subtype.val h
    rw [Units.ext (mul_right_cancel₀ (gen_ne a) h3)]
  let F : b.1 → ℂ := fun α => ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)})
  have hsupp : Function.support F ⊆ Set.range Ψ := by
    intro α hα
    have hα0 : (α : 𝓞 E) ≠ 0 := by
      intro h0; apply hα; simp only [F, h0, uphi_embZ_zero]; simp
    have hle : Ideal.span {(α : 𝓞 E)} ≤ b.1 := (Ideal.span_singleton_le_iff_mem _).2 α.2
    obtain ⟨c, hc⟩ := Ideal.dvd_iff_le.2 hle
    have hcne : c ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hc
      exact hα0 hc
    have hcS : (⟨c, hcne⟩ : NZIdeal E) ∈ S := by
      show cls _ * cls b = 1
      rw [cls_mul_eq_one_iff]
      exact ⟨⟨α, by rw [mul_comm, ← hc]⟩⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1
      ((hgen ⟨_, hcS⟩).trans (by rw [mul_comm, ← hc]) : Ideal.span {gen ⟨_, hcS⟩} = Ideal.span {(α : 𝓞 E)})
    refine ⟨(⟨_, hcS⟩, u), Subtype.ext ?_⟩
    show (u : 𝓞 E) * gen _ = α
    rw [mul_comm]; exact hu
  rw [← hinj.tsum_eq hsupp]
  let f : S × (𝓞 E)ˣ → ℂ := fun p => ((uphi (p.2 • embZ (gen p.1)) : ℝ) : ℂ) * H (p.1.1.1 * b.1)
  have hFf : ∀ p, F (Ψ p) = f p := fun p => by
    simp only [F, f]
    rw [hspan p]
    show ((uphi (embZ ((p.2 : 𝓞 E) * gen p.1)) : ℝ) : ℂ) * _ = _
    rw [unit_smul_embZ]
  simp only [hFf]
  have hw : ∀ a : S, HasSum (fun u : (𝓞 E)ˣ => uphi (u • embZ (gen a))) (torsionOrder E : ℝ) :=
    fun a => hasSum_uphi_unit_smul _ (norm_embZ_ne_zero (gen_ne a))
  have hfib : ∀ a : S, HasSum (fun u => f (a, u)) (((torsionOrder E : ℕ) : ℂ) * H (a.1.1 * b.1)) := by
    intro a
    have := (Complex.hasSum_ofReal.2 (hw a)).mul_right (H (a.1.1 * b.1))
    simpa [f] using this
  have hnfib : ∀ a : S, HasSum (fun u => ‖f (a, u)‖) ((torsionOrder E : ℝ) * ‖H (a.1.1 * b.1)‖) := by
    intro a
    have := (hw a).mul_right ‖H (a.1.1 * b.1)‖
    have e : (fun u => ‖f (a, u)‖) = fun i => uphi (i • embZ (gen a)) * ‖H (a.1.1 * b.1)‖ := by
      funext u
      simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (uphi_nonneg _)]
    rw [e]; exact this
  have hHn : Summable fun a : S => (torsionOrder E : ℝ) * ‖H (a.1.1 * b.1)‖ :=
    ((summable_norm_iff.2 hH).subtype S).mul_left _
  have hfs : Summable f := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun a => (hnfib a).summable, ?_⟩
    simpa only [(hnfib _).tsum_eq] using hHn
  have hsum := hfs.hasSum.prod_fiberwise hfib
  rw [← hsum.tsum_eq, tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast torsionOrder_ne_zero E), one_mul,
    tsum_subtype S (fun a => H (a.1 * b.1))]
  congr 1

end ReciprocityTheory.Cheb
