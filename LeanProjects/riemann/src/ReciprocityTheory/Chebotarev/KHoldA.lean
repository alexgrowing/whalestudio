import ReciprocityTheory.Chebotarev.NormGsEmbZLe
import ReciprocityTheory.Chebotarev.RpowNegFinrankSubOne
import ReciprocityTheory.Chebotarev.IdealLat
import ReciprocityTheory.Chebotarev.MeanZero
import ReciprocityTheory.Chebotarev.LatSum

open NumberField NumberField.mixedEmbedding NumberField.Units Set

open scoped Classical

namespace ReciprocityTheory.Cheb

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def gfun {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) (s : ℝ) (a : NZIdeal E) : ℂ :=
  χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) *
    ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))

theorem exists_F {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2,
      F s = ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  obtain ⟨hle, reps, hmem, hcover, huniq, hper, hmean⟩ := exists_reps_meanZero χ b c hcop
  obtain ⟨R₀, C, hRC⟩ := gs_diff_bound (E := E) χ (∑ β ∈ reps, ‖β‖)
  have hr : -(Module.finrank ℚ E : ℝ) - 1 < -(Module.finrank ℤ (latOf b.1) : ℝ) := by
    rw [finrank_latOf b.2]; linarith
  have hd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ latOf (mbc l b.1 c.1), R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + β) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by
    intro s hs β hβ x _ hR
    exact hRC s hs x β (Finset.single_le_sum (f := fun β => ‖β‖) (fun _ _ => norm_nonneg _) hβ) hR
  have hbd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ latOf b.1, ‖Gs χ s x‖ ≤ 1 := by
    intro s hs x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact norm_gs_embZ_le χ hs.1 α
  have hsm : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : latOf b.1 => Gs χ s (α : mixedSpace E) := fun s hs =>
    summable_gs χ (latOf b.1) (finrank_latOf b.2) hs.1
  have hct : ∀ x ∈ latOf b.1, ContinuousOn (fun s => Gs χ s x) (Icc 1 2) := fun x _ =>
    (continuous_gs χ x).continuousOn
  obtain ⟨F, hF, hFeq⟩ := exists_continuousOn_latticeSum (latOf b.1) (latOf (mbc l b.1 c.1)) hle reps
    hmem hcover huniq (cfun χ b.1 c.1) hper hmean (fun s => Gs χ s) _ hr ⟨R₀, C, hd⟩ 1 hbd hsm hct
  refine ⟨F, hF, fun s hs => ?_⟩
  rw [hFeq s hs]
  exact tsum_latOf b.1 (fun x => cfun χ b.1 c.1 x * Gs χ s x)

def Hfun {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (I : Ideal (𝓞 E)) : ℂ :=
  ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * (χ (((Ideal.absNorm I / Ideal.absNorm b.1 : ℕ)) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if b.1 * c.1 ∣ I then 1 else 0)) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)))

theorem natCast_cpow_mul_cpow_neg {n : ℕ} (hn : n ≠ 0) (s : ℂ) : (n : ℂ) ^ s * (n : ℂ) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hn (by exact_mod_cast h.1)

theorem Hfun_mul {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (a : NZIdeal E) :
    Hfun χ b c s (a.1 * b.1) = gfun χ c s a := by
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hdvd : (b.1 * c.1 ∣ a.1 * b.1) ↔ c.1 ∣ a.1 := by
    rw [mul_comm a.1]; exact mul_dvd_mul_iff_left b.2
  simp only [Hfun, gfun, map_mul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb), hdvd, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  have := natCast_cpow_mul_cpow_neg hb (s : ℂ)
  linear_combination (χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) * this

theorem uphi_Hfun_span {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (α : b.1) :
    ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * Hfun χ b c s (Ideal.span {(α : 𝓞 E)}) =
      ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        (cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E))) := by
  obtain ⟨q, hq⟩ := absNorm_dvd_algebraNorm α.2
  have hbc : (b.1 * c.1 ∣ Ideal.span {(α : 𝓞 E)}) ↔ (α : 𝓞 E) ∈ b.1 * c.1 := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hsg := rsgn_mul_norm (α : 𝓞 E)
  have hchi : χ ((((Ideal.absNorm (Ideal.span {(α : 𝓞 E)})) / Ideal.absNorm b.1 : ℕ)) : ZMod l) =
      χ ((Algebra.norm ℤ (α : 𝓞 E) / (Ideal.absNorm b.1 : ℤ) : ℤ) : ZMod l) * χ (rsgn (embZ (α : 𝓞 E)) : ZMod l) := by
    rw [← map_mul, ← Int.cast_mul, ← Int.cast_natCast, Ideal.absNorm_span_singleton, Int.natCast_div,
      Int.natCast_natAbs, ← hsg, Int.mul_ediv_assoc _ (absNorm_dvd_algebraNorm α.2), mul_comm]
  have hn : ((mixedEmbedding.norm (embZ (α : 𝓞 E)) : ℝ) : ℂ) =
      ((Ideal.absNorm (Ideal.span {(α : 𝓞 E)}) : ℕ) : ℂ) := by
    rw [norm_embZ, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    rw [← Int.cast_abs, Complex.ofReal_intCast]
  simp only [Hfun, cfun, Gs, preZ_embZ, hbc, hchi, hn]
  ring

theorem class_sum_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ)
    (hg : Summable (gfun χ c s)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  have h := tsum_class_eq_latSum b (Hfun χ b c s) (by simpa only [Hfun_mul] using hg)
  simp only [Hfun_mul] at h
  rw [h]
  simp_rw [uphi_Hfun_span]
  rw [tsum_mul_left, mul_assoc]

theorem exists_class_cont {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, Summable (gfun χ c s) →
      ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
        ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * F s := by
  obtain ⟨F, hF, hFeq⟩ := exists_F χ b c hcop
  exact ⟨F, hF, fun s hs hg => by rw [class_sum_eq χ b c s hg, hFeq s hs]⟩

end

end ReciprocityTheory.Cheb
