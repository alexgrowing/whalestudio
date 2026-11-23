import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi

noncomputable section
namespace GlobalTheory.CompanionTheory.CharacterBiduality

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indicator_mem_SB {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by
  have hcl : IsClopen (A : Set (Fin n → k)) := ⟨AddSubgroup.isClosed_of_isOpen A hAo, hAo⟩
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩

theorem fourier_sub_translate_eq_zero [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (μ : Measure (Fin n → k)) [μ.IsAddHaarMeasure]
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k)))
    (hAo : IsOpen (A : Set (Fin n → k))) (x : Fin n → k)
    (hx : ∀ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) → ψ (η ⬝ᵥ x) = 1) (y : Fin n → k) :
    ∫ z, ((A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) z -
        (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hc : Continuous fun z : Fin n → k => (ψ (z ⬝ᵥ y) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  have hi1 : Integrable (fun z => g z * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    (hg.1.continuous.mul hc).integrable_of_hasCompactSupport hg.2.mul_right
  have hgx : HasCompactSupport fun z => g (z + x) := hg.2.comp_homeomorph (Homeomorph.addRight x)
  have hi2 : Integrable (fun z => g (z + x) * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    ((hg.1.continuous.comp (continuous_id.add continuous_const)).mul hc).integrable_of_hasCompactSupport
      hgx.mul_right
  have e1 : ∫ z, g (z + x) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ =
      (ψ (-(x ⬝ᵥ y)) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
    have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ ((w - x) ⬝ᵥ y) : ℂ)) x
    simp only [add_sub_cancel_right] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hwx : (w - x) ⬝ᵥ y = w ⬝ᵥ y + -(x ⬝ᵥ y) := by rw [sub_dotProduct, sub_eq_add_neg]
    beta_reduce
    rw [hwx, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, e1]
  by_cases hy : ∀ a ∈ A, ψ (y ⬝ᵥ a) = 1
  · have h1 : ψ (x ⬝ᵥ y) = 1 := by rw [dotProduct_comm]; exact hx y hy
    have h2 : ψ (-(x ⬝ᵥ y)) = 1 := by rw [AddChar.map_neg_eq_inv, h1, inv_one]
    simp [h2]
  · push Not at hy
    obtain ⟨a, haA, hne⟩ := hy
    have h0 : ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
      have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ (w ⬝ᵥ y) : ℂ)) a
      have h3 : ∫ z, g (z + a) * (ψ ((z + a) ⬝ᵥ y) : ℂ) ∂μ =
          (ψ (y ⬝ᵥ a) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        have hga : g (w + a) = g w := by
          by_cases hw : w ∈ A
          · simp [hgdef, Set.indicator, hw, A.add_mem hw haA]
          · have : w + a ∉ A := fun h => hw (by simpa using A.sub_mem h haA)
            simp [hgdef, Set.indicator, hw, this]
        simp only [hga, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm a y]
        ring
      rw [h3] at h
      have h4 : (1 - (ψ (y ⬝ᵥ a) : ℂ)) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
        rw [sub_mul, one_mul, h, sub_self]
      refine (mul_eq_zero.1 h4).resolve_left fun h5 => hne (Circle.ext ?_)
      simpa using (sub_eq_zero.1 h5).symm
    simp [h0]

theorem exists_annihilator_ne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A →
    ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo x hxA
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  haveI := t2Space k
  let μ : Measure (Fin n → k) := Measure.addHaar
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hgx : (fun z => g (z + x)) ∈ SB (Fin n → k) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const),
      hg.2.comp_homeomorph (Homeomorph.addRight x)⟩
  have hf : (fun z => g z - g (z + x)) ∈ SB (Fin n → k) := (SB (Fin n → k)).sub_mem hg hgx
  obtain ⟨s, hs⟩ := fourier_inversion_pi μ hc hf
  have hz : ∀ y : Fin n → k, ∫ z, (g z - g (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 :=
    fourier_sub_translate_eq_zero ψ hψ μ A hAc hAo x hcon
  simp only [hz, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (box (Fin n) r) := fun r => by
    have h1 : (0 : Fin n → k) ∈ box (Fin n) r := fun i _ => by simp [cball]
    have h2 : 0 < μ (box (Fin n) r) := (isOpen_box r).measure_pos μ ⟨0, h1⟩
    exact ENNReal.toReal_pos h2.ne' (isCompact_box r).measure_lt_top.ne
  have hne : ((μ.real (box (Fin n) s) * μ.real (box (Fin n) (c * s⁻¹)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (hpos s) (hpos _)).ne'
  have h0 : g 0 - g (0 + x) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hne
  have hg0 : g 0 = 1 := Set.indicator_of_mem (SetLike.mem_coe.2 A.zero_mem) _
  have hgx0 : g (0 + x) = 0 := by
    rw [zero_add]
    exact Set.indicator_of_notMem (fun h => hxA h) _
  rw [hg0, hgx0] at h0
  simp at h0

end GlobalTheory.CompanionTheory.CharacterBiduality
