import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalar

noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem std_ne_one {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) : ψ ≠ 1 := by
  intro h1
  have hn : 0 < Module.finrank ℚ F := Module.finrank_pos
  let m : NumberField.mixedEmbedding.mixedSpace F :=
    algebraMap ℝ (NumberField.mixedEmbedding.mixedSpace F) (1 / (2 * (Module.finrank ℚ F : ℝ)))
  let a : AF F := ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m, 0)
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a := by
    intro u hu
    have hu1 : u.1 = 0 := by
      have h2 : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (h2.trans (map_zero _).symm)
    show u * a = 0
    exact Prod.ext (by show u.1 * _ = 0; rw [hu1, zero_mul]) (by show u.2 * 0 = 0; rw [mul_zero])
  have hψa := h.2.2 a hAt
  rw [h1, AddChar.one_apply] at hψa
  have htr : Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a) = 1 / 2 := by
    show Algebra.trace ℝ _ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)) = 1 / 2
    rw [RingEquiv.apply_symm_apply, Algebra.trace_algebraMap, NumberField.mixedEmbedding.finrank, nsmul_eq_mul]
    have : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [htr] at hψa
  have he : Complex.exp (-(2 * ↑Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ)) = -1 := by
    rw [show -(2 * ↑Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [he] at hψa
  norm_num at hψa

theorem std_norm {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 :=
  (GlobalTheory.T.adelic_character_rational_dual F ψ h.1 (std_ne_one h) h.2.1).1 x

theorem std_ne_zero {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (x : AF F) : ψ x ≠ 0 := by
  intro h0
  have h1 : ψ (x + -x) = ψ x * ψ (-x) := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem thetaUniq_of : ThetaUniq := by
  intro F _ _ κ _ ψ hψ l hl hinv
  exact GlobalTheory.CompanionTheory.ThetaUniq.theta_unique F κ ψ hψ.1 (std_ne_one hψ) hψ.2.1 l hl (fun w Φ hΦ => hinv w.1 w.2 Φ hΦ)

theorem thetaInj_of : ThetaInj := by
  intro F _ _ κ _ ψ hψ Φ hΦ h0
  exact GlobalTheory.CompanionTheory.ThetaInj.theta_inj F κ ψ hψ.1 (std_ne_one hψ) hψ.2.1 Φ hΦ h0

theorem fourier_uniq {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (a : (κ → F) → ℂ) (hs : Summable a)
    (h0 : ∀ t : κ → AF F, ∑' y, a y * ψ ((fun i => algebraMap F (AF F) (y i)) ⬝ᵥ t) = 0) (y₀ : κ → F) : a y₀ = 0 := by
  classical
  let e : (κ → F) → (κ → AF F) → ℂ := fun y t => ψ ((fun i => algebraMap F (AF F) (y i)) ⬝ᵥ t)
  let c : (κ → F) → ℂ := fun y => a (y + y₀)
  have hmul : ∀ y s t, e y (s + t) = e y s * e y t := fun y s t => by
    simp only [e, dotProduct_add, AddChar.map_add_eq_mul]
  have hle : ∀ y t, ‖e y t‖ ≤ 1 := fun y t => (std_norm h _).le
  have h00 : ∀ t, e 0 t = 1 := fun t => by simp [e]
  have hne : ∀ y, y ≠ 0 → ∃ t, e y t ≠ 1 := by
    intro y hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have hi' : y i ≠ 0 := hi
    obtain ⟨s, hs'⟩ : ∃ s, ψ s ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact std_ne_one h (AddChar.ext ψ 1 fun s => by simpa using hc s)
    refine ⟨Pi.single i (algebraMap F (AF F) (y i)⁻¹ * s), ?_⟩
    simp only [e, dotProduct_single]
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
  have hcs : Summable fun y => ‖c y‖ := by
    have hc : Summable c := (Equiv.addRight y₀).summable_iff.mpr hs
    exact summable_norm_iff.mpr hc
  have hF : ∀ t, ∑' y, c y * e y t = 0 := by
    intro t
    have key : ∀ y, c y * e y t = e (-y₀) t * (a (y + y₀) * e (y + y₀) t) := by
      intro y
      have hsplit : e y t = e (-y₀) t * e (y + y₀) t := by
        simp only [e]
        rw [← AddChar.map_add_eq_mul, ← add_dotProduct]
        congr 2
        funext i
        simp [map_add, map_neg]
      rw [hsplit]
      ring
    simp_rw [key]
    rw [tsum_mul_left]
    have hre : ∑' y, a (y + y₀) * e (y + y₀) t = ∑' y, a y * e y t :=
      (Equiv.addRight y₀).tsum_eq (fun y => a y * e y t)
    rw [hre]
    have := h0 t
    simp only [e] at this ⊢
    rw [this, mul_zero]
  have := GlobalTheory.CompanionTheory.ThetaInj.charSeries_coeff_eq_zero e c 0 hmul hle h00 hne hcs hF
  simpa [c] using this

end PositivityTheory.ThKCT
