import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem expSol_eq_zero_of_eqOn_Ioo :
    ∀ (l : List ℂ) (f : ℝ → ℂ), f ∈ expSol l → ∀ s t : ℝ, s < t → (∀ x ∈ Set.Ioo s t, f x = 0) → f = 0 := by
  intro l
  induction l with
  | nil => intro f hf _ _ _ _; exact mem_expSol_nil.1 hf
  | cons c l ih =>
    intro f hf s t hst h0
    rw [mem_expSol_cons] at hf
    obtain ⟨hd, hg⟩ := hf
    have hg0 : deriv f - c • f = 0 := by
      refine ih _ hg s t hst (fun x hx => ?_)
      have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => h0 y hy)
      simp [Pi.sub_apply, hev.deriv_eq, h0 x hx]
    have hder : ∀ x, HasDerivAt f (c * f x) x := by
      intro x
      have h1 := congrFun hg0 x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have e : deriv f x = c * f x := sub_eq_zero.1 h1
      rw [← e]; exact (hd x).hasDerivAt
    set k : ℝ → ℂ := fun x => Complex.exp (-c * x) * f x with hk
    have hkd : ∀ x, HasDerivAt k 0 x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      have h2 := ((h1.const_mul (-c)).cexp).mul (hder x)
      have h3 := h2.congr_deriv (show _ = (0 : ℂ) by ring)
      exact h3
    have hkc : ∀ x y, k x = k y := fun x y =>
      is_const_of_deriv_eq_zero (fun z => (hkd z).differentiableAt) (fun z => (hkd z).deriv) x y
    have hm : (s + t) / 2 ∈ Set.Ioo s t := ⟨by linarith, by linarith⟩
    funext x
    have := hkc x ((s + t) / 2)
    simp only [hk, h0 _ hm, mul_zero] at this
    simpa [Complex.exp_ne_zero] using this

end GlobalTheory.HCF
