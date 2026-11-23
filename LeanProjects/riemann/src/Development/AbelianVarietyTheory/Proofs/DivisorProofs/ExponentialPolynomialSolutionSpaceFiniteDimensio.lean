import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem eq_smul_exp_of_deriv_eq {c : ℂ} {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (h : deriv f = c • f) : f = f 0 • (fun t : ℝ => Complex.exp (c * t)) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * s)) (-c * Complex.exp (-c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c * 1) t :=
      (hasDerivAt_id t).ofReal_comp.const_mul (-c)
    have := h1.cexp
    simpa [mul_comm] using this
  set g : ℝ → ℂ := fun t => Complex.exp (-c * t) * f t with hg
  have hgd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h2 := (hd t).mul (hf t).hasDerivAt
    have e : deriv f t = c * f t := by
      have := congrFun h t; simpa using this
    rw [e] at h2
    have h3 := h2.congr_deriv (show _ = (0:ℂ) by ring)
    exact h3
  have hgdiff : Differentiable ℝ g := fun t => (hgd t).differentiableAt
  have hc := is_const_of_deriv_eq_zero hgdiff (fun t => (hgd t).deriv)
  funext t
  have h0 := hc t 0
  simp only [hg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h0
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h0, mul_comm (Complex.exp _) (f t), mul_assoc, ← Complex.exp_add]
  have e2 : -c * (t : ℂ) + c * t = 0 := by ring
  rw [e2, Complex.exp_zero, mul_one]

theorem expSol_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l)
  | [] => by
      have : expSol [] = ⊥ := rfl
      rw [this]; infer_instance
  | c :: l => by
      haveI := expSol_finiteDimensional l
      let φ : expSol (c :: l) →ₗ[ℂ] expSol l :=
        { toFun := fun f => ⟨deriv (f : ℝ → ℂ) - c • (f : ℝ → ℂ), (mem_expSol_cons.1 f.2).2⟩
          map_add' := fun f g => by
            apply Subtype.ext
            have hf := (mem_expSol_cons.1 f.2).1
            have hg := (mem_expSol_cons.1 g.2).1
            funext x
            simp only [Submodule.coe_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            rw [deriv_add (hf x) (hg x)]; ring
          map_smul' := fun k f => by
            apply Subtype.ext
            have hf := (mem_expSol_cons.1 f.2).1
            funext x
            simp only [Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
              Submodule.coe_smul_of_tower]
            rw [deriv_const_smul k (hf x)]; simp only [smul_eq_mul]; ring }
      have hker : ((LinearMap.ker φ).map (expSol (c :: l)).subtype) ≤
          Submodule.span ℂ {fun t : ℝ => Complex.exp (c * t)} := by
        rintro _ ⟨f, hf, rfl⟩
        have hd := (mem_expSol_cons.1 f.2).1
        have h0 : deriv (f : ℝ → ℂ) - c • (f : ℝ → ℂ) = 0 := by
          have := congrArg Subtype.val (LinearMap.mem_ker.1 hf)
          simpa [φ] using this
        have h1 : deriv (f : ℝ → ℂ) = c • (f : ℝ → ℂ) := sub_eq_zero.1 h0
        rw [Submodule.mem_span_singleton]
        exact ⟨(f : ℝ → ℂ) 0, (eq_smul_exp_of_deriv_eq hd h1).symm⟩
      haveI : FiniteDimensional ℂ ((LinearMap.ker φ).map (expSol (c :: l)).subtype) :=
        Submodule.finiteDimensional_of_le hker
      have hkerFG : (LinearMap.ker φ).FG :=
        Submodule.fg_of_fg_map_injective _ (Submodule.injective_subtype _)
          (Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance)
      have hmapFG : ((⊤ : Submodule ℂ (expSol (c :: l))).map φ).FG :=
        IsNoetherian.noetherian _
      have htop : (⊤ : Submodule ℂ (expSol (c :: l))).FG :=
        Submodule.fg_of_fg_map_of_fg_inf_ker φ hmapFG (by rw [top_inf_eq]; exact hkerFG)
      exact Module.finite_def.2 htop

end GlobalTheory.HCF
