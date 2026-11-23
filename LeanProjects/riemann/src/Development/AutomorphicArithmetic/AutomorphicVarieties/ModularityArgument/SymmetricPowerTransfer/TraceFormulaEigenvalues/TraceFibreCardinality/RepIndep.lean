import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

section

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V} {s : B.Tw} {f : G → ℂ}

private theorem rep_indep (hf : s.IsTest f) (φ : B.Forms) (h y : G) :
    f (s.θ (y : G ⧸ B.U).out) • s.Θ (φ.1 (h * (y : G ⧸ B.U).out)) = f (s.θ y) • s.Θ (φ.1 (h * y)) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U y
  rw [hu, map_mul, hf.right, ← mul_assoc, φ.2.2, map_smul, smul_smul, mul_right_comm,
    Units.inv_mul, one_mul]

private theorem fin_supp (hf : s.IsTest f) (k : G ⧸ B.U → V) :
    (Function.support fun x : G ⧸ B.U => f (s.θ x.out) • k x).Finite := by
  refine hf.fin.subset fun x hx => ?_
  rw [Function.mem_support] at hx
  rw [Set.mem_setOf_eq]
  intro h0
  exact hx (by rw [h0, zero_smul])

private theorem opF_mem (hf : s.IsTest f) (φ : B.Forms) : s.opF f φ.1 ∈ B.Forms := by
  refine ⟨fun γ g => ?_, fun g u => ?_⟩
  · unfold Base.Tw.opF
    have hθ : s.θ.symm (B.ι γ) = B.ι (s.θΓ.symm γ) := by
      rw [MulEquiv.symm_apply_eq, s.comm, MulEquiv.apply_symm_apply]
    have key : B.W γ (∑ᶠ x : G ⧸ B.U, f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)))
        = ∑ᶠ x : G ⧸ B.U, B.W γ (f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out))) :=
      (B.W γ).toAddMonoidHom.map_finsum (fin_supp hf _)
    rw [key]
    refine finsum_congr fun x => ?_
    rw [map_smul, map_mul, hθ, mul_assoc, φ.2.1, s.int, MulEquiv.apply_symm_apply]
  · unfold Base.Tw.opF
    rw [smul_finsum' _ (fin_supp hf _)]
    let e : Equiv.Perm (G ⧸ B.U) := MulAction.toPerm ((s.θ.symm (u : G))⁻¹)
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun x => ?_
    have hex : e x = (((s.θ.symm (u : G))⁻¹ * x.out : G) : G ⧸ B.U) := by
      show (s.θ.symm (u : G))⁻¹ • x = _
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rw [hex, rep_indep hf φ (s.θ.symm (g * u)) ((s.θ.symm (u : G))⁻¹ * x.out)]
    have hg : s.θ.symm (g * ↑u) * ((s.θ.symm (u : G))⁻¹ * x.out) = s.θ.symm g * x.out := by
      rw [map_mul, mul_assoc, mul_inv_cancel_left]
    have hf1 : f (s.θ ((s.θ.symm (u : G))⁻¹ * x.out)) = (B.ω u : ℂ) * f (s.θ x.out) := by
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
      have hl := hf.left u⁻¹ (s.θ x.out)
      simp only [Subgroup.coe_inv, InvMemClass.coe_inv] at hl
      rw [hl, map_inv, inv_inv]
    rw [hg, hf1, mul_smul]

private def opL (hf : s.IsTest f) : Module.End ℂ B.Forms where
  toFun φ := ⟨s.opF f φ.1, opF_mem hf φ⟩
  map_add' φ ψ := by
    refine Subtype.ext (funext fun g => ?_)
    change s.opF f (φ.1 + ψ.1) g = s.opF f φ.1 g + s.opF f ψ.1 g
    unfold Base.Tw.opF
    rw [← finsum_add_distrib (fin_supp hf _) (fin_supp hf _)]
    refine finsum_congr fun x => ?_
    rw [Pi.add_apply, map_add, smul_add]
  map_smul' c φ := by
    refine Subtype.ext (funext fun g => ?_)
    change s.opF f (c • φ.1) g = c • s.opF f φ.1 g
    unfold Base.Tw.opF
    rw [smul_finsum' _ (fin_supp hf _)]
    refine finsum_congr fun x => ?_
    rw [Pi.smul_apply, map_smul, smul_comm]

end

theorem rSpec : RSpec := by
  intro Γ G V _ _ _ _ B s f hf φ
  have h : ∃ L : Module.End ℂ B.Forms, ∀ φ, (L φ).1 = s.opF f φ.1 := ⟨opL hf, fun _ => rfl⟩
  unfold Base.Tw.R
  rw [dif_pos h]
  exact h.choose_spec φ

end UpperTheory.V.Z.Sym.Tf
