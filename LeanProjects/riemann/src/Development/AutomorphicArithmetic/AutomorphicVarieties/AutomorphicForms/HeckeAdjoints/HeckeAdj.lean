import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.heckeAdj :
    UpperTheory.V.Af.Gk.HeckeAdj := by
  intro F _ _ a w V _ _ ρ H hH x hx ϖ hϖ j
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w a, GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w a := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hf := fun (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion F)) V) => GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 := (H.flip x).toAddMonoidHom.map_finsum (hf ρ)
  have e2 := (H x).toAddMonoidHom.map_finsum (hf (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))))
  refine e1.trans ((finsum_congr fun c => ?_).trans e2.symm)
  generalize c.out = g
  change H (_ • ρ g x) x = H x (_ • ρ (GlobalTheory.CuspRep.invT a _ g) x)
  unfold Formalism.UG.Tj
  by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
      ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
  · rw [Set.indicator_of_mem hg, Pi.one_apply, one_smul, one_smul]
    obtain ⟨k, hk, b, hb, e⟩ := hg
    obtain ⟨d, rfl⟩ : ∃ d, g = k * d * b := ⟨k⁻¹ * g * b⁻¹, by group⟩
    have hd : d.val = Formalism.UG.diagJ a ϖ j := by
      rw [Units.val_mul, Units.val_mul] at e
      exact (Units.mul_right_inj k).1 ((Units.mul_left_inj b).1 e)
    have hd' : GlobalTheory.CuspRep.invT a _ d = d⁻¹ := by
      rw [← inv_eq_iff_eq_inv]
      apply Units.ext
      rw [InvT.invT_inv_val, hd, Formalism.UG.diagJ, Matrix.diagonal_transpose]
    simp only [map_mul, Module.End.mul_apply, hd']
    rw [hfix b hb, hfix _ (hK b hb)]
    have h1 : H (ρ k (ρ d x)) x = H (ρ d x) x := by
      rw [← hH k (ρ d x) x, hfix k hk]
    have h2 : H x (ρ (GlobalTheory.CuspRep.invT a _ k) (ρ d⁻¹ x)) = H x (ρ d⁻¹ x) := by
      rw [← hH (GlobalTheory.CuspRep.invT a _ k) x (ρ d⁻¹ x), hfix _ (hK k hk)]
    rw [h1, h2, ← hH d x (ρ d⁻¹ x), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rw [Set.indicator_of_notMem hg]
    simp
