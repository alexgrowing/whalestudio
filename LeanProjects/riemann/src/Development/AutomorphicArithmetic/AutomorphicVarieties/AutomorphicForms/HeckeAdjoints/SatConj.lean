import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HeckeAdj
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.satConj :
    UpperTheory.V.Af.Gk.SatConj := by
  intro F _ _ a w V W _ _ _ _ ρ ρ' H C hdef hH hC B hB
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w a, GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w a := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hB' : GlobalTheory.LFun.HasSatGL w (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))) (B.map (·⁻¹)) :=
    InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun _ _ => rfl) hB
  have key : ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w a), x ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ρ' (C x) (B.map (·⁻¹)) := by
    intro x hx h0
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
    have h1 := hB.2 x hx h0
    have h2 := hB'.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix _ (hK k hk)) h0
    refine ⟨(map_ne_zero_iff C C.injective).2 h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hC, hfix k hk],
      h2.2.2.1, fun ϖ hϖ j hj => ?_⟩
    have e := heckeAdj F a w V ρ H hH x hx ϖ hϖ j
    rw [h1.2.2.2 ϖ hϖ j hj, h2.2.2.2 ϖ hϖ j hj, H.map_smulₛₗ, (H x).map_smul, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul] at e
    have e' := mul_right_cancel₀ (fun h => h0 (hdef x h)) e
    rw [← e', ← C.map_smulₛₗ, ← h1.2.2.2 ϖ hϖ j hj]
    refine ((C.toLinearMap.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x)).trans (finsum_congr fun c => ?_)).symm
    generalize c.out = g
    change C (_ • ρ g x) = _ • ρ' g (C x)
    rw [C.map_smulₛₗ, hC]
    congr 1
    unfold Formalism.UG.Tj
    by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
        ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
    · rw [Set.indicator_of_mem hg, Pi.one_apply, map_one]
    · rw [Set.indicator_of_notMem hg, map_zero]
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx.2.1 hx.1).2.1, (key x hx.2.1 hx.1).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := C.surjective y
    refine key x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => C.injective ?_) ((map_ne_zero_iff C C.injective).1 h0)
    rw [hC, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
