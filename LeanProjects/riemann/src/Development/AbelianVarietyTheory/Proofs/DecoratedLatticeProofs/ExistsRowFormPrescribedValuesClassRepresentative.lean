import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PerIn

theorem exists_Mt_of_rep_values : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  intro E K ι _ _ _ _ _ _ _ R I Q emb σ _hH w hw hinv
  classical
  let φ : ∀ b, Q.S'.G b → Pol ℂ ι (R.N R.m - 1) → Pol ℂ ι (R.N R.m - 1) := fun b g x =>
    (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam b g)) x
  have φmul : ∀ b (g h : Q.S'.G b) x, φ b (g * h) x = φ b g (φ b h x) := by
    intro b g h x
    simp only [φ, map_mul, Units.val_mul, mul_inv, Module.End.mul_apply, map_smul, smul_smul]
  have hinv' : ∀ c (s : Q.S'.G c.1), s • Q.S'.rep c = Q.S'.rep c → w c = φ c.1 s (w c) :=
    fun c s hs => hinv c ⟨s, hs⟩
  let F : ∀ b, Q.S'.D b → Pol ℂ ι (R.N R.m - 1) := fun b d => φ b (Q.S'.mv b d) (w (Q.S'.cl b d))
  have hcl : ∀ b (g : Q.S'.G b) (d : Q.S'.D b), Q.S'.cl b (g • d) = Q.S'.cl b d := fun b g d =>
    Sigma.ext rfl (heq_of_eq (Quotient.sound (MulAction.mem_orbit d g)))
  have hlaw : ∀ b (g : Q.S'.G b) d, F b (g • d) = φ b g (F b d) := by
    intro b g d
    set c := Q.S'.cl b d with hc
    have hrep : Q.S'.rep (Q.S'.cl b (g • d)) = Q.S'.rep c :=
      congrArg (Q.S'.rp b) (Quotient.sound (MulAction.mem_orbit d g))
    have h1 : Q.S'.mv b (g • d) • Q.S'.rep c = g • d := by
      convert Q.S'.mv_smul b (g • d) using 2; exact hrep.symm
    have h2 := Q.S'.mv_smul b d
    have hs : ((g * Q.S'.mv b d)⁻¹ * Q.S'.mv b (g • d)) • Q.S'.rep c = Q.S'.rep c := by
      rw [mul_smul, h1, _root_.mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff, h2]
    have hw := hinv' c _ hs
    show φ b (Q.S'.mv b (g • d)) (w (Q.S'.cl b (g • d))) = φ b g (φ b (Q.S'.mv b d) (w c))
    rw [hcl, ← φmul]
    conv_rhs => rw [hw, ← φmul, mul_inv_cancel_left]
  refine ⟨⟨F, fun b d => ⟨?_, fun g _ => hlaw b g d⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hw _))
  · rintro ⟨b, q⟩
    have hq : Q.S'.cl b (Q.S'.rep ⟨b, q⟩) = ⟨b, q⟩ := Sigma.ext rfl (heq_of_eq (Q.S'.rp_spec b q))
    have hr : Q.S'.rep (Q.S'.cl b (Q.S'.rep ⟨b, q⟩)) = Q.S'.rep ⟨b, q⟩ := congrArg (Q.S'.rp b) (Q.S'.rp_spec b q)
    have h1 : Q.S'.mv b (Q.S'.rep ⟨b, q⟩) • Q.S'.rep ⟨b, q⟩ = Q.S'.rep ⟨b, q⟩ := by
      convert Q.S'.mv_smul b (Q.S'.rep ⟨b, q⟩) using 2; exact hr.symm
    show φ b (Q.S'.mv b (Q.S'.rep ⟨b, q⟩)) (w (Q.S'.cl b (Q.S'.rep ⟨b, q⟩))) = w ⟨b, q⟩
    rw [hq]
    exact (hinv' ⟨b, q⟩ _ h1).symm

end GlobalTheory.Mem.Col2.PerIn
