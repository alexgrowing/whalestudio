import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.OneMapTuples.unitC_of_cXiAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n r : ℕ) (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∀ (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → d.IsLev → d.l₂.A = 1 → ∀ (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ), 0 < N → (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1) → ∀ (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U₂.X k).Ψ r) (c0 : ℂ), c0 ^ N = 1 → GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0 → GlobalTheory.Dict.UnitC d := by
  intro D H Dw V l Xo c n r d hr io hι hpq x₀ hx₀ hd hA xi N hN hxN U dict c0 hc0 hv A y
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := hd
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  have hσ : GoodEmb d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) := rfl
  have val₀ : ∀ h : GA D V, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom,
      toC (evR d.Xo₂ d.c₂ d.cδ (U.un _ ⟨_, hx⟩)) ^ N = 1 := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    obtain ⟨hx, ex⟩ := GlobalTheory.ShortMove.rdU_eq U d.cδ _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
    refine ⟨hx, ?_⟩
    rw [ex.symm.trans hv, mul_pow, hc0, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, one_mul]
  choose hdom val₀ using val₀
  have hx : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)
  have hroot : ∀ z : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      evR d.Xo₂ d.c₂ d.cδ z ^ N = 1 := fun z => by
    obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U dict io e₀ F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx hdom z
    rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hsec hh]
    exact val₀ h
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS _ H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    _ d.cδ hsec.1 N hroot
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ N h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS _ _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hN.ne'

end
