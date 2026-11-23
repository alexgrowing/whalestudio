import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Sobolev2

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem clm_sum {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (ℓ : (Fin k → ℝ) →L[ℝ] M) (s : Fin k → ℝ) :
    ℓ s = ∑ i, s i • ℓ (ev i) := by
  have : s = ∑ i, s i • ev i := by
    funext j; simp [ev, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  rw [map_sum]
  simp [map_smul]

section Real

variable (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)

include hΛ hL in

theorem beta_poly (s t : Fin k → ℝ) :
    Λ (symplOH S T (L s) (L t)).1 = ∑ i, ∑ j, s i * t j * Λ (symplOH S T (L (ev i)) (L (ev j))).1 := by

  have hs : ∀ t, Λ (symplOH S T (L s) (L t)).1 = ∑ i, s i * Λ (symplOH S T (L (ev i)) (L t)).1 := by
    intro t
    let g : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun s => Λ (symplOH S T (L s) (L t)).1) (fun a b => by
      simp only [map_add, symplOH_add_left]; exact Λ.map_add _ _)
    have hg : Continuous g := by
      have h1 : Continuous fun s => symplOH S T (L s) (L t) := (continuous_symplOH_left (L t)).comp hL
      exact hΛ.comp (continuous_fst.comp h1)
    have := clm_sum (AddMonoidHom.toRealLinearMap g hg) s
    simpa [g, smul_eq_mul] using this
  rw [hs t]
  refine Finset.sum_congr rfl fun i _ => ?_
  let g : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => Λ (symplOH S T (L (ev i)) (L t)).1) (fun a b => by
    simp only [map_add, symplOH_add_right]; exact Λ.map_add _ _)
  have hg : Continuous g := by
    have h1 : Continuous fun t => symplOH S T (L (ev i)) (L t) := (continuous_symplOH_right _).comp hL
    exact hΛ.comp (continuous_fst.comp h1)
  have := clm_sum (AddMonoidHom.toRealLinearMap g hg) t
  simp only [AddMonoidHom.coe_toRealLinearMap, g, AddMonoidHom.mk'_apply, smul_eq_mul] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.real_smul]
  ring

end Real

section RealCont

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in

theorem cont_real {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x0 : WO S T) {n : ℕ} (l : Fin n → Fin k) :
    Continuous fun s => dH ψ L l f (x0 + L s) := by
  set b : Fin k → Fin k → ℂ := fun i j => Λ (symplOH S T (L (ev i)) (L (ev j))).1
  set g0 : (Fin k → ℝ) → ℂ := fun r => f (x0 + L r)
  have hg0 : ContDiff ℝ ∞ g0 := hf.smooth k L hL.1 hL.2.1 x0
  set ℓ := ellx Λ hΛ L hL.1 x0
  set Φ : (Fin k → ℝ) × (Fin k → ℝ) → ℂ := fun p =>
    Complex.exp (ℓ p.2 + ∑ i, ∑ j, (p.1 i : ℂ) * (p.2 j : ℂ) * b i j) * g0 (p.1 + p.2)
  have hΦ : ContDiff ℝ ∞ Φ := by
    have h1 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin k → ℝ) => ℓ p.2 := ℓ.contDiff.comp contDiff_snd
    have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∑ i, ∑ j, (p.1 i : ℂ) * (p.2 j : ℂ) * b i j := by
      refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
      refine ContDiff.mul (ContDiff.mul ?_ ?_) contDiff_const
      · exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_fst)
      · exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (h1.add h2)).mul (hg0.comp (contDiff_fst.add contDiff_snd))
  have hGf : ∀ s, Gf ψ L f (x0 + L s) = fun t => Φ (s, t) := by
    intro s; funext t
    have hrs : eInf D • L s = L s := (wo_real_iff (L s)).mp (hL.2.1 s)
    have hrt : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
    simp only [Gf, heisO, Φ, g0]
    rw [symplOH_add_left]
    have h2 : (symplOH S T x0 (L t) + symplOH S T (L s) (L t)).2 = 0 := by
      show (symplOH S T x0 (L t)).2 + (symplOH S T (L s) (L t)).2 = 0
      rw [symplOH_snd _ _ hrt, symplOH_snd _ _ hrt, add_zero]
    rw [hψΛ _ h2, show (symplOH S T x0 (L t) + symplOH S T (L s) (L t)).1 =
      (symplOH S T x0 (L t)).1 + (symplOH S T (L s) (L t)).1 from rfl, map_add, beta_poly Λ hΛ L hL.1 s t,
      map_add, add_assoc]
    rfl
  have hval : ∀ s, dH ψ L l f (x0 + L s) = iteratedFDeriv ℝ n Φ (s, 0) (fun i => (0, ev (l i))) := by
    intro s
    have e : dH ψ L l f (x0 + L s) = iteratedFDeriv ℝ n (Gf ψ L f (x0 + L s)) 0 (fun i => ev (l i)) := rfl
    rw [e, hGf s]
    have hcomp : (fun t => Φ (s, t)) = (fun q => Φ (q + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ)) := by
      funext t; simp
    have hΦs : ContDiff ℝ ∞ (fun q => Φ (q + (s, 0))) := hΦ.comp (contDiff_id.add contDiff_const)
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ))
      hΦs 0 (natCast_lt_inf n).le, iteratedFDeriv_comp_add_right]
    simp
  simp_rw [hval]
  exact (ContinuousMultilinearMap.apply ℝ _ ℂ _).continuous.comp
    ((hΦ.continuous_iteratedFDeriv (natCast_lt_inf n).le).comp (continuous_id.prodMk continuous_const))

end RealCont

end Formalism.IndefR.Eqv

end
