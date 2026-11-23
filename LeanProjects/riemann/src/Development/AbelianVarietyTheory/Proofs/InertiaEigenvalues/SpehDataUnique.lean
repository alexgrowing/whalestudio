import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published GlobalTheory.LFun

namespace GlobalTheory.SpehPair

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a d : ℕ}

theorem isUnitary_of_isNormalised {π : CuspSub E a} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  have hs : ∀ (b : ℕ) (t : ℝ), splitCentre E b t =
      Matrix.GeneralLinearGroup.scalar (Fin b) (infId E (expU fun _ => (t : ℂ))) := fun b t =>
    (cornerGL_scalar (sInf E) _)
  have h1 : ∀ t : ℝ, ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 := fun t => by
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h0 (Subtype.ext (funext hc))
    have h2 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
    rw [← hs, h φ hφ] at h2
    exact mul_right_cancel₀ hg (h2.symm.trans (one_mul _).symm)
  have h3 : ((CuspSub.triv E (le_refl 1)).twist ω).HasCentral ω :=
    CuspSub.hasCentral_iff.2 (CG.hasCentChar_ofChar ω)
  have h4 : IsNormalised ((CuspSub.triv E (le_refl 1)).twist ω) := fun φ hφ t g => by
    rw [hs, h3.apply hφ, h1, one_mul]
  exact hω.isUnitary_iff.2 (h3.isUnitary_iff.1 (Model.isUnitary_of_isNormalised h4))

theorem eventually_spherical {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ, IsLocCompGL V w σ →
      GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w N) := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  filter_upwards [LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨f, hf0, hfV, hf⟩ := hσ
  let F : σ.V →ₗ[ℂ] V := f.codRestrict V hfV
  have hF : ∀ g v, F (σ.ρ g v) = DiscLocEx.locRepD hV.stable w g (F v) := fun g v => Subtype.ext (hf g v)
  have hF0 : F ≠ 0 := fun e => hf0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v))
  have hi : LinearMap.ker F = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hF, hv, map_zero]) |>.resolve_right fun e => hF0 (LinearMap.ker_eq_top.1 e)
  have hfix : (⟨φ, hφ⟩ : V) ∈ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w N) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
      obtain ⟨g, rfl⟩ := hk
      exact hw g)
  have h1 : LinearMap.range F ⊓ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w N) ≠ ⊥ := fun e =>
    hF0 (LinearMap.range_eq_bot.1 (DiscLocEx.eq_bot_of_fixedD hV w GlobalTheory.SatInd.isCompact_KGL
      (fun e => h0 (congrArg Subtype.val e)) hfix _ (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hF g v⟩) e))
  obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => LinearMap.ker_eq_bot.1 hi (by
    rw [hF, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩

theorem exists_sat_twist (hd : 1 ≤ d) {π : CuspSub E a} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {σ' : SmIrr (GL (Fin N) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ)
    {T : Multiset ℂˣ} (hT : HasSatGL w σ'.ρ T) (ν : ℝ → HChar E) (hν : ∀ s, (ν s).IsAbsPow s) :
    ∃ B : Fin d → Multiset ℂˣ, (∀ i, ((CG.mk π).twist (ν (-spehExp d i))).HasSat w (B i)) ∧ ∑ i, B i = T := by
  obtain ⟨S, hS, e⟩ := GlobalTheory.SatInd.exists_sat_of_isSpeh hd σ.smooth σ.irred h hT
  refine ⟨_, fun i => GlobalTheory.SphGal.hasSatGL_twist E a π _ w S ((hν _).1 w)
    (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hS), ?_⟩
  refine Multiset.map_injective Units.val_injective (Eq.trans ?_ e)
  refine (map_sum (Multiset.mapAddMonoidHom _) _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Units.val_mul, (hν _).2.1 w, spehExp]
  congr 2
  push_cast
  ring

end GlobalTheory.SpehPair

end
