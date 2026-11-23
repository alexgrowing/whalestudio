import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.LocSph

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

namespace SatakeVectorEventually

def MapsD {N : ℕ} (V : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E N // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E N (locGL E N w g) (f v)}

theorem iSup_range_eq {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (h : IsLocCompGL V w σ) :
    ⨆ f : MapsD V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E N, (∀ g, act o * finRep E N (locGL E N w g) = finRep E N (locGL E N w g) * act o) →
      ∀ (f : MapsD V w σ) v, act o (f.1 v) ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hV.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : MapsD V w σ) ⟨v, rfl⟩
  refine (hV.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : MapsD V w σ, LinearMap.range f.1) ≤ (⨆ f : MapsD V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E N w g)⁻¹)) (fun g' => by
          change finRep E N _ * _ = _ * finRep E N _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E N w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E N) (infGL_comm (Unitary.toUnits k) (locGL E N w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E N w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hfV, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, hfV, hf⟩ : MapsD V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact (Submodule.mem_bot ℂ).1 this

end SatakeVectorEventually

open SatakeVectorEventually in

theorem eventually_satV {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, SatV V w B := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  filter_upwards [eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.discreteAutomorphicRepGL_exists_localComponent PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N V hV w
  have hfix : ∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) φ = φ := fun k hk => by
    obtain ⟨g, rfl⟩ := hk
    exact hw g
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [iSup_range_eq hV w σ hσ]; exact hψ
  obtain ⟨v, hv0, hv⟩ := exists_fixed_of_mem_iSup ((finRep E N).comp (locGL E N w)) σ.ρ σ.irred
    (fun f : MapsD V w σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL w N : Set _) φ h0 hfix (hmem φ hφ)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w N) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  have key : ∀ ψ ∈ V, (∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) ψ = ψ) → ψ ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) ψ B := fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB (fun f : MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0
  exact ⟨B, ⟨φ, hφ, key φ hφ hfix h0⟩, key⟩

end PositivityTheory.Rg.Rs.SatakeVectors

end
