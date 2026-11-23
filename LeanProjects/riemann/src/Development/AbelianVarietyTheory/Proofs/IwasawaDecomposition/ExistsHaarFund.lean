import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

noncomputable section

namespace GlobalTheory.Mem.SJ.HaarMove

open MeasureTheory
open scoped Pointwise

theorem exists_haar_fund {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [MeasurableSpace G'] [BorelSpace G']
    (μ' : Measure G') [μ'.IsHaarMeasure] (ι : G ≃ₜ* G') (Γ : Subgroup G) (Γ' : Set G')
    (hΓ : ∀ g, g ∈ Γ ↔ ι g ∈ Γ') (F' : Set G') (hm : MeasurableSet F') (hc : ∀ y, ∃ γ ∈ Γ', γ * y ∈ F')
    (hd : ∀ γ ∈ Γ', γ ≠ 1 → μ' ((fun y => γ * y) '' F' ∩ F') = 0) (t : G) :
    ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∀ f : G → ℂ, ∫ g in F, f g ∂μ = ∫ x in F', f (ι.symm x * t) ∂μ' := by
  let e : G' ≃ᵐ G := (ι.symm.toHomeomorph.trans (Homeomorph.mulRight t)).toMeasurableEquiv
  have he : ∀ x, e x = ι.symm x * t := fun _ => rfl
  have hes : ∀ g, e.symm g = ι (g * t⁻¹) := fun g => by
    rw [MeasurableEquiv.symm_apply_eq, he]; simp
  have hH : (μ'.map e).IsHaarMeasure := by
    have h1 : (μ'.map ι.symm).IsHaarMeasure := ι.symm.isHaarMeasure_map μ'
    have h2 : μ'.map e = (μ'.map ι.symm).map (· * t) := by
      exact (Measure.map_map (measurable_mul_const t) (map_continuous ι.symm).measurable).symm
    rw [h2]; infer_instance
  refine ⟨μ'.map e, e.symm ⁻¹' F', hH, ?_, fun f => ?_⟩
  · refine IsFundamentalDomain.mk'' (e.symm.measurable hm).nullMeasurableSet (ae_of_all _ fun g => ?_)
      (fun γ hγ => ?_) (fun γ => (measurePreserving_mul_left (μ'.map e) (γ : G)).quasiMeasurePreserving)
    · obtain ⟨γ, hγ, h⟩ := hc (e.symm g)
      refine ⟨⟨ι.symm γ, (hΓ _).2 (by simpa using hγ)⟩, ?_⟩
      show e.symm (ι.symm γ * g) ∈ F'
      rw [hes] at h ⊢
      simpa [mul_assoc] using h
    · have h0 := hd (ι γ) ((hΓ _).1 γ.2) (fun h => hγ (Subtype.ext (ι.injective (by simpa using h))))
      rw [AEDisjoint, MeasurableEquiv.map_apply]
      refine measure_mono_null ?_ h0
      rintro x ⟨⟨g, hg, hx⟩, h2⟩
      refine ⟨⟨e.symm g, hg, ?_⟩, by simpa using h2⟩
      have hx' : (γ : G) * g = ι.symm x * t := hx
      show ι γ * e.symm g = x
      rw [hes, ← map_mul, ← mul_assoc, hx']; simp
  · rw [setIntegral_map_equiv]
    simp only [he]
    congr 2
    ext x; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schur_of_bridge {D : D7} {V : HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V))
    (χ : GA D V → ℂ) (hS : ∀ μ 𝓕, SchurMult θ M J χ μ 𝓕) (hθ : IsInfFam θ)
    (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ι : GA D V ≃ₜ* I.GA) (hι : ∀ g, g ∈ GQ V ↔ ι g ∈ I.GFset) (t : GA D V)
    (T : MMap M) (hT : T ∈ Mult θ M J χ) (T' : MMap M) (hT' : T' ∈ Mult θ M J χ) :
    ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂((I.muA μf).restrict fund) =
      c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : (I.muA μf).IsHaarMeasure := by
    unfold AutInst.muA Formalism.REAL.muG; infer_instance
  obtain ⟨μ, F, hμ, hF, hint⟩ := exists_haar_fund (I.muA μf) ι (GQ V) I.GFset hι fund hf.1 hf.2.1 hf.2.2 t
  obtain ⟨c, hc⟩ := hS μ F hθ hμ hF T hT T' hT'
  exact ⟨c, fun v v' => (hint fun g => star (T v g) * T' v' g).symm.trans (hc v v').2⟩

end GlobalTheory.Mem.SJ.HaarMove

end
