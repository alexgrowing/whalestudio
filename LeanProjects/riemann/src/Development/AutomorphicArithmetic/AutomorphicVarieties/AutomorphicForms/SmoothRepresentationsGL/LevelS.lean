import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.levelS :
    UpperTheory.V.Af.Smo.LevelS := by
  intro E _ _ n V
  let e := AdelicGLn.finiteRestrictedEquiv E n
  let f : (∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) →
      GL (Fin n) (Af E) := fun x => e.symm (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hf : Continuous f := e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  let o : ∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E))) :=
    fun v => ⟨1, one_mem _⟩
  have ho : f o = 1 := by
    refine e.symm_apply_eq.2 ?_
    rw [map_one]
    rfl
  have hV : f ⁻¹' (V : Set (GL (Fin n) (Af E))) ∈ 𝓝 o := hf.continuousAt.preimage_mem_nhds (ho ▸ V.mem_nhds_one)
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨S, t, ht, hS⟩ := hV
  refine ⟨S, fun k hk => ?_⟩
  have hek : ∀ v, e k v = cmp v k := fun v => Units.ext (Matrix.ext fun _ _ => rfl)
  have hi : ∀ v : HeightOneSpectrum (𝓞 E), cmp v k ∈ GLnLocal.integralGL (v.adicCompletion E) n := fun v => by
    have h := GlobalTheory.AdelicU.mem_GLint_iff.1 (hk.2 v)
    rw [GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    exact h
  have hx : f (fun v => ⟨cmp v k, hi v⟩) = k := by
    refine e.symm_apply_eq.2 (DFunLike.ext _ _ fun v => ?_)
    exact (hek v).symm
  rw [← hx]
  refine hS fun v hv => ?_
  have : (⟨cmp v k, hi v⟩ : (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) = o v :=
    Subtype.ext (hk.1 v hv)
  exact this ▸ mem_of_mem_nhds (ht v)
