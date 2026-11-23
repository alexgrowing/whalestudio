import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuotAlt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem gmap_cont {K L : Type} [Field K] [Field L] [TopologicalSpace K] [TopologicalSpace L]
    [IsTopologicalRing K] [IsTopologicalRing L] (i : K ≃+* L) (hi : Continuous i) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) i.toRingHom) := by
  have h : Continuous ((RingHom.mapMatrix (m := Fin 2) i.toRingHom).toMonoidHom) :=
    Continuous.matrix_map continuous_id hi
  exact Continuous.units_map _ h

private theorem gmap_surj {K L : Type} [Field K] [Field L] (i : K ≃+* L) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin 2) i.toRingHom) := by
  intro g
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin 2) i.symm.toRingHom g, ?_⟩
  ext a b
  simp

attribute [-instance] GlobalTheory.AdmLoc.modFun in
theorem UpperTheory.ConvolutionTheory.R2.I.fin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : P F) (w : P E) (i : Kv v ≃+* Kv w), Continuous i →
      ∀ σ (σ' : SmIrr (GLv w)), π.IsLocComp v σ → ∀ T : σ'.V →ₗ[ℂ] (GLv v → ℂ), T ≠ 0 →
      (∀ g u x, T (σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) u) x = T u (x * g)) → (∀ u, T u ∈ MC (π.locRep v)) →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x) := by
  intro F E _ _ _ _ _ π v w i hi σ σ' h T hT hTe hTm
  let φ : GLv v →* GLv w := Matrix.GeneralLinearGroup.map i.toRingHom
  have hφc : Continuous φ := gmap_cont i hi
  have hφs : Function.Surjective φ := gmap_surj i
  let ρ₂ : Representation ℂ (GLv v) σ'.V := σ'.ρ.comp φ
  have hsm : GlobalTheory.PRep.IsSmooth ρ₂ := fun u => (σ'.smooth u).preimage hφc
  have hir : ρ₂.IsIrreducible := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ'.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g u hu => ?_⟩
    obtain ⟨g', rfl⟩ := hφs g
    exact hW g' u hu
  let σ₂ : SmIrr (GLv v) := { V := σ'.V, ρ := ρ₂, smooth := hsm, irred := hir }
  have key := UpperTheory.ConvolutionTheory.R2.Pp.isotypQuot F π v σ σ₂ h (GLv v → ℂ) (GlobalTheory.PRep.rightReg ℂ (GLv v) ℂ) T hT
    (fun g u => by
      funext x
      exact hTe g u x)
    (fun u => by
      refine (Submodule.span_le.2 ?_) (hTm u)
      rintro _ ⟨Λ, f, rfl⟩
      refine Submodule.subset_span ⟨
        { toFun := fun f x => Λ (π.locRep v x f)
          map_add' := fun a b => by funext x; simp
          map_smul' := fun c a => by funext x; simp }, fun g x => ?_, f, rfl⟩
      funext y
      simp [GlobalTheory.PRep.rightReg, LinearMap.funLeft])
  exact key
