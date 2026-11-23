import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PullLocSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProd

noncomputable section

namespace PI.VolStabW.TopoFibInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X]

theorem isFibreFamily_map (e : V ≃ₜ V) {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν B fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hf : ∀ x, f (e x) = f x) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν B (fun b => (fib b).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι b ∧ x ∈ U)
      rw [hf x, hx]
    rw [this]
    exact hfib.1 b
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    refine lintegral_congr fun b => ?_
    exact (lintegral_map_equiv _ _).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b hb => (integrable_map_equiv em φ).2 (h1 b hb), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib b).map em)) = fun b => ∫ x, (φ ∘ e) x ∂(fib b) :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    exact h2

end Abstract

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gramR_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (h • X) = gramR R σ J X := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  funext x y
  change hR R σ J (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR R σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

theorem linIndep_mulVec {A : Type} [CommRing A] (G : GL (Fin M) A) (X : Fin a → Fin M → A) :
    LinearIndependent A (fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) ↔ LinearIndependent A X := by
  have inj : ∀ H : GL (Fin M) A, LinearMap.ker (mulVecLin (H : Matrix (Fin M) (Fin M) A)) = ⊥ :=
    fun H => by
      refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
      have := congrArg (fun z => ((H⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ z) hxy
      simpa [mulVecLin_apply, mulVec_mulVec] using this
  constructor
  · intro hl
    have h2 := hl.map' (mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) (inj G⁻¹)
    have e : (⇑(mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) ∘
        fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) = X := by
      funext x
      simp [mulVec_mulVec]
    rw [e] at h2
    exact h2
  · intro hl
    exact hl.map' (mulVecLin (G : Matrix (Fin M) (Fin M) A)) (inj G)

theorem linIndep_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) (h • X) ↔ LinearIndependent (R ⊗[F] E) X :=
  linIndep_mulVec (HA.mat R σ J h) X

end Loc

end PI.VolStabW.TopoFibInv

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MuInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ h : HA (Ainf F) σ J, μinf.map (fun X => h • X) = μinf

def MuInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ h : HA (Fv F v) σ J, μv.map (fun X => h • X) = μv

theorem fibInvInf_of (hP : FibPin) (hM : MuInvInf) : FibInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfi h Φinf
    hcΦ hcs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Ainf F) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfi
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h)
    (fun x => TopoFibInv.gramR_smul (Ainf F) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Ainf F) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 μinf hμ νinf hν _ _ hfam hfi Φinf
    hcΦ hcs
  rw [integral_map_equiv] at this
  exact this

theorem fibInvV_of (hP : FibPin) (hM : MuInvV) : FibInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfv h Φv hSB
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Fv F v) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfv
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h)
    (fun x => TopoFibInv.gramR_smul (Fv F v) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Fv F v) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2 v μv hμ νv hν _ _ hfam hfv Φv hSB
  rw [integral_map_equiv] at this
  exact this

theorem nuInv_of_steps (hD : DetAdm) (hC : CompG) (hP : FibPin) (hMI : MuInvInf) (hMV : MuInvV) :
    NuInv :=
  nuInv_of_loc gramPres_holds (pullLoc_of hC (fibInvInf_of hP hMI) (fibInvV_of hP hMV)) hD

end PI.VolStabW
