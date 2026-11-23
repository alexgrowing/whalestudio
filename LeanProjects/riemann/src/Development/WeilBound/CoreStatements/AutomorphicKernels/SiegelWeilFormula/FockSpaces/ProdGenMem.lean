import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isSw_fP {m n : ℕ} (P : PX m n) : IsSw (fP P) := by
  obtain ⟨S, hS⟩ := fPSch P (c := 2 * Real.pi) (by positivity)
  exact ⟨S, funext fun x => by rw [hS]; rfl⟩

theorem prodGen_mem (d : SD σ) (R : RD d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨L, hL⟩ := archEquiv d R
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  rw [SD.schM, Submodule.mem_comap]
  apply Submodule.subset_span
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hT, hL, crd_cmb]

theorem fock_le (d : SD σ) (R : RD d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨P, g, hg, rfl⟩
  choose S hS using fun w => isSw_fP (P w)
  simp only [← hS]
  exact prodGen_mem d R S g hg

theorem tens_mem (d : SD σ) (R : RD d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  subst hφ
  change Ψ ∈ R.fockOn (Finset.univ.erase w) at hΨ
  unfold RD.fockOn at hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, g, hg, rfl⟩ := hx
    choose S hS using fun w' => isSw_fP (P w')
    have hmem := prodGen_mem d R (Function.update S w φ) g hg
    have heq : R.tens w ⇑φ
        (fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
        fun X => (∏ w', (Function.update S w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2 := by
      funext X
      rw [← Finset.mul_prod_erase Finset.univ (fun w' => (Function.update S w φ w') (R.loc w' X))
        (Finset.mem_univ w)]
      have hpr : ∏ w' ∈ Finset.univ.erase w, (Function.update S w φ w') (R.loc w' X) =
          ∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X) :=
        Finset.prod_congr rfl fun w' hw' => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), hS w']
      rw [hpr]
      simp only [RD.tens, Function.update_self]
      ring
    rw [heq]
    exact hmem
  | zero =>
    have h0 : R.tens w ⇑φ 0 = 0 := by
      funext X
      simp [RD.tens]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [tens_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [tens_smul]
    exact Submodule.smul_mem _ a hx

end PositivityTheory.SiegelWeilFormula.KFock

end
