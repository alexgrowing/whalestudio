import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParamsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem linearIndependent_of_isParamFunV : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type)
    (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) →
    (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) →
    LinearIndependent ℂ f := by
  intro D V Sb ι f B h0 hP hB
  have hJ := GlobalTheory.LFun.sphOff_KsphC V Sb
  choose a ha using fun i => GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D V (KsphC V ∅) (fun _ => 1) Sb hJ (B i)
  have hfix : ∀ i, ∀ v ∉ Sb, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v, ∀ g,
      f i (g * GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) = f i g := by
    intro i v hv k hk g
    obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
      have := v.isPrime
      obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
    have hx := (hP i v hv w hw).mem_fixed
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hx k hk) g
  let α := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
    Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb t.1 t.2.1 t.2.2}
  refine GlobalTheory.FinWeil.linearIndependent_of_simultaneous_eigen f (fun i (t : α) => a i t.1.1 t.1.2.1)
    (fun t : α => heckeLin V t.1.2.2) ?_ (fun t i => ha i (f i) (hP i) _ _ _ t.2) h0
  intro i i' hii
  by_contra hne
  obtain ⟨w, hw, hne'⟩ := hB i i' hne
  have hc : ∀ P d R, Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb P d R → heckeLin V R (f i') = a i P d • f i' := by
    intro P d R hR
    have := congrFun hii ⟨(P, d, R), hR⟩
    rw [ha i' (f i') (hP i') P d R hR]
    exact congrArg (· • f i') this.symm
  have h1 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i) (hfix i) (ha i (f i) (hP i)) (B i)).1 (hP i)
  have h2 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i') (hfix i') hc (B i')).1 (hP i')
  exact hne' (GlobalTheory.LFun.IsSysParamOff.unique h1 h2 hw)

end GlobalTheory.ChainOnto
