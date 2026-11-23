import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem linRedC : LinRedC := by
  unfold LinRedC
  intro hT hTC hL hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW
  have hTT : TTheta := hT.2.2.2.1
  have hTA : ThetaAuto := hT.2.2.2.2
  have hsch : ∀ i, Φs i ∈ d.sch := fun i => (hK i).1
  have hΦ : (∑ i : Fin k, cs i • Φs i) ∈ d.sch :=
    lin_sum_mem d Finset.univ cs Φs (fun i _ => hsch i)
  have hunf := fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  choose t ht using hunf
  have hpsi : ∀ a, ‖d.B.ψ a‖ = 1 := fun a => GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std a
  unfold WhitAtC
  intro nb lam 𝓖 hcd ε w hw T hT'
  have hval : c * d.orb T ((d.om x) (∑ i : Fin k, cs i • Φs i)) =
      ∑ i : Fin k, cs i * (c * d.orb T ((d.om x) (Φs i))) := by
    have hI : d.I (∑ i : Fin k, cs i • Φs i) = ∑ i : Fin k, cs i • d.I (Φs i) := by
      funext y
      rw [lin_I_sum d hTT hTA Finset.univ cs Φs (fun i _ => hsch i) y]
      simp [Finset.sum_apply]
    have h1 := hTC F E σ d _ hΦ nb lam 𝓖 hcd T x
    rw [← h1, hI, lin_fc_sum hL d hcd T hT' x Finset.univ cs (fun i => d.I (Φs i))
      (fun i => ((hTA F E σ d).2.2 (Φs i) (hsch i)).2.1)
      (fun i => ((hTA F E σ d).2.2 (Φs i) (hsch i)).2.2), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hTC F E σ d _ (hsch i) nb lam 𝓖 hcd T x]
    ring
  rw [hval]
  have hsum := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (↑↑T * ↑β)) ∂lam)
    (fun i => c * d.orb T ((d.om x) (Φs i))) (s0 d.m d.n)
    (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hT')
  refine HolValueAt.congr hsum ⟨∑ i : Fin k, |t i|, fun z hz => ?_⟩
  have hz' : ∀ i, t i < z.re := fun i =>
    lt_of_le_of_lt ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) hz
  have hint : ∀ i, MeasureTheory.Integrable (fun β => flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (↑↑T * ↑β))) lam := fun i =>
    ((ht i z (hz' i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd
      (lin_psi_meas d _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun β => (hpsi _).le))
  simp only
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finset_sum]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
    simp only [flat, section_linear_finset_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · exact fun i _ => (hint i).const_mul (cs i)

end PositivityTheory.SiegelWeilFormula.KWhit

end
