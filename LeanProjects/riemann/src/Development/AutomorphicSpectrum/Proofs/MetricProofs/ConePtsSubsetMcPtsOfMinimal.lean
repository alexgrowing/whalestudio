import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentsMeetNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartRatioImageNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResFibreSum

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem conePts_subset_mcPts_of_minimal {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) : conePts Q ⊆ mcPts P := fun _ hz =>
  ⟨hz.1, fun f hf => hz.2 _ (hQ.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem exists_minimal_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ∃ Q ∈ (cxIdeal P).minimalPrimes, z ∈ conePts Q := by
  have hz' : z ∈ conePts (cxIdeal P) := by rw [← mcPts_eq_conePts]; exact hz
  have hle : cxIdeal P ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) :=
    fun f hf => RingHom.mem_ker.2 (hz'.2 f hf)
  have : (RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, hQ, hz'.1, fun f hf => RingHom.mem_ker.1 (hQle hf)⟩

theorem mem_conePts_of_segre_eq {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (hs : segre z = segre z') : z' ∈ conePts Q := by
  classical
  choose i0 hi0 using hz.1
  obtain ⟨-, h4⟩ := eq_bsmul_of_segre_eq i0 hi0 hs
  have hJ := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge.isMultiHomogIdeal_of_mem_minimalPrimes hP hQ
  have h5 := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z hz.2
  refine ⟨hz', fun f hf => ?_⟩
  rw [h4]
  exact h5 f hf

theorem isSheet_of_isSetSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)}
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet P Ψ y w γ :=
  ⟨h.1, h.2.mono fun _ h' => ⟨h'.1, conePts_subset_mcPts_of_minimal hQ h'.2.1, h'.2.2⟩⟩

theorem isSetSheet_of_isSheet {P : Ideal (MRing ι)} {Q : Ideal (MRingOver ℂ ι)} (hP : IsArithVar P (e + 1))
    (hQ : Q ∈ (cxIdeal P).minimalPrimes) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hone : ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q → z ∈ conePts Q' →
      Ψ (segre z) = Fin.cons 1 y → Q' = Q)
    (hw : w ∈ setFibre (conePts Q) Ψ y) (h : IsSheet P Ψ y w γ) :
    IsSetSheet (conePts Q) Ψ y w γ := by
  obtain ⟨z, hz, hzw, -⟩ := hw
  obtain ⟨hd, hm, hΨγ⟩ := h.2.self_of_nhds
  have hγQ : γ y ∈ conePts Q := mem_conePts_of_segre_eq hP hQ hz hm.1 (hzw.trans h.1.symm)
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hev : ∀ᶠ y' in 𝓝 y, ∀ Q' ∈ (cxIdeal P).minimalPrimes, Q' ≠ Q → γ y' ∉ conePts Q' := by
    refine (Filter.eventually_all_finite hfin).2 fun Q' hQ' => ?_
    by_cases hne : Q' = Q
    · exact Eventually.of_forall fun _ h' => absurd hne h'
    have hnot : γ y ∉ conePts Q' := fun hc => hne (hone Q' hQ' _ hγQ hc hΨγ)
    obtain ⟨f, hf, hf0⟩ : ∃ f ∈ Q', eval (γ y) f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨hm.1, hcon⟩
    have hc : ContinuousAt (fun y' => eval (γ y') f) y :=
      (MvPolynomial.continuous_eval f).continuousAt.comp hd.continuousAt
    filter_upwards [hc.eventually_ne hf0] with y' hy' _ hmem
    exact hy' (hmem.2 f hf)
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hev] with y' h1 h2
  obtain ⟨Q', hQ', hz'⟩ := exists_minimal_of_mem_mcPts h1.2.1
  by_cases hne : Q' = Q
  · subst hne
    exact ⟨h1.1, hz', h1.2.2⟩
  · exact absurd hz' (h2 Q' hQ' hne)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
