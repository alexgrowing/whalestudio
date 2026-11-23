import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaPoisson

section Gen

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  (Γ : AddSubgroup A) [DiscreteTopology Γ] (K : Set A) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : A → A → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure A) (𝓕 : Set A) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)

include hK hcov hc hsy hadd hn hker hinj hμ hF h1

theorem poisson_translates {f : A → ℂ} (hf : Continuous f)
    (hb : ∀ Q : Set A, IsCompact Q → ∃ b : Γ → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ : Γ, ‖f (ξ + x)‖ ≤ b ξ)
    (hsum : Summable fun γ : Γ => ‖∫ x, f x * B x γ ∂μ‖) :
    ∑' ξ : Γ, f ξ = ∑' γ : Γ, ∫ x, f x * B x γ ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable Γ.subtype f := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := hb Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  have hfi : Integrable f μ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hf hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine ⟨⟨-γ, Γ.neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h
  have hcont : Continuous fun x => ∑' ξ : Γ, f (ξ + x) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨Q, hQ, hxQ⟩ := exists_compact_mem_nhds x
    obtain ⟨b, hb1, hb2⟩ := hb Q hQ
    have h : ContinuousOn (fun x => ∑' ξ : Γ, f (ξ + x)) Q :=
      continuousOn_tsum (fun ξ => (hf.comp (continuous_const.add continuous_id)).continuousOn) hb1
        (fun ξ x hx => hb2 x hx ξ)
    exact h.continuousAt hxQ
  have hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ := by
    intro γ
    have hi : Integrable (fun x => f x * B x γ) μ :=
      hfi.mul_bdd (c := 1) (hc γ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y γ).le)
    rw [(GlobalTheory.CovolumeOneSelfDual.unfold Γ μ 𝓕 hF _ hi).2]
    congr 1
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]
  have key := GlobalTheory.CompactQuotientFourier.inversion_at_zero A Γ K hK hcov Γ (fun γ x => B γ x)
    (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x)
    (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    (fun a h => Subtype.ext (hinj a a.2 h)) μ 𝓕 hμ hF h1 (fun x => ∑' ξ : Γ, f (ξ + x))
    hcont
    (fun γ hγ x => by
      rw [← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]
      refine tsum_congr fun ξ => ?_
      simp [add_assoc])
    (by simp only [hcoef]; exact hsum)
  simp only [hcoef, add_zero] at key
  exact key

end Gen

section Adelic

variable {D : D7} {m n : ℕ}

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩)
    ⟨fun _ _ h => rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, h⟩ => ⟨ξ, Subtype.ext h⟩⟩

theorem tsum_ratMx (f : Mx D m n → ℂ) :
    ∑' γ : ratMx D m n, f γ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, f (ξ.map (incA D)) :=
  ((ratEquiv D m n).tsum_eq fun γ : ratMx D m n => f γ).symm

theorem pairing_symm {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ x y = GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ y x := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA
  rw [← GlobalTheory.SiegelWeilLitCompare.gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ T x y))]
  congr 2
  simp only [Matrix.trace, map_sum]
  rfl

theorem translates_bound {θ : InfFam D} (hθ : IsInfFam θ) (φ : schwartzA θ m n) (Q : Set (Mx D m n)) (hQ : IsCompact Q) :
    ∃ b : ratMx D m n → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ : ratMx D m n, ‖φ.1 (ξ + x)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun γ => |C| * b ((ratEquiv D m n).symm γ), ((ratEquiv D m n).symm.summable_iff.2 hb).mul_left |C|, ?_⟩
  intro x hx γ
  obtain ⟨ξ, rfl⟩ := (ratEquiv D m n).surjective γ
  have h1 := hb' x hx ξ
  have h2 := hC (x + rat ξ)
  have e : ((ratEquiv D m n ξ : Mx D m n) + x) = x + rat ξ := add_comm _ _
  rw [e]
  beta_reduce
  rw [Equiv.symm_apply_apply]
  exact h2.trans (mul_le_mul (le_abs_self C) h1 (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C))

end Adelic

theorem theta_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
    ∀ g : G D n, mat g = blk4 0 1 (-1) 0 →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g hg Φ
  obtain ⟨-, -, hψ, -, -, hθ, ⟨𝓕, hμ⟩, hω⟩ := hS
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

end GlobalTheory.CompanionTheory.ThetaPoisson
