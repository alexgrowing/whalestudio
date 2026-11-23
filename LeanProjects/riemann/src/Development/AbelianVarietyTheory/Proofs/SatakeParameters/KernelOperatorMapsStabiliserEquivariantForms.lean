import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValuesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLawStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ.FiCore

theorem isVal_sum {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → Yv → ℂ) (h : ∀ c, IsVal fr lam (RingHom.id ℂ) (f c)) :
    IsVal fr lam (RingHom.id ℂ) (∑ c ∈ s, w c • f c) := by
  choose P hP hf using h
  refine ⟨∑ c ∈ s, w c • P c, Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hP c), ?_⟩
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, evG, MvPolynomial.eval₂_sum, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem lawAt_sum {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ)
    (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → C.Y i → ℂ) (h : ∀ c, LawAt O i g (f c)) :
    LawAt O i g (∑ c ∈ s, w c • f c) := by
  intro y y' hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [h c y y' hy]; ring

theorem K_mem_Fi : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  intro D u C A Pm M O G hF hU hd hT i hi φ hφ
  have hv := hF.1 i hi.le φ hφ
  refine (hF.2 (i + 1) (Nat.le_add_left 1 i) hi _).2 fun c' => ?_
  have hK : C.K i φ c' = ∑ c, C.wt i c • C.Kmap i c c' (φ c) := by
    simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM]
  rw [hK]
  exact ⟨isVal_sum _ _ _ _ _ fun c => GlobalTheory.T.pair_kernel_maps_step_weight_values D u C A Pm M O i hi (hU i hi) c c' _ (hv c),
    fun g hg => lawAt_sum O _ g _ _ _ fun c =>
      GlobalTheory.T.pair_kernel_term_target_stabiliser_law D u C A Pm M O i hi (hU i hi) c c' (hd i hi c c') g (hT i hi c c' g hg) _ (hv c)⟩

end GlobalTheory.KerJ.FiCore
