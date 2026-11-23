import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

variable {D : D7}

theorem isIsoSplit_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hq : d.qX * d.e = 1 := d.e'e
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm⟩
  · exact Matrix.mulVec_injective_iff.1 fun x y h => by
      have := congrArg (d.qX *ᵥ ·) h
      simpa only [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec] using this
  · rw [cT_sig]; exact d.ee
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]; exact d.iso
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]
    apply rat_injective
    rw [rat_mul, rat_mul, rat_conjTranspose, rat_zero, Matrix.mul_assoc]
    exact d.wittDecomp_gram_X_anisotropic

set_option maxHeartbeats 1000000 in
theorem mem_NI_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (h1 : mt S g ⬝ d.jX = d.jX)
    (h2 : d.pY ⬝ mt S g = d.pY) (B : Mx D ρ S₀.rank) (h3 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ B) : g ∈ NI S d.e := by
  apply Subgroup.subset_closure
  have hm1 : (mt S g - 1) ⬝ d.jX = 0 := by rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  have hm0 : (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by rw [Matrix.sub_mul, h3, Matrix.one_mul, add_sub_cancel_left]
  refine ⟨hm1, ?_, ?_⟩
  · rw [cT_sig]
    change d.pY ⬝ (mt S g - 1) = 0
    rw [Matrix.mul_sub, h2, Matrix.mul_one, sub_self]
  · intro x hx
    rw [cT_sig] at hx
    refine ⟨B *ᵥ (d.p0 *ᵥ fun i => incA D (x i)), ?_⟩
    have hv : d.pY *ᵥ (fun i => incA D (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec (incA D) d.qY x i
      change incA D (((d.eᴴ * HSpace.gram S) *ᵥ x) i) = _ at this
      rw [hx, Pi.zero_apply, map_zero] at this
      exact this.symm
    have hsum : (fun i => incA D (x i)) = d.jX *ᵥ (d.pX *ᵥ fun i => incA D (x i)) +
        d.j0 *ᵥ (d.p0 *ᵥ fun i => incA D (x i)) := by
      have h := congrArg (· *ᵥ fun i => incA D (x i)) d.sum_eq_one
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero] at h
      exact h.symm
    have hX : ∀ a, mt S g *ᵥ (d.jX *ᵥ a) = d.jX *ᵥ a := fun a => by rw [Matrix.mulVec_mulVec, h1]
    have h0 : ∀ a, mt S g *ᵥ (d.j0 *ᵥ a) = d.j0 *ᵥ a + d.jX *ᵥ (B *ᵥ a) := fun a => by
      rw [Matrix.mulVec_mulVec, h3, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    have final : (mt S g - 1) *ᵥ (fun i => incA D (x i)) = d.jX *ᵥ (B *ᵥ (d.p0 *ᵥ fun i => incA D (x i))) := by
      have hs := Matrix.sub_mulVec (mt S g) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (fun i => incA D (x i))
      rw [Matrix.one_mulVec] at hs
      rw [hs]
      conv_lhs => rw [hsum]
      rw [Matrix.mulVec_add, hX, h0]
      abel
    exact final

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge
open GlobalTheory.MixModel
variable {D : D7}

theorem orthProjPartHomToHermitian_eq_wittDecompositionCore {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w : WO S₀ T) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w := by
  rw [HypDec.matrixExtendByZero_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig, Matrix.mul_assoc]
  rfl

theorem integrand_eq {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (x a : Mx D T.rank ρ) (w : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 =
      heisO ψ S T (d.extX T x) f (d.extY T a + d.ext0 T w) := by
  rw [d.integrandS_eq]
  simp only [heisO]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extX T x) (d.ext0 T w), d.wittDecomp_sympl_extIsotropic_extAnisotropic T x w,
    neg_zero, add_zero, add_right_comm]

theorem mixS_eq_res {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f) := by
  funext w
  simp only [HypDec.mixS, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, orthProjPartHomToHermitian_eq_wittDecompositionCore]
  congr 1
  funext a
  exact integrand_eq d ψ f x a w

theorem mixS_heis {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 := by
  funext w
  simp only [HypDec.mixS]
  congr 1
  funext a
  rw [integrand_eq d ψ f x a w, integrand_eq d ψ _ 0 a w, map_zero]
  simp only [heisO, add_zero, GlobalTheory.OrientedHeis.symplOH_add_left]
  rw [symplOH_skew S T 0 (d.extY T a), symplOH_skew S T 0 (d.ext0 T w)]
  simp only [symplOH_zero_left, neg_zero, zero_add, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

theorem heis_bridge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (0 < ρ → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀) ∧ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ = ratMx D T.rank ρ ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e y = d.extY T y) ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e' y = d.extX T y) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f)) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0) ∧ (∀ b, d.nB b ∈ NI S d.e) ∧ ∀ c, d.nC c ∈ NI S d.e := by
  intro D ψ S S₀ T ρ d
  exact ⟨isIsoSplit_hyp d, rfl, fun _ => rfl, fun _ => rfl, orthProjPartHomToHermitian_eq_wittDecompositionCore d T,
    fun μ 𝓕 f x => mixS_eq_res d ψ μ 𝓕 f x, fun μ 𝓕 f x => mixS_heis d ψ μ 𝓕 f x,
    fun b => mem_NI_hyp d _ (d.nB_jX b) (d.pY_nB b) b (d.nB_j0 b),
    fun c => mem_NI_hyp d _ (d.nC_jX c) (d.pY_nC c) 0 (by rw [d.nC_j0, Matrix.mul_zero, add_zero])⟩

end GlobalTheory.Bridge

end
