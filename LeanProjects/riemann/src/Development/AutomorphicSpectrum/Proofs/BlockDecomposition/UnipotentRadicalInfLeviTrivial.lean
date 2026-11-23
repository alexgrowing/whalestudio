import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem mt_mul_frame {k : ℕ} (x y : GA D B) (J : Mx D B.rank k) :
    mt B (x * y) ⬝ J = mt B x ⬝ (mt B y ⬝ J) := by
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul]

theorem levi_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    {a : GL (Fin t) (AE D)} (e : d.nC c * d.nB b = d.emb0 g * d.levi a) : a = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.jX = mt B (d.emb0 g * d.levi a) ⬝ d.jX := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_jX, d.nC_jX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX] at h
  apply Units.ext
  have h' : d.pX ⬝ d.jX = d.pX ⬝ (d.jX ⬝ a.1) := congrArg (fun M => d.pX ⬝ M) h
  rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h'
  exact h'.symm

theorem unitary_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    (e : d.nC c * d.nB b = d.emb0 g * d.levi 1) : g = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.j0 = mt B (d.emb0 g * d.levi 1) ⬝ d.j0 := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_j0, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, d.nC_j0,
    ← Matrix.mul_assoc, d.nC_jX] at h
  have h' : d.p0 ⬝ (d.j0 + d.jX ⬝ b) = d.p0 ⬝ (d.j0 ⬝ mt W g) := congrArg (fun M => d.p0 ⬝ M) h
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.zero_mul,
    add_zero, Matrix.one_mul] at h'
  apply GlobalTheory.MixModel.mt_injective
  rw [← h', GlobalTheory.MixModel.mt_one]

theorem radN_disj_levM : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  intro D B W t d x hn hm
  obtain ⟨c, b, hx⟩ := (mem_radN d).1 hn
  obtain ⟨g, a, hy⟩ := (mem_levM d).1 hm
  have e : d.nC c * d.nB b = d.emb0 g * d.levi a := hx.symm.trans hy
  have ha := levi_part_eq_one d e
  subst ha
  have hg := unitary_part_eq_one d e
  subst hg
  have h1 : d.emb0 1 * d.levi 1 = 1 := by rw [map_one, map_one, mul_one]
  exact Subtype.ext (hy.trans h1)

end GlobalTheory.CompanionTheory.QKAvg
