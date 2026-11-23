import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

theorem mt_decomp_j0 (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = (d.j0 + d.jX ⬝ b) ⬝ mt W g := by
  have e : mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) =
      mt B (d.nC c) ⬝ (mt B (d.nB b) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a))) := by
    simp only [mt_mul, Matrix.mul_assoc]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.j0 = d.j0 ⬝ mt W g := by
    rw [Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have e₂ : mt B (d.nC c) ⬝ (d.j0 + d.jX ⬝ b) = d.j0 + d.jX ⬝ b := by
    rw [Matrix.mul_add, d.nC_j0, ← Matrix.mul_assoc, d.nC_jX]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc (mt B (d.nB b)), d.nB_j0,
    ← Matrix.mul_assoc, e₂]

theorem mt_decomp_jY (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = (d.jY + d.jX ⬝ c.1) ⬝ adj (a⁻¹).1 := by
  have e : mt B (d.nC c * (d.emb0 g * d.levi a)) = mt B (d.nC c) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a)) := by
    simp only [mt_mul]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.jY = d.jY ⬝ adj (a⁻¹).1 := by
    rw [Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  rw [e, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc, d.nC_jY]

theorem coordB_eq_zero (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = 0) : b = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_j0, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : mt W g ⬝ mt W g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  calc b = b ⬝ mt W g ⬝ mt W g⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem coordC_eq_zero (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = 0) : c = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_jY, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : adj (a⁻¹).1 ⬝ adj a.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  apply Subtype.ext
  calc c.1 = c.1 ⬝ adj (a⁻¹).1 ⬝ adj a.1 := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem pX_levM {q : GlobalTheory.RegSW.stab d} (hq : q ∈ levM d) :
    d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0 ∧ d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0 := by
  obtain ⟨g, a, h⟩ := hq
  rw [h, mt_mul]
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding, d.pX_j0]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc (mt B (d.emb0 g)), d.wittDecomp_anisotropicEmbedding_inclY,
      ← Matrix.mul_assoc, d.pX_jY, Matrix.zero_mul]

theorem mem_levM_of_pX {q : GlobalTheory.RegSW.stab d} (h₀ : d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0)
    (hY : d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0) : q ∈ levM d := by
  obtain ⟨n, ⟨c, b, hn⟩, m, ⟨g, a, hm⟩, e⟩ := exists_radN_mul_levM d q
  have hq : (q : GA D B) = d.nC c * d.nB b * (d.emb0 g * d.levi a) := by
    rw [e, Subgroup.coe_mul, hn, hm]
  rw [hq] at h₀ hY
  have hb := coordB_eq_zero d c b g a h₀
  subst hb
  rw [d.nB_zero, mul_one] at hY
  have hc := coordC_eq_zero d c g a hY
  subst hc
  refine (mem_levM d).2 ⟨g, a, hq.trans ?_⟩
  rw [d.nC_zero, d.nB_zero, one_mul, one_mul]

theorem isClosed_levM (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun q : GlobalTheory.RegSW.stab d => mt B (q : GA D B) :=
    (continuous_mt B).comp continuous_subtype_val
  have h₀ : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have hY : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have e : (levM d : Set (GlobalTheory.RegSW.stab d)) = {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} ∩
      {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    Set.ext fun q => ⟨fun h => pX_levM d h, fun h => mem_levM_of_pX d h.1 h.2⟩
  rw [e]
  exact h₀.inter hY

end GlobalTheory.CompanionTheory.QKAvg
