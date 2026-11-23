import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import GroundTheory.PAdicHodge.ACrisBdR

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def radN : Subgroup (GlobalTheory.RegSW.stab d) where
  carrier := {q | ∃ (c : skewA D t) (b : Mx D t W.rank), (q : GA D B) = d.nC c * d.nB b}
  mul_mem' := by
    rintro x y ⟨c, b, hx⟩ ⟨c', b', hy⟩
    refine ⟨c + c' + cComm W b b', b + b', ?_⟩
    rw [Subgroup.coe_mul, hx, hy, HypDec.nC_add, HypDec.nC_add]
    calc d.nC c * d.nB b * (d.nC c' * d.nB b')
        = d.nC c * (d.nB b * d.nC c') * d.nB b' := by group
      _ = d.nC c * (d.nC c' * d.nB b) * d.nB b' := by rw [d.nC_mul_nB]
      _ = d.nC c * d.nC c' * (d.nB b * d.nB b') := by group
      _ = d.nC c * d.nC c' * (d.nB (b + b') * d.nC (cComm W b b')) := by rw [d.nB_mul_nB]
      _ = d.nC c * d.nC c' * (d.nC (cComm W b b') * d.nB (b + b')) := by rw [d.nC_mul_nB]
      _ = _ := by group
  one_mem' := ⟨0, 0, by simp [d.nC_zero, d.nB_zero]⟩
  inv_mem' := by
    rintro x ⟨c, b, hx⟩
    refine ⟨-c, -b, ?_⟩
    rw [Subgroup.coe_inv, hx, mul_inv_rev, d.nB_inv, d.nC_inv, d.nC_mul_nB]

def levM : Subgroup (GlobalTheory.RegSW.stab d) where
  carrier := {q | ∃ (g : GA D W) (a : GL (Fin t) (AE D)), (q : GA D B) = d.emb0 g * d.levi a}
  mul_mem' := by
    rintro x y ⟨g, a, hx⟩ ⟨g', a', hy⟩
    refine ⟨g * g', a * a', ?_⟩
    rw [Subgroup.coe_mul, hx, hy, map_mul, map_mul]
    calc d.emb0 g * d.levi a * (d.emb0 g' * d.levi a')
        = d.emb0 g * (d.levi a * d.emb0 g') * d.levi a' := by group
      _ = d.emb0 g * (d.emb0 g' * d.levi a) * d.levi a' := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group
  one_mem' := ⟨1, 1, by simp⟩
  inv_mem' := by
    rintro x ⟨g, a, hx⟩
    refine ⟨g⁻¹, a⁻¹, ?_⟩
    rw [Subgroup.coe_inv, hx, mul_inv_rev, map_inv, map_inv, ← map_inv, ← map_inv, d.wittHyperbolic_anisotropic_commute_levi]

theorem mem_radN {q : GlobalTheory.RegSW.stab d} :
    q ∈ radN d ↔ ∃ (c : skewA D t) (b : Mx D t W.rank), (q : GA D B) = d.nC c * d.nB b := Iff.rfl

theorem mem_levM {q : GlobalTheory.RegSW.stab d} :
    q ∈ levM d ↔ ∃ (g : GA D W) (a : GL (Fin t) (AE D)), (q : GA D B) = d.emb0 g * d.levi a := Iff.rfl

theorem exists_radN_mul_levM (q : GlobalTheory.RegSW.stab d) : ∃ n ∈ radN d, ∃ m ∈ levM d, q = n * m := by
  obtain ⟨b, c, g, e⟩ := GlobalTheory.GodementSectionReduction.exists_decomp d q
  refine ⟨⟨d.nC c * d.nB b, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d c) (GlobalTheory.GodementSectionReduction.nB_mem d b)⟩, ⟨c, b, rfl⟩,
    ⟨d.emb0 g * d.levi (GlobalTheory.RegSW.onX d q), mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d g) (GlobalTheory.RegSW.levi_mem d _)⟩, ⟨g, _, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, e, ← d.nC_mul_nB]
  simp only [mul_assoc]

theorem conj_coord (g : GA D W) (a : GL (Fin t) (AE D)) (c : skewA D t) (b : Mx D t W.rank) :
    (d.emb0 g * d.levi a) * (d.nC c * d.nB b) * (d.emb0 g * d.levi a)⁻¹ =
      d.nC (skewConj a.1 c) * d.nB (a.1 ⬝ b ⬝ mt W g⁻¹) := by
  have h : d.emb0 g * d.levi a * (d.nC c * d.nB b) =
      d.nC (skewConj a.1 c) * d.nB (a.1 ⬝ b ⬝ mt W g⁻¹) * (d.emb0 g * d.levi a) := by
    calc d.emb0 g * d.levi a * (d.nC c * d.nB b)
        = d.emb0 g * (d.levi a * d.nC c) * d.nB b := by group
      _ = d.emb0 g * d.nC (skewConj a.1 c) * (d.levi a * d.nB b) := by rw [d.levi_mul_nC]; group
      _ = d.emb0 g * d.nC (skewConj a.1 c) * (d.nB (a.1 ⬝ b) * d.levi a) := by rw [d.levi_mul_nB]
      _ = d.nC (skewConj a.1 c) * (d.emb0 g * d.nB (a.1 ⬝ b)) * d.levi a := by rw [d.wittHyperbolic_anisotropic_commute_nC]; group
      _ = _ := by rw [d.wittHyperbolic_anisotropic_conj_nB]; group
  rw [h, mul_inv_cancel_right]

instance radN_normal : (radN d).Normal := by
  refine ⟨fun n hn q => ?_⟩
  obtain ⟨n₁, hn₁, m, ⟨g, a, hm⟩, rfl⟩ := exists_radN_mul_levM d q
  obtain ⟨c, b, hc⟩ := hn
  have h : m * n * m⁻¹ ∈ radN d := ⟨skewConj a.1 c, a.1 ⬝ b ⬝ mt W g⁻¹, by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hm, hc, conj_coord]⟩
  have e : n₁ * m * n * (n₁ * m)⁻¹ = n₁ * (m * n * m⁻¹) * n₁⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hn₁ h) (inv_mem hn₁)

end GlobalTheory.CompanionTheory.QKAvg
