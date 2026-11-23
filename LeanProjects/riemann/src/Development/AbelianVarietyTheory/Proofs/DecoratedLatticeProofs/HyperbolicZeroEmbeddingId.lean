import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HypZeroTriv

variable {D : D7}

theorem hyperbolic_zero_j0_one (V : HSp D) : (hypZero V).j0 = 1 := by simp [HypDec.j0, hypZero, rat_one]

theorem hyperbolic_zero_embedding_id (V : HSp D) (g : GA D V) : (hypZero V).emb0 g = g := by
  apply mt_injective V
  have h := (hypZero V).wittDecomp_anisotropicEmbedding_inclAnisotropic g
  rwa [hyperbolic_zero_j0_one, Matrix.mul_one, Matrix.one_mul] at h

theorem mem_flagN_hypZero (V : HSp D) {n : GA D V} (hn : n ∈ flagN (hypZero V)) : n = 1 := by
  change n ∈ Formalism.L2.Theta.NFlag V (hypZero V).e at hn
  have hle : Formalism.L2.Theta.NFlag V (hypZero V).e ≤ ⊥ := by
    unfold Formalism.L2.Theta.NFlag
    rw [Subgroup.closure_le]
    rintro g ⟨-, hg⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    have hcol : ∀ j : Fin V.rank, (Formalism.L2.Theta.subOne V g).mulVec (Pi.single j 1) = 0 := by
      intro j
      obtain ⟨a, ha⟩ := hg (Pi.single j 1) (Subsingleton.elim _ _)
      have hr : (Formalism.L2.Theta.ratV (D := D) (Pi.single j (1 : D.host.E))) = Pi.single j 1 := by
        funext k
        by_cases hk : k = j
        · subst hk; simp [Formalism.L2.Theta.ratV]
        · simp [Formalism.L2.Theta.ratV, Pi.single_apply, hk]
      rw [hr] at ha
      rw [ha]
      funext k
      simp [Matrix.mulVec, dotProduct]
    have h0 : Formalism.L2.Theta.subOne V g = 0 := by
      ext k j
      have := congrFun (hcol j) k
      simpa [Matrix.mulVec_single] using this
    apply mt_injective V
    have h1 : Formalism.L2.Theta.mt V g = 1 := by
      have := h0
      unfold Formalism.L2.Theta.subOne at this
      exact sub_eq_zero.1 this
    rw [h1]
    simp [Formalism.L2.Theta.mt]
  exact Subgroup.mem_bot.1 (hle hn)

theorem main : ∀ (D : D7) (V : HSp D), (∀ g, (hypZero V).emb0 g = g) ∧ (∀ n ∈ flagN (hypZero V), n = 1) ∧
    ∀ (A L : HSp D) (o : OrthDec V A L) h, embA (hypZero V) o h = o.emb (h, 1) := by
  intro D V
  refine ⟨hyperbolic_zero_embedding_id V, fun n hn => mem_flagN_hypZero V hn, fun A L o h => ?_⟩
  rw [embA_apply, hyperbolic_zero_embedding_id]

end GlobalTheory.HypZeroTriv

end
