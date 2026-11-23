import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.FcIsUnitSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.MapFrobW
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.NormLLtOne

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.G3

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev kk (r : Res l K) : Wc.K₀ l r.k →+* Formalism.Per6.Bcris l := k₀Lift ((Formalism.Per6.cB l).comp r.w) (period_ring_base.isUnit_l l)

theorem kk_eq (r : Res l K) (w : WittVector l r.k) :
    kk r (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = Formalism.Per6.cB l (r.w w) :=
  IsLocalization.lift_eq _ w

theorem perC_hk (r : Res l K) (w : WittVector l r.k) :
    r.perC.k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = r.perC.c (r.w w) :=
  kk_eq r w

theorem perC_hl (r : Res l K) : IsUnit (r.perC.c (l : (per l K).A)) := by
  show IsUnit (Formalism.Per6.cB l (l : ACris.ACris ℂ_[l] l))
  rw [map_natCast]
  exact period_ring_base.isUnit_l l

theorem k_ext (r : Res l K) {C : Type} [CommRing C] (f g : Wc.K₀ l r.k →+* C)
    (h : ∀ w : WittVector l r.k, f (algebraMap _ (Wc.K₀ l r.k) w) = g (algebraMap _ (Wc.K₀ l r.k) w)) (x : Wc.K₀ l r.k) : f x = g x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (WittVector l r.k)) (RingHom.ext h)) x

theorem frob_alg (r : Res l K) (w : WittVector l r.k) : WittVector.FractionRing.frobeniusRingHom l r.k (algebraMap _ (Wc.K₀ l r.k) w) =
    algebraMap _ (Wc.K₀ l r.k) (WittVector.frobenius w) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (WittVector.frobeniusEquiv l r.k) w

theorem perC_hφk (r : Res l K) (x : Wc.K₀ l r.k) : r.perC.φ (r.perC.k x) = r.perC.k (Wc.frob₀ l r.k x) := by
  have hF := (factsC l K r).1
  refine k_ext r (r.perC.φ.comp r.perC.k) (r.perC.k.comp (WittVector.FractionRing.frobeniusRingHom l r.k)) (fun w => ?_) x
  exact (congrArg r.perC.φ (perC_hk r w)).trans ((hF.φ_c _).trans ((congrArg r.perC.c (w_phi r w)).trans
    ((perC_hk r _).symm.trans (congrArg r.perC.k (frob_alg r w).symm))))

theorem perC_hσk (r : Res l K) [FiniteDimensional ℚ_[l] K] (g : K.fixingSubgroup) (x : Wc.K₀ l r.k) :
    r.perC.σ g (r.perC.k x) = r.perC.k x := by
  have hF := (factsC l K r).1
  refine k_ext r ((r.perC.σ g).comp r.perC.k) r.perC.k (fun w => ?_) x
  exact (congrArg (r.perC.σ g) (perC_hk r w)).trans ((hF.σ_c g _).trans ((congrArg r.perC.c (w_fix r g w)).trans (perC_hk r w).symm))

end CrystallineSemistableComparison.Pb.G3
