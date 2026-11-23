import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem qC_eq (q : ℚ_[l]) : qC l q = algebraMap ℚ_[l] ℂ_[l] q :=
  (IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l] q).symm

theorem th_alg (x : Formalism.Per6.BdRp l) : period_ring_base.th l (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) x) = Formalism.Per6.θD l x := by
  have h : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) x ∈ period_ring_base.Plus l := ⟨x, rfl⟩
  rw [period_ring_base.th, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (RingHom.mem_range.1 h).choose_spec)

theorem th_qQ (q : ℚ_[l]) : period_ring_base.th l (qQ l q) = qC l q := ((period_ring_base.base l).th_q q).2.trans (qC_eq q).symm

theorem θA_zA (z : ℤ_[l]) : θA l (zA l z) = qC l (z : ℚ_[l]) := by
  have e : ACris.iota ℂ_[l] l (zA l z) = algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (z : ℚ_[l]) := ACris.iota_padicInt z
  exact (congrArg (Formalism.Per6.θD l) e).trans ((th_alg _).symm.trans (th_qQ _))

theorem σC_qC (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (q : ℚ_[l]) : period_ring_base.σC g (qC l q) = qC l q := by
  rw [← th_qQ, ← (period_ring_base.base l).th_σ g _ ((period_ring_base.base l).th_q q).1, σD_qQ]

theorem χ_ne (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : period_ring_base.χ g ≠ 0 := by
  intro h0
  have h1 := σD_tQ (l := l) g
  rw [h0, map_zero, zero_mul, map_eq_zero_iff _ (Formalism.Per6.σD g).injective] at h1
  exact DeRhamTwist.Twist.tQ_ne h1

theorem sSup_pb {X X' : Scheme.{0}} (D : E.LineData X) (f : X' ⟶ X) (h : sSup (Pb.𝒱D D) = ⊤) : sSup (Pb.𝒱D (D.pb f)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : f x ∈ sSup (Pb.𝒱D D) := h ▸ trivial
  obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  refine TopologicalSpace.Opens.mem_sSup.2 ⟨f ⁻¹ᵁ V, ⟨pullback.lift ((f ∣_ V) ≫ σ) (f ⁻¹ᵁ V).ι ?_, ?_⟩, hV⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact pullback.lift_snd _ _ _

theorem proper_q {M : Model l K} (h : M.Sm) : IsProper M.q := by
  have := AdicGeo.proper_p h.1
  infer_instance

theorem smooth_q {M : Model l K} (h : M.Sm) : Smooth M.q := by
  have := h.2
  infer_instance

end CrystallineSemistableComparison.HT
