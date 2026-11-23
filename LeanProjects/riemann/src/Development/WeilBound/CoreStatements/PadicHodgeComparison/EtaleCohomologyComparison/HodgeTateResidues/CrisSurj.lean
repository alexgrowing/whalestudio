import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ToYIsFirstChernIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.GaloisTTransform
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmoothQ
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.RedInEx
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison.HT

open Pb Pb.Kap PAlg

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

theorem crisSurj : CrisSurj l := fun n => ((RL.base_acr (base l) isBase_base).2 n).1

def thP : period_ring_base.Plus l →+* ℂ_[l] where
  toFun x := period_ring_base.th l x.1
  map_one' := by
    have h := th_alg (l := l) 1
    rw [map_one, map_one] at h
    exact h
  map_mul' x y := (period_ring_base.base l).th_mul _ x.2 _ y.2
  map_zero' := by
    have h := th_alg (l := l) 0
    rw [map_zero, map_zero] at h
    exact h
  map_add' x y := (period_ring_base.base l).th_add _ x.2 _ y.2

theorem θD_algCl (x : PadicAlgCl l) : θD l (algClToBdR l x) = clToC l x := thetaAlgHom_algClToBdR l x

theorem br (ht : TFil l) (hs : CrisSurj l) : Br (per l K) (cb K ht hs) (RingHom.id (Acris l)) (thP l)
    (fun σ => ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (fun σ => galBase (IntermediateField.fixingSubgroupEquiv K σ))
    (fun σ => (period_ring_base.σC σ.1).toRingHom) fun σ => qC l (period_ring_base.χ σ.1) where
  et := rfl
  t_ne := DeRhamTwist.Twist.tQ_ne
  θ_i x := ⟨⟨_, ⟨ACris.iota ℂ_[l] l x, rfl⟩⟩, rfl, th_alg _⟩
  θ_o k := ⟨⟨_, ⟨algClToBdR l k.1, rfl⟩⟩, rfl, (th_alg _).trans (θD_algCl l k.1)⟩
  ker x := ((period_ring_base.base l).th_zero x.1 x.2).trans ⟨fun ⟨y, hy, e⟩ => ⟨⟨y, hy⟩, e⟩, fun ⟨y, e⟩ => ⟨y.1, y.2, e⟩⟩
  θ_σ g x := ⟨⟨_, (period_ring_base.base l).plus_σ g.1 x.1 x.2⟩, rfl, (period_ring_base.base l).th_σ g.1 x.1 x.2⟩
  galois_t_transform g := ⟨⟨_, ((period_ring_base.base l).th_q (period_ring_base.χ g.1)).1⟩, σD_tQ g.1, th_qQ _⟩
  eσ _ _ := rfl
  cris g n x := galBase_cris _ n x

theorem red_ex {m : ℕ} (L : Lev (per l K) m) (hL : L.Good) (hC : L.CrisOK) (n : ℕ) :
    ∃ d : RedIn (B.DD false (base l) n) (B.κb (okToOC l K) false n) L.γ l n,
      ∀ c, d.ρ ((base l).cris n c) = Ideal.Quotient.mk _ (L.lam c) :=
  redIn_ex L.γ m L.lam (hL.lat m le_rfl).tf hC.1 hC.2 n

theorem lvEx_of (h : ∃ S : LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK) : LvEx l K := fun ht hs =>
  h.elim fun S hS => (br l K ht hs).sys S hS.1 fun m n => red_ex l K (S.L m) (hS.1.lev m) (hS.2 m) n

end CrystallineSemistableComparison.HT
