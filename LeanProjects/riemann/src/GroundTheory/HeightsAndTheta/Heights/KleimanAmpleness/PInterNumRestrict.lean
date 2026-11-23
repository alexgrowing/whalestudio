import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumRestrict

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem inr_foldl_restrict {n : ℕ} (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y)
    (rr : Fin n → Ω → K') (hL : ∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (rr i)) :
    ∀ (l : List (Fin n)) (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∃ (P : LineBundle k x) (P' : LineBundle k y) (s : Ω → K'),
        l.foldl (fun F i => F.twist (L i).toSubSystem) Q.toSubSystem = P.toSubSystem ∧
        l.foldl (fun F i => F.twist (L' i).toSubSystem) Q'.toSubSystem = P'.toSubSystem ∧
        RestrictData P.toSubSystem hxy P'.toSubSystem s
  | [], Q, Q', r, h => ⟨Q, Q', r, rfl, rfl, h⟩
  | i :: l, Q, Q', r, h => by
    obtain ⟨s, hs⟩ := RestrictTwist.proof.2 k Ω N x K' y hxy Q (L i) Q' (L' i) r (rr i) h (hL i)
    exact inr_foldl_restrict L L' rr hL l (Q.tensorProd (L i)) (Q'.tensorProd (L' i)) s hs

theorem proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle pp n hsub L L' rr hL
  have hT : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      restrLen pp ((tensorSub (fun i => (L' i).toSubSystem) T).twist (twistSys k y (c : ℤ))) =
        restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) := by
    intro T
    obtain ⟨r0, h0⟩ := RestrictTwist.proof.1 k Ω N x K' y hxy hle 0
    obtain ⟨P, P', s, hP, hP', hs⟩ := inr_foldl_restrict L L' rr hL
      ((List.finRange n).filter (· ∈ T)) (twistBundle k x 0) (twistBundle k y 0) r0 h0
    have e1 : tensorSub (fun i => (L i).toSubSystem) T = P.toSubSystem := hP
    have e2 : tensorSub (fun i => (L' i).toSubSystem) T = P'.toSubSystem := hP'
    rw [e1, e2]
    exact hRL k Ω N x K' y hxy hle pp n hsub P P' s hs
  have hall : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L' i).toSubSystem) c =
      interSum pp (fun i => (L i).toSubSystem) c := by
    filter_upwards [Filter.eventually_all.2 hT] with c hc
    unfold interSum
    exact Finset.sum_congr rfl fun T _ => by rw [hc T]
  unfold interNum limUnder
  rw [Filter.map_congr hall]

end InterNumRestrict

end

end GroundTheory.Heights₂.Heights.Kleiman
