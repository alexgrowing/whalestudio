import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLListProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProductCuspidalGL_list_properties : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ L n, IsCl (J θ L n)) ∧ (∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' → J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n) ∧ ∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L → L.Perm L' → J θ L n = J θ L' n := by
  first | (exact @GlobalTheory.Shin.J_list_props) | (exact GlobalTheory.Shin.J_list_props) | (intros; apply GlobalTheory.Shin.J_list_props <;> assumption)
