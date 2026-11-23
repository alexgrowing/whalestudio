import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapSurjectiveSkew
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_map_surjective_skew : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → GoodForm S σ H → 1 ≤ k → ∀ Y : Matrix n n (Res S ϖ), Y ∈ skewTr S σ H ϖ → ∃ g ∈ congSU S σ H ϖ k, levMap S ϖ k (g : Matrix n n A) = Y := by
  first | exact @GlobalTheory.SUCong.levSurj | exact GlobalTheory.SUCong.levSurj | (intros; apply GlobalTheory.SUCong.levSurj <;> assumption)
