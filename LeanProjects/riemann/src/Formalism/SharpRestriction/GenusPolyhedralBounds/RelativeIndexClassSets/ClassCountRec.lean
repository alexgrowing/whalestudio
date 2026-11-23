import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCount
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ParOfEqBase
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FibreRankGat
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup

noncomputable section

namespace Formalism.MainNotions.Gaps.CC

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab Formalism.MainNotions.StandardLattice Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

structure ClsTie (D : D7) where

  pz : D.what₂.Word → 𝓞 D.host.E

  piG : Fin 2 → 𝓞 D.host.E
  hyp : ∀ u, LevHyp D.host (D.mem u).A.T (pz u) piG

  P : D.what₂.Word → Par D.host.F D.host.E D.R.k
  charpoly_eq_of_isIso : ∀ u, P u = hostPar D.host (D.mem u).A.T (pz u) piG
  S : ∀ u, (P u).Splits
  e : ∀ u, (D.mem u).C.cls 0 ≃ (P u).Cls (S u)

section Rec

variable {D : D7}

theorem massI_eq (M : ℕ) : massI D M = massH D.host M := rfl

theorem card_classes_level_zero (X : ClsTie D) (u : D.what₂.Word) :
    (Nat.card ((D.mem u).C.cls 0) : ℝ) =
      massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  rw [Nat.card_congr (X.e u), classCount_par D.host (D.mem u).A.T (X.pz u) X.piG (X.hyp u) (X.P u) (X.charpoly_eq_of_isIso u) (X.S u)]
  rfl

theorem class_number_of_class_data (X : ClsTie D) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := fun _ _ u _ => card_classes_level_zero X u

theorem trivial_stabilisers_of_step_zero (Lv : LevelData D) (hst : ∀ u, (D.mem u).C.StabZero) : SmallOrderPrimeLogSumBound D Lv := fun _ u => hst u

theorem forms_rank_of_class_data (X : ClsTie D) (Lv : LevelData D) (hst : ∀ u, (D.mem u).C.StabZero) : Conclusion4f D Lv :=
  level_rank_of_trivial_stabilisers D Lv (trivial_stabilisers_of_step_zero Lv hst) (class_number_of_class_data X Lv)

theorem rankM_of_tie (X : ClsTie D) (hst : ∀ u, (D.mem u).C.StabZero) (hM : ∀ u, Mu0Tie D u) : LinkB.RankM D := by
  intro u
  have h := hM u (hst u)
  have h2 : (D.duS u : ℝ) = (Nat.card ((D.mem u).C.cls 0) : ℝ) * ∏ ρ, dimV (uColR D u ρ) := h
  rw [h2, card_classes_level_zero X u]
  unfold duStarU duStarP
  ring

theorem mu0Tie_of_rank (u : D.what₂.Word) (n : ℕ) (hr : D.duS u = Nat.card ((D.mem u).C.cls 0) * n)
    (hn : (n : ℝ) = ∏ ρ, dimV (uColR D u ρ)) : Mu0Tie D u := by
  intro _
  have h2 : ((D.duS u : ℕ) : ℝ) = (Nat.card ((D.mem u).C.cls 0) : ℝ) * ∏ ρ, dimV (uColR D u ρ) := by
    rw [hr, Nat.cast_mul, hn]
  exact h2

theorem fibreDim_uColR (u : D.what₂.Word) : (FR.fibreDim (D.hcW u) : ℝ) = ∏ ρ, dimV (uColR D u ρ) :=
  FR.fibreDim_eq (D.hcW u)

theorem rankM_of_cls (X : ClsTie D)
    (hr : ∀ u, D.duS u = Nat.card ((D.mem u).C.cls 0) * FR.fibreDim (D.hcW u)) : LinkB.RankM D := by
  intro u
  rw [hr u, Nat.cast_mul, card_classes_level_zero X u, fibreDim_uColR u]
  unfold duStarU duStarP
  ring

theorem rankM_of_cls' (X : ClsTie D)
    (hr : ∀ u, D.duS u = Fintype.card ((D.mem u).C.cls 0) * FR.fibreDim (D.hcW u)) : LinkB.RankM D :=
  rankM_of_cls X fun u => by rw [hr u, Nat.card_eq_fintype_card]

theorem proviso_of_cls (X : ClsTie D) (L : SizeData₂ D)
    (hr : ∀ u, D.duS u = Nat.card ((D.mem u).C.cls 0) * FR.fibreDim (D.hcW u))
    (hDu : FactDuStar D) (hDs : FactDstar D) : ChProviso_at L (Real.exp 1) :=
  proviso_e L (rankM_of_cls X hr) hDu hDs

theorem proviso_of_cls_le (X : ClsTie D) (L : SizeData₂ D)
    (hr : ∀ u, D.duS u = Nat.card ((D.mem u).C.cls 0) * FR.fibreDim (D.hcW u))
    (hDu : FactDuStar D) (hDs : FactDstar D) {C0 : ℝ} (hC : Real.exp 1 ≤ C0) : ChProviso_at L C0 :=
  LinkB.proviso_mono L (Real.exp_pos 1) hC (proviso_of_cls X L hr hDu hDs)

theorem proviso_three (X : ClsTie D) (L : SizeData₂ D)
    (hr : ∀ u, D.duS u = Nat.card ((D.mem u).C.cls 0) * FR.fibreDim (D.hcW u))
    (hDu : FactDuStar D) (hDs : FactDstar D) : ChProviso_at L 3 :=
  proviso_of_cls_le X L hr hDu hDs (by have := Real.exp_one_lt_d9; linarith)

end Rec

section Base

variable {R : Ranks} (H : Host R) (T0 : ℕ) [hT0 : Fact T0.Prime] (pz0 : 𝓞 H.E)
  (hpz0 : (pz0 : H.E) * H.conj (pz0 : H.E) = (T0 : H.E))

theorem card_cls_base (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (hyp : LevHyp H T pz piG)
    (S : (letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz (fun i => H.conj (piG i : H.E))).Splits) :
    (Nat.card ((letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz (fun i => H.conj (piG i : H.E))).Cls S) : ℝ) =
      massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f) * ((T : ℝ) ^ R.k - 1) ^ R.f :=
  classCount_par H T pz piG hyp _ (parOf_eq_base H T0 pz0 hpz0 T pz piG) S

theorem card_clsPkg (X : Type) [Finite X] (d : ℕ) (hd : 0 < d) : Nat.card ((clsPkg X d hd).cls 0) = Nat.card X := rfl

end Base

end Formalism.MainNotions.Gaps.CC

end
