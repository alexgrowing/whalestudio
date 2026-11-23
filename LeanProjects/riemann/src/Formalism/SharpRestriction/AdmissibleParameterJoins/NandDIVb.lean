import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVa
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def RankMj (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0

def ThetaOnto (D : D7) (μ : D.what₂.Tup) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, Function.Surjective (D.what₂.thetaP μ j)

def LocEachLift (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, ∃ i : D.nd.Loc, D.nd.j i = j

theorem RankMj_of_MjRank {D : D7} (X : DivX D)
    (h : ∀ j, 1 ≤ j → j ≤ D.R.m → (X.MjH j).rank = D.what₂.D0) : RankMj D :=
  fun j hj => finrank_Mj X j (h j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)

theorem RankMj_of_isot {D : D7} (hI : Rows.IsotInternal D.what₂) (hR : Rows.IsotRank D.what₂) : RankMj D :=
  fun j hj => finrank_Mj_of_isot D.what₂ hI hR j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

theorem dZ0_eq_D0_of_rankMj_of_thetaOnto {D : D7} (L : SizeData₂ D) (hM : RankMj D) (h : ThetaOnto D D.what₂.mu0) :
    ∀ j ∈ SizeData₂.lifts D, L.dZ0 j = D.what₂.D0 := by
  intro j hj
  unfold SizeData₂.dZ0
  rw [finrank_Zj_of_injective D.what₂ _ j (thetaT_injective_of_onto D.what₂ _ j (h j hj)), hM j hj]

theorem rank_at_place_eq_of_surjective {D : D7} (L : SizeData₂ D) (hM : RankMj D) (w : D.what₂.places.Pl)
    (h : ThetaOnto D (D.what₂.muTw w)) : ∀ j ∈ SizeData₂.lifts D, L.zeroSpaceRankAtPlace j w = D.what₂.D0 := by
  intro j hj
  unfold SizeData₂.zeroSpaceRankAtPlace
  rw [finrank_Zj_of_injective D.what₂ _ j (thetaT_injective_of_onto D.what₂ _ j (h j hj)), hM j hj]

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

theorem rank_at_place_eq_of_scalars {D : D7} (L : SizeData₂ D) (hM : RankMj D) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    L.zeroSpaceRankAtPlace (D.nd.j i) (D.nd.w i) = D.what₂.D0 := by
  have h := theta_injective_of_scalars D h42 hI i hj
  unfold SizeData₂.zeroSpaceRankAtPlace
  rw [← D.nd.mu_w i, finrank_Zj_of_injective D.what₂ _ _ h, hM _ hj]

theorem family_rank_eq_of_surjective {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RankMj (Fm.D x i) ∧ ThetaOnto (Fm.D x i) (Fm.D x i).what₂.mu0) :
    SmallLevelRankEq Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i => dZ0_eq_D0_of_rankMj_of_thetaOnto (Fm.L x i) (h x hx i).1 (h x hx i).2⟩

theorem family_rank_eq_of_scalars {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RankMj (Fm.D x i) ∧ Formalism.MainNotions.SumRepresentations.Conclusion42 (Fm.D x i) ∧
      Rows.IsotInternal (Fm.D x i).what₂ ∧ LocEachLift (Fm.D x i) ∧ Formalism.MainNotions.TwistedPlaces.adm3 (Fm.L x i)) : SmallLevelRankEq Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨x0, fun x hx i j hj => ?_⟩
  obtain ⟨hM, h42, hI, hL, h3⟩ := h x hx i
  obtain ⟨a, rfl⟩ := hL j hj
  rw [← h3 _ hj ((Fm.D x i).nd.w a) ((Fm.D x i).nd.w_tw a)]
  exact rank_at_place_eq_of_scalars (Fm.L x i) hM h42 hI a hj

theorem rank_uniform_over_places {D : D7} (L : SizeData₂ D) (hM : RankMj D) (h : ∀ μ, ThetaOnto D μ) : Formalism.MainNotions.TwistedPlaces.adm3 L := by
  intro j hj w _
  rw [rank_at_place_eq_of_surjective L hM w (h _) j hj, dZ0_eq_D0_of_rankMj_of_thetaOnto L hM (h _) j hj]

end Formalism.MainNotions.J

end
