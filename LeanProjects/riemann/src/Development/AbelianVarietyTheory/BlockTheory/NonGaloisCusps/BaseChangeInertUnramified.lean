import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeInertUnramified

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Objects

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def SphericalAtInert (B : NBC A) (j : ℕ) (π : B.AU j) : Prop :=
  ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w

structure IsDiscreteSelfDualSum (A : NAut N) (P : List (Part A.CG)) : Prop where

  discrete : ∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d

  selfDual : ∀ p ∈ P, A.csd p.π

  distinct : P.Nodup

structure IsBaseChange (B : NBC A) (j : ℕ) (π : B.AU j) (P : List (Part A.CG)) : Prop where

  parts : IsDiscreteSelfDualSum A P

  rank : rankIso N A P = R.nV

  split : ∀ w : PlE H, IsSplitPl H w → isoLoc N A P w = B.locAU j π w

  inertUnr : ∀ w : PlE H, ¬ IsSplitPl H w → A.unr (isoLoc N A P w)

  inertSat : ∀ w : PlE H, ¬ IsSplitPl H w →
    A.frobEig (isoLoc N A P w) = ubc R.nV (B.satAU j π w)

  infChar : ∀ τ : H.E →+* ℂ, isoInf N A P τ = B.infW j (B.wtAU j π) τ

def BaseChangeExists (B : NBC A) (j : ℕ) : Prop :=
  ∀ π : B.AU j, SphericalAtInert B j π → ∃ P : List (Part A.CG), IsBaseChange B j π P

end Objects

structure Standing (D : D7) (j : ℕ) : Prop where
  cm : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _
  unram : ∀ w : PlE D.host, Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal
  degree : 2 ≤ Module.finrank ℚ D.host.F
  inertOdd : ∀ w : PlE D.host, ¬ IsSplitPl D.host w → (2 : 𝓞 D.host.E) ∉ w.asIdeal
  rank : letI := D.host.cmStar; (D.sp.V j).rank = D.R.nV
  definite : letI := D.host.cmStar; (D.sp.V j).IsDefinite

def AtRecordGuarded (D : D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → Standing D j → BaseChangeExists D.nbc j

def AtRecord (D : D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → BaseChangeExists D.nbc j

def ForFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, AtRecord (Fm.D x i)

def BaseChangeClosed (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ForFamily Fm)

theorem atRecord_iff_guarded (D : D7) (h : ∀ j, 1 ≤ j → j ≤ D.R.m → Standing D j) :
    AtRecord D ↔ AtRecordGuarded D :=
  ⟨fun H j h1 h2 _ => H j h1 h2, fun H j h1 h2 => H j h1 h2 (h j h1 h2)⟩

theorem ubc_map_inv (n : ℕ) (α : Multiset ℂ) : (ubc n α).map (·⁻¹) = ubc n α := by
  unfold ubc
  split_ifs <;> simp [Multiset.map_map, add_comm]

theorem card_ubc (n : ℕ) (α : Multiset ℂ) (h : Multiset.card α = n / 2) : Multiset.card (ubc n α) = n := by
  unfold ubc
  split_ifs with ho
  · obtain ⟨k, rfl⟩ := ho
    simp [h]; omega
  · obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp ho
    simp [h]; omega

theorem isBCV_of_isBaseChange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (B : NBC A) (i : N.Loc) (Q : A.AV i) (P : List (Part A.CG))
    (h : IsBaseChange B (N.j i) (B.embAV i Q) P) : IsBCV N A i Q P := by
  refine ⟨fun p hp => ⟨(h.parts.discrete p hp).1, (h.parts.discrete p hp).2, h.parts.selfDual p hp⟩, ?_,
    h.rank, fun w hw => ?_, fun w hw => ⟨h.inertUnr w hw, ?_⟩, fun τ => ?_⟩
  · refine h.parts.distinct.map ?_
    rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ e
    simp only [Prod.mk.injEq, Sigma.mk.injEq] at e
    obtain ⟨⟨rfl, e2⟩, rfl⟩ := e
    cases e2
    rfl
  · rw [B.embAV_loc]; exact h.split w hw
  · rw [B.embAV_sat]; exact h.inertSat w hw
  · rw [B.embAV_inf]; exact h.infChar τ

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeInertUnramified

end
