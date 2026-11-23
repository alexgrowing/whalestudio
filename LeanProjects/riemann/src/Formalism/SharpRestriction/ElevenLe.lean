import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

variable {D : D7} (L : SizeData₂ D)

def szTh : ℝ := L.sc.eps / 100

def szNst : ℝ := 2 * (D.R.n : ℝ) * L.sc.delta1

def szlA : ℝ := (D.R.k : ℝ) * L.sc.x ^ L.sc.eps / ((D.R.m : ℝ) * L.de2)

def szlStar : ℝ :=
  (D.R.m : ℝ) * L.sc.b /
    ((D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L))

def szCond (_L : SizeData₂ D) : ℝ := (D.host.QS : ℝ) * D.host.q * D.host.d

def SizeN : Prop :=
  L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L)

def SizeM : Prop :=
  L.sc.x ^ (-szTh L) * Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ) ∧
    (D.R.m : ℝ) ≤ L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)

def SizeK : Prop :=
  L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) ≤ (D.R.k : ℝ) ∧
    (D.R.k : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps + szTh L)

def SizeKRel : Prop :=
  L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps ≤ D.R.k ∧
  8 * L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L ≤ D.R.k ∧
  (D.R.k : ℝ) ≤ Real.sqrt L.sc.x * D.R.n * rankBudget D.R L.sc.x L.sc.eps ∧
  Real.sqrt ((D.R.k : ℝ) / D.R.m) ≤ rankBudget D.R L.sc.x L.sc.eps ∧
  (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k ∧
  (D.R.m : ℝ) * Real.sqrt L.sc.x * Real.log L.sc.x ≤ D.R.k ∧
  L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 6 * L.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 3 * L.sc.L * Real.log D.host.rdE ≤ (D.R.k : ℝ) * Real.log D.R.k ^ 2 ∧
  Real.log D.R.f ≤ Real.sqrt D.R.rS ∧
  Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L ∧
  L.sc.x ^ szTh L * Real.log (Real.log L.sc.b) ≤ (D.R.r : ℝ) * D.R.f * Real.log D.R.r ∧
  L.sc.x ^ szTh L * L.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k ∧
  (D.R.f : ℝ) ≤ (D.R.m : ℝ) ^ 2 * D.R.n ∧
  (D.R.f : ℝ) ≤ (D.R.r : ℝ) ^ 2

def SizeT : Prop :=
  1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ L.sc.x ^ (L.Ct + szTh L)

def SizeCond : Prop := szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b

def SizeQD : Prop :=
  L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q ∧
  L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ Real.log D.host.q ∧
  Real.log D.host.q ≤ L.sc.x ^ (L.sc.eps / 5 + szTh L) ∧
  L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ Real.log D.host.d ∧
  Real.log D.host.d ≤ L.sc.x ^ (L.sc.eps / 5 + szTh L) ∧
  |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps ∧
  1 ≤ D.host.rdE ∧ D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)

def SizeTT : Prop :=
  L.sc.x ^ (-szTh L) * D.R.n * L.sc.delta1 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ szNst L

def SizeLa : Prop := L.sc.x ^ L.sc.eps ≤ L.LaG ∧ L.LaG ≤ L.sc.x ^ (L.sc.eps + szTh L)

def SizeRho : Prop :=
  4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k + L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤
    L.sc.x ^ (-2 : ℝ)

def SizeBot : Prop :=
  ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k

def SizeDe2 : Prop := L.sc.x ^ (-L.sc.eps) ≤ L.de2

def SizeLw : Prop := (D.host.Lw : ℝ) ≤ Real.log L.sc.x ^ 2

def SizeEta : Prop :=
  (D.R.t : ℝ) ≤ L.etaSz ∧
  L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) ∧
  Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4) ∧
  (D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x ∧
  (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧
  (D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L ∧
  (D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ∧
  L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2 ∧
  (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * szlA L ≤ L.de2 * D.R.m * L.sc.b

def SizeNodes : Prop :=
  12 * L.sc.b / szlStar L + 2 * D.R.t + 8 ≤ L.etaSz / D.R.m ∧
  (D.R.k : ℝ) * D.R.t * L.sc.L ≤ L.etaSz / D.R.m ∧
  L.sc.x ^ szTh L * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ L.etaSz / D.R.m ∧
  4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ L.etaSz / D.R.m ∧
  L.sc.x ^ szTh L * D.R.k * (D.R.m : ℝ) ^ (9 / 2 : ℝ) ≤ L.etaSz / D.R.m ∧
  2 * ((D.R.r : ℝ) + D.R.m * D.R.t) ^ 3 + D.R.t + 3 ≤ L.etaSz / D.R.m ∧
  (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ L.etaSz / D.R.m

def SizeLstar : Prop :=
  L.sc.b' + L.Sc + L.etaSz + L.sc.b / szlStar L < szlStar L ∧
  2 * L.etaSz + D.R.t + 8 * L.sc.b / szlStar L + 7 < szlStar L

def SizeDel : Prop :=
  (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) ∧
  L.sc.x ^ szTh L * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧
  Real.log (D.s.Del : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) / 2 ∧
  (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
  L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n ∧
  4 * L.Sc ≤ L.LaG * L.sc.b' / D.R.k ∧
  4 * L.sc.x ^ szTh L * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b' ∧
  L.sc.x ^ szTh L * D.R.m * Real.log D.host.v ≤ D.R.k

def SizeW : Prop := Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n

def SizeBm (_L : SizeData₂ D) : Prop :=
  ∀ τ (h : 0 < D.R.m), (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) ≤ 2 * (((D.hc τ).b ⟨0, h⟩ : ℚ) : ℝ)

def SizeXpp : Prop :=
  ∀ j τ j' τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ'

def SizeG : Prop :=
  ∀ i j : Fin 2, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * (D.host.g j : ℝ) ∧
    Real.log (D.host.g i : ℝ) ≤ L.sc.x ^ szTh L * L.sc.L

def SizeTu : Prop := ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ L.sc.x ^ szTh L * D.R.m * L.sc.L

def SizePde : Prop :=
  Real.log (D.host.pde : ℝ) ≤ L.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ L.sc.L

def SizeWords (_L : SizeData₂ D) : Prop := @Fintype.card D.what₂.Word D.wordFin ≤ 2 ^ (D.R.k - 3)

def SizesAt : Prop :=
  SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeKRel L ∧ SizeT L ∧ SizeCond L ∧ SizeQD L ∧ SizeTT L ∧
  SizeLa L ∧ SizeRho L ∧ SizeBot L ∧ SizeDe2 L ∧ SizeLw L ∧ SizeEta L ∧ SizeNodes L ∧
  SizeLstar L ∧ SizeDel L ∧ SizeW L ∧ SizeBm L ∧ SizeXpp L ∧ SizeG L ∧ SizePde L ∧
  SizeWords L ∧ 11 ≤ D.host.splitBound

theorem SizesAt.eleven_le {D : D7} {L : SizeData₂ D} (S : SizesAt L) : 11 ≤ D.host.splitBound :=
  S.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Formalism.MainNotions

end
