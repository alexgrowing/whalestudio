import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.YcondFactor

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

structure PreSys (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mu : ℝ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 mu X β) (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (Std : MonH X) where
  ιC : Fin (numSeg X.TT) → Type
  finC : ∀ j, Fintype (ιC j)
  Kc : ∀ j, ιC j → MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)
  dK : ∀ j, ιC j → Fin (2 * segS X.TT j + 1) → ℕ
  pl : ∀ j, ιC j → MonH X
  fC : ∀ j, ιC j → RHH O X
  oC : ∀ j, ιC j → ℕ
  dgC : ∀ j, ιC j → X.TT × Bool → ℕ
  fH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → RHH O X
  oH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ
  dgH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → X.TT × Bool → ℕ
  ιM : Type
  finM : Fintype ιM
  multM : ιM → ℕ
  fM : ιM → RHH O X
  aM : ιM → MonH X
  oM : ιM → ℕ
  dgM : ιM → X.TT × Bool → ℕ
  fR : RHH O X
  R : MonH X
  oR : ℕ
  dR : X.TT × Bool → ℕ

  KInt : ∀ j a, Kc j a ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)
  KPol : ∀ j a, Kc j a ∈ Pol (KK O) X.m (dK j a)
  digit_le_one : ∀ j a i, dK j a i ≤ 1
  dKsum : ∀ j i, ∑ a, dK j a i = (L.LL j).deg i
  Kprod : ∀ j, ∏ a, Kc j a = G j

  facC : ∀ j a, IsFac w (fC j a) (oC j a)
    (monomial (pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc j a)))
  homC : ∀ j a, HomW (ndHom X) (oC j a)
    (monomial (pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc j a)))
  liftC : ∀ j a, lift1 X O w (fC j a) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC j a)
  polC : ∀ j a, monomial (pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc j a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC j a)
  plQ : ∀ j a l, multideg (pl j a) l ≤ X.p ^ X.G'
  plY : ∀ j a j', multideg (pl j a) (topEnd X j', false) = 0

  facH : ∀ j i, IsFac w (fH j i) (oH j i) (ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i))
  homH : ∀ j i, HomW (ndHom X) (oH j i) (ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i))
  liftH : ∀ j i, lift1 X O w (fH j i) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH j i)
  polH : ∀ j i, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH j i)

  facM : ∀ a, IsFac w (fM a) (oM a) (monomial (aM a) 1)
  homM : ∀ a, ndM X (aM a) = oM a
  liftM : ∀ a, lift1 X O w (fM a) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgM a)
  polM : ∀ a l, multideg (aM a) l = dgM a l

  rigA : InA fR
  rigLift : lift1 X O w fR =
    (w ^ oR) • ((∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial R 1)
  rigHom : HomW (ndHom X) oR
    ((∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial R 1)
  rigPol : (∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial R 1 ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dR
  rigInt : InA ((∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) *
    (monomial R 1 : RHH O X))

  dgCQ : ∀ j a l, dgC j a l ≤ X.p ^ X.G'
  dgHQ : ∀ j i l, dgH j i l ≤ X.p ^ X.G'
  dgMQ : ∀ a l, dgM a l ≤ X.p ^ X.G'
  dgCY : ∀ j a j', dgC j a (topEnd X j', false) = 0
  dgHY : ∀ j i j', dgH j i (topEnd X j', false) = 0
  dgMY : ∀ a j', dgM a (topEnd X j', false) = 0
  degEq : ∀ l, dR l + ((∑ j, ∑ a, dgC j a l) + ((∑ j, ∑ i, L.lv j i * dgH j i l) + ∑ a, multM a * dgM a l)) =
    hhDegs X.TT X.aT X.bT l
  stdEq : Std = R + ((∑ j, ∑ a, pl j a) + ∑ a, multM a • aM a)

  clean : ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
    ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 1 →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g'
      (fR * ((∏ j, ∏ a, fC j a) * ((∏ j, ∏ i, fH j i ^ L.lv j i) * ∏ a, fM a ^ multM a)))
      (ordFam C0 CE1 CE2 X β + X.c)
  total : fR * ((∏ j, ∏ a, fC j a) * ((∏ j, ∏ i, fH j i ^ L.lv j i) * ∏ a, fM a ^ multM a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT)
  ordEq : oR + ((∑ j, ∑ a, oC j a) + ((∑ j, ∑ i, L.lv j i * oH j i) + ∑ a, multM a * oM a)) = ordFam C0 CE1 CE2 X β

end Formalism.MainNotions.ColumnSystems.Pf
