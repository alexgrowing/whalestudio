import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

noncomputable section

namespace Formalism.MainNotions.ThetaNormsAndLinks

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

structure MetX {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} (G : LiftErrorLocal.GeoX Lc) where

  Pts : Lc.Pt Lc.Xm → Lc.Unim → Type

  nAt : ∀ y La n, Lc.Sn y La n → Pts y La → ℝ

  nrm_def : ∀ y La n s, IsLUB (Set.range (nAt y La n s)) (G.nrm y La n s)

  mulP : ∀ y La, Pts y La → Pts y La
  mulP_surjective : ∀ y La, Function.Surjective (mulP y La)

  trP : ∀ y La n, Lc.Th y La n → Equiv.Perm (Pts y La)

  Fo : ∀ y La, Set (Pts y La)

namespace MetX

variable {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} {G : LiftErrorLocal.GeoX Lc} (M : MetX G)

def I1 : Prop := ∀ y La x, M.nAt y La 1 (Lc.vth y La 1) x ≤ 1

def I2 : Prop := ∀ y La n (s : Lc.Sn y La n) x,
  M.nAt y La (p * n) (G.pull y La n s) x = M.nAt y La n s (M.mulP y La x)

def I3 : Prop := ∀ y La n, ∃ c : Lc.Th y La n →* ℝ, (∀ γ, 0 < c γ) ∧
  ∀ γ (s : Lc.Sn y La n) x, M.nAt y La n (Lc.act y La n γ s) x = c γ * M.nAt y La n s (M.trP y La n γ x)

def I4 : Prop := ∀ y La n (s : Lc.Sn y La n), (∀ x ∈ M.Fo y La, M.nAt y La n s x ≤ 1) →
  ∀ DF, Lc.jet y La n DF s ∈ Lc.intJet y La n DF

def All : Prop := M.I1 ∧ M.I2 ∧ M.I3 ∧ M.I4

end MetX

structure QPack {D : D7} {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) (y : Lc.Pt Lc.Xm) where
  A : Type
  [rA : CommRing A]
  th : A →+* (Lc.fld y).C
  th_range : ∀ c : (Lc.fld y).C, ‖c‖ ≤ 1 ↔ c ∈ th.range
  xi : A
  nu : A
  th_nu : ‖th nu‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1))
  TA : Type
  [aT : AddCommGroup TA]
  [mT : Module A TA]
  M : Type
  [aM : AddCommGroup M]
  [mM : Module A M]
  iT : Lc.Tp y →+ TA
  iT_span : Submodule.span A (Set.range iT) = ⊤
  i : TA →ₗ[A] M
  k : M →ₗ[A] TA
  ik : ∀ m, i (k m) = (xi * nu) • m
  ki : ∀ t, k (i t) = (xi * nu) • t
  tf : ∀ m : M, xi • m = 0 → m = 0
  FilM : Submodule A M
  red : FilM →+ Lc.OmV y
  red_smul : ∀ (a : A) (m : FilM), red (a • m) = th a • red m
  red_range : ∀ v, v ∈ Lc.om y ↔ ∃ m, red m = v
  i_mem : ∀ t, i t ∈ FilM
  ht_eq : ∀ t, Lc.ht y t = red ⟨i (iT t), i_mem (iT t)⟩
  k_Fil : ∀ m ∈ FilM, ∃ t, k m = xi • t

attribute [instance] QPack.rA QPack.aT QPack.mT QPack.aM QPack.mM

structure Loc8 {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) where

  mg : ∀ d i, MetX (X.gx d i)
  mc : ∀ N i, MetX (X.cmx N i)

  DatK : ∀ i j b, Set (D.nexp.Dat i j b)

def Loc8.ThK {D : D7} {nch : NChoice D} {X : LiftErrorLocal.Loc D nch} (Z : Loc8 X) (w : LiftErrorLocal.Pl D) (j : ℕ) (b : Bool) :
    Submodule (D.ntw.O (nch.twI w)) (D.nexp.Fm (nch.twI w) j b) :=
  IntegralHeckeForms.Th D.nexp (nch.twI w) j b (Z.DatK (nch.twI w) j b)

def dK (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : ℝ := (LiftErrorLocal.rkK (D.nexp.Bsup i j b) : ℝ)

def d0 (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : ℝ :=
  (Module.finrank (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Fm0 D.nexp i j b) : ℝ)

def dG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : ℕ :=
  Module.finrank (FractionRing (D.ntw.O i)) (IntegralHeckeForms.V0 D.nexp i j b)

def eSh (D : D7) : ℝ := (((D.R.f : ℝ) * D.R.k) ^ 3)⁻¹ / 4

section Int

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def IntAt (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (la : HeightOneSpectrum (𝓞 X.B.KO)) (wt : WeightFamilies.Wt D j)
    (N : Submodule (𝓞 X.B.KO) (X.B.Cusp j wt)) : Prop :=
  ∀ F ∈ N, ∀ y : (X.W j h1 h2).Pt la, 0 ≤ (X.W j h1 h2).vAt la y ((X.W j h1 h2).inc wt F)

def Int4 (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (la : HeightOneSpectrum (𝓞 X.B.KO)) : Prop :=
  IntAt X j h1 h2 la (X.run j).wL ((X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL) ∧
  IntAt X j h1 h2 la (X.run j).wF ((X.W j h1 h2).Thc (X.run j).S.sF (X.run j).wF) ∧
  IntAt X j h1 h2 la ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF)
    ((X.W j h1 h2).Thc (X.run j).S.s0 ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF)) ∧
  IntAt X j h1 h2 la (X.run j).ka ((X.W j h1 h2).Thc (X.run j).S.sK (X.run j).ka)

def laDiv (n : ℕ) (la : HeightOneSpectrum (𝓞 X.B.KO)) : Prop := ((n : ℕ) : 𝓞 X.B.KO) ∈ la.asIdeal

end Int

section admitted

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X)

def admissible_unitary_of_inputs : Prop := (∀ d i, (Z.mg d i).All) ∧ ∀ N i, (Z.mc N i).All

def SandwichExists : Prop := (∀ d (i : Fin 2) (y : (X.P6.loc d (D.host.g i)).Pt (X.P6.loc d (D.host.g i)).Xm),
    Nonempty (QPack (X.P6.loc d (D.host.g i)) y)) ∧
  ∀ N i (y : (X.cm N i).Pt (X.cm N i).Xm), Nonempty (QPack (X.cm N i) y)

def TransferenceTheoremCond : Prop := WeightFamilies.TransferenceTheoremCond

def CharacterRankDiscriminant (CRd : ℝ) : Prop := ∀ d (i : Fin 2) (Z : (X.P6.loc d (D.host.g i)).Mdl) (y : (X.P6.loc d (D.host.g i)).Pt Z),
  (((X.P6.loc d (D.host.g i)).dP y : ℕ) : ℝ) ^ 2 ≤ WeightFamilies.RRv D (CRd - 2)

def MirabolicIndexCond : Prop := ∃ tableDegreeThreeBase : Subgroup (G0g D.nd), D.nexp.U ≤ tableDegreeThreeBase ∧
  (Nat.card tableDegreeThreeBase : ℝ) = LiftErrorLocal.delq D * (Nat.card D.nexp.U : ℝ) ∧
  ∀ (i : D.ntw.Tw) (b : Bool) (h : G0g D.nd), h ∈ tableDegreeThreeBase → h ∉ D.nexp.U →
    ∃ (u : D.nexp.U) (hu : h⁻¹ * (u : G0g D.nd) * h ∈ D.nexp.U),
      D.nexp.psiU i b u ≠ D.nexp.psiU i b ⟨h⁻¹ * (u : G0g D.nd) * h, hu⟩

def admR (C : NChoice D) : Prop := ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (1 - eSh D) * dK D (C.twI w) j b ≤ (Nat.card D.nexp.U : ℝ) * d0 D (C.twI w) j b

def admG2 : Prop := (1 - eSh D) * (Nat.card D.nexp.U : ℝ) ≤ LiftErrorLocal.delq D

def BadRowShareBound (C : NChoice D) : Prop := ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  d0 D (C.twI w) j b - (dG D (C.twI w) j b : ℝ) ≤
    Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * d0 D (C.twI w) j b

def EqualGoodMultiplicities (C : NChoice D) : Prop := ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  dG D (C.twI w) j b = D.what₂.D0

def admA : Prop := PDVN.ConjugationNormInvariance D

def SupLatticeGroupStable : Prop := ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (g : G0g D.nd),
  (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤ D.nexp.Bsup i j b

def SupSpansPsiPart : Prop := ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
  Submodule.span (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Mall D.nexp i j b : Set (D.nexp.Fm i j b)) = IntegralHeckeForms.Fm0 D.nexp i j b

def SupStableOffPairs : Prop := ∀ (i : D.ntw.Tw), ¬ D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (g : G0g D.nd),
  (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤ D.nexp.Bsup i j b

def SupSpansOffPairs : Prop := ∀ (i : D.ntw.Tw), ¬ D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
  Submodule.span (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Mall D.nexp i j b : Set (D.nexp.Fm i j b)) = IntegralHeckeForms.Fm0 D.nexp i j b

def AdditiveCharacterIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la → Int4 X j h1 h2 la

def ScalingIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  laDiv X (2 * (NumberField.discr D.host.E).natAbs) la → Int4 X j h1 h2 la

def CrudeIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  laDiv X (D.host.pde * D.host.pde') la → Int4 X j h1 h2 la

def ThetaLevelPrimeIntegrality : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  ¬ laDiv X (2 * (NumberField.discr D.host.E).natAbs * D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') la →
    Int4 X j h1 h2 la

def MLatticeCond : Prop := WeightFamilies.adm1 X.B

def admT4 : Prop := (∀ i0 w, LiftErrorLocal.Over D i0 w → D.ntw.NonzeroIndexPlace (nch.twI w)) ∧ IntegralHeckeForms.adm7 D X.I.E

def NormDecompositionCond : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  ∃ c : Bool → D.ntw.O (nch.twI w), (∀ b, c b ≠ 0) ∧
    (∑ b : Bool, LiftErrorLocal.vDv (D.ntw.O (nch.twI w)) (D.ntw.l (nch.twI w)) (c b)) = (LiftErrorLocal.Dpm D j : ℝ) ∧
    ∀ b, ∀ x ∈ X.ThN w j h1 h2 b, ∃ z ∈ Z.ThK w j b, x = c b • z

def ThetaKGroupStable : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool, LiftErrorLocal.GStab (Z.ThK w j b)

def ThetaKEquivariantData : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ x ∈ LiftErrorLocal.psiPart (Z.ThK w j b), ((Nat.card D.nexp.U : ℕ) : D.ntw.O (nch.twI w)) • x ∈ X.Th0 w j b

def WeightGeneratorsInLattice : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
  ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
    s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def RunColumnChoices : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m →
  (X.run j).nW = (X.run j).n1 + (X.run j).n2 ∧
  ∀ i0 la, X.laOver i0 la →
    (X.run j).nus la = (eWL X.B.KO la : ℝ) * (WeightAlgebra.DF (X.run j).wL : ℝ) / ((D.host.g i0 : ℝ) - 1)

def ScalarSizeConditions (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  WeightAlgebra.ParA L H.CA ∧
  WeightAlgebra.SetC L (X.W j h1 h2) H.CK H.C1 H.A1 (X.run j).ka (X.run j).wL (X.run j).wF X.TO (X.run j).nP (X.run j).nW
    (X.run j).h0 ∧
  WeightAlgebra.H3 L H C2 A2 CR 0 (X.run j).wL X.TO ∧ (X.TO : ℝ) ≤ L.sc.x ^ CT ∧
  ∀ i0, X.RangeB CRd i0 (X.run j).wL (X.run j).n1 (X.run j).n2 ∧ 2 * WeightAlgebra.DF (X.run j).ka + 2 < D.host.g i0 ∧
    X.cB CRd i0 j (WeightAlgebra.DF (X.run j).wL) (X.run j).nW ≤ WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL

def FurtherSizeConditions (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  WeightAlgebra.H4 L (X.W j h1 h2) H C2 A2 CR (X.run j).ka (X.run j).wL (X.run j).wF X.TO (X.run j).nW

def GlobalScalarBounds (H : WeightAlgebra.KHyp) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  WeightAlgebra.ScalB L (X.W j h1 h2) H.C1 H.A1 (X.run j).S (X.run j).ka (X.run j).wL (X.run j).wF X.TO

def RegularityOffTypePrimes (H : WeightAlgebra.KHyp) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (∀ la, 0 ≤ (X.run j).nus la) ∧ (Function.support (X.run j).nus).Finite ∧
  (∑ᶠ la, |(X.run j).nus la| * (X.W j h1 h2).lN la) ≤ WeightAlgebra.PN D L * (X.run j).wL.size ∧
  ∀ la, (∀ i0, ¬ X.laOver i0 la) → ∀ y : (X.W j h1 h2).Pt la,
    (X.W j h1 h2).depth (X.run j).S.sW (X.run j).wL la y ≤
      (((X.run j).nus la + WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL * (X.W j h1 h2).phiC la y : ℝ) : EReal)

end admitted

section Conclusion₂

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def Conclusion1 : Prop := (∀ d i, (X.gx d i).INT) ∧ ∀ N i, (X.cmx N i).INT

def Conclusion2 : Prop := (∀ d (i : Fin 2), LiftErrorLocal.HTb (X.P6.loc d (D.host.g i))) ∧ ∀ N i, LiftErrorLocal.HTb (X.cm N i)

def CoveringRadiusFunction (CRd : ℝ) : Prop := ∀ d (i : Fin 2), LiftErrorLocal.PhiB (X.P6.loc d (D.host.g i)) CRd

def Conclusion5 (C : NChoice D) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (C.twI w)) (D.nexp.Fm (C.twI w) j b),
    B1.FG → B2 ≤ B1 → LiftErrorLocal.spK B2 = LiftErrorLocal.spK B1 → LiftErrorLocal.GStab B1 → LiftErrorLocal.GStab B2 →
    LiftErrorLocal.delq D * LiftErrorLocal.lenQ (D.ntw.l (C.twI w)) (LiftErrorLocal.psiPart B1) (LiftErrorLocal.psiPart B2) ≤
      LiftErrorLocal.lenQ (D.ntw.l (C.twI w)) B1 B2 + (LiftErrorLocal.rkK B1 : ℝ) * LiftErrorLocal.vU D (C.twI w)

def Conclusion6 (C : NChoice D) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (LiftErrorLocal.rkK (D.nexp.Bsup (C.twI w) j b) : ℝ) / LiftErrorLocal.delq D ≤
                 2 * (Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.V0 D.nexp (C.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (C.twI w) j b).map (IntegralHeckeForms.AO D.nexp (C.twI w) j b) ≤ D.nexp.Bsup (C.twI w) j b

def ShareLatticeRanks (C : NChoice D) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  LiftErrorLocal.rkK (IntegralHeckeForms.Mall D.nexp (C.twI w) j b) =
                 Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) ∧
    LiftErrorLocal.rkK (LiftErrorLocal.Mj D (C.twI w) j b) = D.what₂.D0

def GGEveryPlace (C : NChoice D) : Prop := ∀ w, PDVN.GGAt D C w

def ShareEveryPlace (C : NChoice D) : Prop := ∀ w, PDVN.SHAt D C w

def ShareRankEveryPlace (C : NChoice D) : Prop := ∀ w, PDVN.SHbAt D C w

def ScaledGeneratorsInSup : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL ≤ X.B.Mlat j (X.run j).wL ∧
  (X.W j h1 h2).Thc (X.run j).S.sF (X.run j).wF ≤ X.B.Mlat j (X.run j).wF ∧
  (X.W j h1 h2).Thc (X.run j).S.s0 ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF) ≤
    X.B.Mlat j ((X.W j h1 h2).wF0 (X.run j).wL (X.run j).wF) ∧
  (X.W j h1 h2).Thc (X.run j).S.sK (X.run j).ka ≤ X.B.Mlat j (X.run j).ka

def LinkLatticesEveryPlace : Prop := ∀ w, PDVN.LKAt X w

def LinkConditions : Prop :=
  (∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    (∀ b : Bool, (D.nexp.Bsup (nch.twI w) j b).FG ∧ LiftErrorLocal.GStab (D.nexp.Bsup (nch.twI w) j b) ∧
      X.ThN w j h1 h2 b ≤ D.nexp.Bsup (nch.twI w) j b ∧
      IntegralHeckeForms.InclAt D.nexp (nch.twI w) j b (X.I.E.Dat0 (nch.twI w) j b) (nch.k' w) ∅ 1) ∧
    ∃ c : Bool → D.ntw.O (nch.twI w), (∀ b, c b ≠ 0) ∧
      (∑ b : Bool, LiftErrorLocal.vDv (D.ntw.O (nch.twI w)) (D.ntw.l (nch.twI w)) (c b)) = (LiftErrorLocal.Dpm D j : ℝ) ∧
      ∀ b, ∀ x ∈ LiftErrorLocal.psiPart (LiftErrorLocal.GSpan (X.ThN w j h1 h2 b)), ∃ z ∈ X.Th0 w j b,
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (nch.twI w)) • x = c b • z) ∧
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
    ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
      s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def RunConditions (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (X.run j).nW = (X.run j).n1 + (X.run j).n2 ∧
  (∀ i0, X.RangeB CRd i0 (X.run j).wL (X.run j).n1 (X.run j).n2 ∧ 2 * WeightAlgebra.DF (X.run j).ka + 2 < D.host.g i0 ∧
    X.cB CRd i0 j (WeightAlgebra.DF (X.run j).wL) (X.run j).nW ≤ WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL ∧
    ∀ la, X.laOver i0 la →
      (X.run j).nus la = (eWL X.B.KO la : ℝ) * (WeightAlgebra.DF (X.run j).wL : ℝ) / ((D.host.g i0 : ℝ) - 1)) ∧
  ((∀ i0 la, X.laOver i0 la → ∀ y : (X.W j h1 h2).Pt la,
      (X.W j h1 h2).depth (X.run j).S.sW (X.run j).wL la y ≤
        (((X.run j).nus la + WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL * (X.W j h1 h2).phiC la y : ℝ) : EReal)) →
    WeightAlgebra.Hyp L (X.W j h1 h2) H C2 A2 CR 0 CT (X.run j).S (X.run j).ka (X.run j).wL (X.run j).wF X.TO
      (X.run j).nP (X.run j).nW (X.run j).h0 (X.run j).nus)

end Conclusion₂

section Joint

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

theorem joint1 : Conclusion1 D X = LiftErrorLocal.adm1 D X := rfl
theorem joint2 : Conclusion2 D X = LiftErrorLocal.adm2 D X := rfl
theorem joint3b (CRd : ℝ) : CoveringRadiusFunction D X CRd = LiftErrorLocal.adm3b D X CRd := rfl
theorem joint5 : Conclusion5 D nch = LiftErrorLocal.adm5 D nch := rfl
theorem joint6 : Conclusion6 D nch = LiftErrorLocal.adm6 D nch := rfl
theorem joint6b : ShareLatticeRanks D nch = LiftErrorLocal.TorsionSectionsReflex D nch := rfl
theorem linkConditions_eq : LinkConditions D X = LiftErrorLocal.adm10 D X := rfl
theorem runConditions_eq (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) :
    RunConditions D L X H C2 A2 CR CT CRd = LiftErrorLocal.adm11 D L X H C2 A2 CR CT CRd := rfl

theorem gg_of_everyPlace (C : NChoice D) (h : GGEveryPlace D C) : Conclusion5 D C := fun _ w _ => h w
theorem share_of_everyPlace (C : NChoice D) (h : ShareEveryPlace D C) : Conclusion6 D C := fun _ w _ => h w
theorem shareRank_of_everyPlace (C : NChoice D) (h : ShareRankEveryPlace D C) : ShareLatticeRanks D C := fun _ w _ => h w

theorem offTypePrime_of {Xd : DivX D} (O : PDVN.ONObj D nch Xd) (h5 : GGEveryPlace D nch) (h6 : ShareEveryPlace D nch) (h6b : ShareRankEveryPlace D nch)
    (hL : LinkLatticesEveryPlace D O.X) (hL' : LinkLatticesEveryPlace D O.X') : PDVN.OffTypePrimeConditions O :=
  fun w _ _ => ⟨h5 w, h6 w, h6b w, fun _ => hL w, fun _ => hL' w⟩

theorem supGroupStable_of (E : IntegralHeckeForms.XD D) (h : IntegralHeckeForms.adm3 D E) (hO : SupStableOffPairs D) : SupLatticeGroupStable D := fun i j hj b g => by
  by_cases hi : D.ntw.NonzeroIndexPlace i
  · exact (h i hi j hj b).1 g
  · exact hO i hi j hj b g
theorem supSpans_of (E : IntegralHeckeForms.XD D) (h : IntegralHeckeForms.adm3 D E) (hO : SupSpansOffPairs D) : SupSpansPsiPart D := fun i j hj b => by
  by_cases hi : D.ntw.NonzeroIndexPlace i
  · exact (h i hi j hj b).2.2.1
  · exact hO i hi j hj b

end Joint

section Stmt

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X)

def IntegralityFromMetric : Prop := admissible_unitary_of_inputs D X Z → Conclusion1 D X

def HodgeTateFromSandwich : Prop := SandwichExists D X → Conclusion2 D X

def CoveringRadiusFromTransference (CRd : ℝ) : Prop := TransferenceTheoremCond → CharacterRankDiscriminant D X CRd → 2 ≤ CRd → CoveringRadiusFunction D X CRd

def GGFromIrreducibility (C : NChoice D) : Prop := MirabolicIndexCond D → GGEveryPlace D C

def ShareFromInputs (C : NChoice D) : Prop :=
  admR D C ∧ admG2 D ∧ BadRowShareBound D L C ∧ EqualGoodMultiplicities D C ∧ admA D ∧ SupLatticeGroupStable D → ShareEveryPlace D C

def ShareRankFromInputs (C : NChoice D) : Prop := SupSpansPsiPart D ∧ EqualGoodMultiplicities D C → ShareRankEveryPlace D C

def ScaledGeneratorsIntegral : Prop := AdditiveCharacterIntegrality D X ∧ ScalingIntegrality D X ∧ CrudeIntegrality D X ∧ ThetaLevelPrimeIntegrality D X → ScaledGeneratorsInSup D X

def LinkLatticesFromInputs : Prop := MLatticeCond D X ∧ SupLatticeGroupStable D ∧ ScaledGeneratorsInSup D X → LinkLatticesEveryPlace D X

def LinkFromInputs : Prop :=
  MLatticeCond D X ∧ SupLatticeGroupStable D ∧ ScaledGeneratorsInSup D X ∧ admT4 D X ∧ NormDecompositionCond D X Z ∧ ThetaKGroupStable D X Z ∧ ThetaKEquivariantData D X Z ∧ WeightGeneratorsInLattice D X → LinkConditions D X

def RunFromInputs (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  RunColumnChoices D X ∧ ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ FurtherSizeConditions D L X H C2 A2 CR ∧ GlobalScalarBounds D L X H ∧ RegularityOffTypePrimes D L X H ∧ ScaledGeneratorsInSup D X →
    RunConditions D L X H C2 A2 CR CT CRd

def admitted (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  admissible_unitary_of_inputs D X Z ∧ SandwichExists D X ∧ TransferenceTheoremCond ∧ CharacterRankDiscriminant D X CRd ∧ MirabolicIndexCond D ∧
    (admR D nch ∧ admG2 D ∧ BadRowShareBound D L nch ∧ EqualGoodMultiplicities D nch ∧ admA D ∧ SupLatticeGroupStable D) ∧ SupSpansPsiPart D ∧
    (AdditiveCharacterIntegrality D X ∧ ScalingIntegrality D X ∧ CrudeIntegrality D X ∧ ThetaLevelPrimeIntegrality D X) ∧
    (MLatticeCond D X ∧ admT4 D X ∧ NormDecompositionCond D X Z ∧ ThetaKGroupStable D X Z ∧ ThetaKEquivariantData D X Z ∧ WeightGeneratorsInLattice D X) ∧
    (RunColumnChoices D X ∧ ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ FurtherSizeConditions D L X H C2 A2 CR ∧ GlobalScalarBounds D L X H ∧ RegularityOffTypePrimes D L X H)

def AtEveryPlace : Prop := GGEveryPlace D nch ∧ ShareEveryPlace D nch ∧ ShareRankEveryPlace D nch ∧ LinkLatticesEveryPlace D X

def Conclusion₂ (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  Conclusion1 D X ∧ Conclusion2 D X ∧ CoveringRadiusFunction D X CRd ∧ Conclusion5 D nch ∧ Conclusion6 D nch ∧ ShareLatticeRanks D nch ∧ ScaledGeneratorsInSup D X ∧ LinkConditions D X ∧
    RunConditions D L X H C2 A2 CR CT CRd ∧ AtEveryPlace D X

def Stmt (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  2 ≤ CRd → admitted D L X Z H C2 A2 CR CT CRd → Conclusion₂ D L X H C2 A2 CR CT CRd

end Stmt

theorem MetX.int {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} {G : LiftErrorLocal.GeoX Lc} (M : MetX G) (h : M.All) :
    G.INT := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  intro y La
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (M.nrm_def y La 1 _).2 (by rintro _ ⟨x, rfl⟩; exact h1 y La x)
  · intro n s
    have e : Set.range (M.nAt y La (p * n) (G.pull y La n s)) = Set.range (M.nAt y La n s) := by
      ext t; constructor
      · rintro ⟨x, rfl⟩; exact ⟨M.mulP y La x, (h2 y La n s x).symm⟩
      · rintro ⟨x, rfl⟩
        obtain ⟨x', rfl⟩ := M.mulP_surjective y La x
        exact ⟨x', h2 y La n s x'⟩
    exact IsLUB.unique (M.nrm_def y La (p * n) _) (e ▸ M.nrm_def y La n s)
  · rintro n γ s ⟨k, hk, hγ⟩
    obtain ⟨c, hc, hcs⟩ := h3 y La n
    have c1 : c γ = 1 := by
      have : c γ ^ k = 1 := by rw [← map_pow, hγ, map_one]
      exact (pow_eq_one_iff_of_nonneg (hc γ).le hk.ne').1 this
    have e : Set.range (M.nAt y La n (Lc.act y La n γ s)) = Set.range (M.nAt y La n s) := by
      ext t; constructor
      · rintro ⟨x, rfl⟩; exact ⟨M.trP y La n γ x, by rw [hcs, c1, one_mul]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨(M.trP y La n γ).symm x, by rw [hcs, c1, one_mul, Equiv.apply_symm_apply]⟩
    exact IsLUB.unique (M.nrm_def y La n _) (e ▸ M.nrm_def y La n s)
  · intro n s hs DF
    exact h4 y La n s (fun x _ => ((M.nrm_def y La n s).1 ⟨x, rfl⟩).trans hs) DF

theorem stmt1 (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X) : IntegralityFromMetric D X Z :=
  fun h => ⟨fun d i => (Z.mg d i).int (h.1 d i), fun N i => (Z.mc N i).int (h.2 N i)⟩

theorem ospan_smul {C V : Type} [NormedField C] [AddCommGroup V] [Module C V] {S : Set V} {a : C}
    (ha : ‖a‖ ≤ 1) {v : V} (hv : v ∈ ModuliIntegralCharts.Ospan (C := C) S) : a • v ∈ ModuliIntegralCharts.Ospan (C := C) S := by
  unfold ModuliIntegralCharts.Ospan at *
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb, s, hs,
      by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem QPack.htb_at {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} {y : Lc.Pt Lc.Xm} (Q : QPack Lc y) :
    ModuliIntegralCharts.Ospan (C := (Lc.fld y).C) (Set.range (Lc.ht y)) ≤ Lc.om y ∧
    ∀ x ∈ Lc.om y, ∀ c : (Lc.fld y).C, ‖c‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) →
      c • x ∈ ModuliIntegralCharts.Ospan (C := (Lc.fld y).C) (Set.range (Lc.ht y)) := by
  have key : ∀ t : Q.TA, Q.red ⟨Q.i t, Q.i_mem t⟩ ∈ ModuliIntegralCharts.Ospan (C := (Lc.fld y).C) (Set.range (Lc.ht y)) := by
    intro t
    have ht : t ∈ Submodule.span Q.A (Set.range Q.iT) := by rw [Q.iT_span]; trivial
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      rw [← Q.ht_eq]
      exact AddSubgroup.subset_closure ⟨1, by simp, _, ⟨s, rfl⟩, by simp⟩
    | zero =>
      have : (⟨Q.i 0, Q.i_mem 0⟩ : Q.FilM) = 0 := Subtype.ext (map_zero _)
      rw [this, map_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (⟨Q.i (a + b), Q.i_mem _⟩ : Q.FilM) = ⟨Q.i a, Q.i_mem a⟩ + ⟨Q.i b, Q.i_mem b⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [this, map_add]; exact add_mem ha hb
    | smul a x _ hx =>
      have : (⟨Q.i (a • x), Q.i_mem _⟩ : Q.FilM) = a • ⟨Q.i x, Q.i_mem x⟩ := Subtype.ext (map_smul _ _ _)
      rw [this, Q.red_smul]; exact ospan_smul ((Q.th_range _).2 ⟨a, rfl⟩) hx
  constructor
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨t, rfl⟩, rfl⟩
    obtain ⟨a', rfl⟩ := (Q.th_range a).1 ha
    rw [Q.ht_eq, ← Q.red_smul]
    exact (Q.red_range _).2 ⟨_, rfl⟩
  · intro x hx c hc
    obtain ⟨m, rfl⟩ := (Q.red_range x).1 hx
    obtain ⟨t, ht⟩ := Q.k_Fil m.1 m.2
    have h1 : Q.nu • m.1 = Q.i t := by
      have : Q.xi • (Q.nu • m.1 - Q.i t) = 0 := by
        rw [smul_sub, smul_smul, ← Q.ik, ht, map_smul, sub_self]
      exact sub_eq_zero.1 (Q.tf _ this)
    by_cases h0 : Q.th Q.nu = 0
    · have : c = 0 := by
        rw [← Q.th_nu, h0, norm_zero] at hc; exact norm_le_zero_iff.1 hc
      rw [this, zero_smul]; exact zero_mem _
    · have hc' : ‖c / Q.th Q.nu‖ ≤ 1 := by
        rw [norm_div]; exact div_le_one_of_le₀ (by rw [Q.th_nu]; exact hc) (norm_nonneg _)
      obtain ⟨a, ha⟩ := (Q.th_range _).1 hc'
      have e : c = Q.th (a * Q.nu) := by rw [map_mul, ha, div_mul_cancel₀ _ h0]
      rw [e, ← Q.red_smul]
      have : ((a * Q.nu) • m : Q.FilM) = ⟨Q.i (a • t), Q.i_mem _⟩ := Subtype.ext (by
        show (a * Q.nu) • m.1 = Q.i (a • t)
        rw [mul_smul, h1, map_smul])
      rw [this]; exact key _

theorem stmt2 (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : HodgeTateFromSandwich D X :=
  fun h => ⟨fun d i y => (h.1 d i y).elim fun Q => Q.htb_at, fun N i y => (h.2 N i y).elim fun Q => Q.htb_at⟩

theorem integral_all_places (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)
    (h : AdditiveCharacterIntegrality D X ∧ ScalingIntegrality D X ∧ CrudeIntegrality D X ∧ ThetaLevelPrimeIntegrality D X) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (la : HeightOneSpectrum (𝓞 X.B.KO)) : Int4 X j h1 h2 la := by
  obtain ⟨hg, hr, ho, he⟩ := h
  by_cases hd : laDiv X (2 * (NumberField.discr D.host.E).natAbs * D.host.g 0 * D.host.g 1 * D.host.pde *
      D.host.pde') la
  · have hp := la.isPrime
    unfold laDiv at hd
    push_cast at hd
    rcases hp.mem_or_mem hd with hd | hd
    · rcases hp.mem_or_mem hd with hd | hd
      · rcases hp.mem_or_mem hd with hd | hd
        · rcases hp.mem_or_mem hd with hd | hd
          · exact hr j h1 h2 la (by unfold laDiv; push_cast; exact hd)
          · exact hg j h1 h2 0 la hd
        · exact hg j h1 h2 1 la hd
      · exact ho j h1 h2 la (by unfold laDiv; push_cast; exact Ideal.mul_mem_right _ _ hd)
    · exact ho j h1 h2 la (by unfold laDiv; push_cast; exact Ideal.mul_mem_left _ _ hd)
  · exact he j h1 h2 la hd

theorem stmtS (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : ScaledGeneratorsIntegral D X := by
  intro h j h1 h2
  have H := fun la => integral_all_places D X h j h1 h2 la
  refine ⟨fun F hF => ?_, fun F hF => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · exact ((X.W j h1 h2).Mlat_eq _ F).2 fun la y => (H la).1 F hF y
  · exact ((X.W j h1 h2).Mlat_eq _ F).2 fun la y => (H la).2.1 F hF y
  · exact ((X.W j h1 h2).Mlat_eq _ F).2 fun la y => (H la).2.2.1 F hF y
  · exact ((X.W j h1 h2).Mlat_eq _ F).2 fun la y => (H la).2.2.2 F hF y

theorem run_conditions_holds (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (H : WeightAlgebra.KHyp)
    (C2 A2 CR CT CRd : ℝ) : RunFromInputs D L X H C2 A2 CR CT CRd := by
  rintro ⟨hc, hn, h4, hs, hd, hS⟩ j h1 h2
  obtain ⟨c1, c2⟩ := hc j h1 h2
  obtain ⟨nA, nC, n3, nT, nR⟩ := hn j h1 h2
  obtain ⟨d0, d1, d2, d3⟩ := hd j h1 h2
  refine ⟨c1, fun i0 => ⟨(nR i0).1, (nR i0).2.1, (nR i0).2.2, c2 i0⟩, fun hg =>
    ⟨nA, nC, hs j h1 h2, ⟨d0, d1, d2, fun la y => ?_⟩, hS j h1 h2, n3, h4 j h1 h2, nT⟩⟩
  by_cases h : ∃ i0, X.laOver i0 la
  · obtain ⟨i0, hi⟩ := h; exact hg i0 la hi y
  · exact d3 la (not_exists.1 h) y

theorem eSh_nonneg (D : D7) : 0 ≤ eSh D := by unfold eSh; positivity

theorem eSh_le (D : D7) : eSh D ≤ 1 / 4 := by
  unfold eSh
  have : (((D.R.f : ℝ) * D.R.k) ^ 3)⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos (D.R.f * D.R.k) with h | h
    · have h' : ((D.R.f : ℝ) * D.R.k) = 0 := by exact_mod_cast h
      rw [h']; simp
    · have h' : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.k := by exact_mod_cast h
      exact inv_le_one_of_one_le₀ (one_le_pow₀ h')
  linarith

theorem zO_mem (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (hS : ∀ g : G0g D.nd, (D.nexp.Bsup i j b).map
      ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤ D.nexp.Bsup i j b)
    (z : MonoidAlgebra (D.ntw.O i) (G0g D.nd)) (x : D.nexp.Fm i j b) (hx : x ∈ D.nexp.Bsup i j b) :
    IntegralHeckeForms.zO D.nexp i j b z x ∈ D.nexp.Bsup i j b := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp [IntegralHeckeForms.zO, MonoidAlgebra.map_zero]
  | add f g hf hg =>
    have : IntegralHeckeForms.zO D.nexp i j b (f + g) x = IntegralHeckeForms.zO D.nexp i j b f x + IntegralHeckeForms.zO D.nexp i j b g x := by
      simp [IntegralHeckeForms.zO, MonoidAlgebra.map_add]
    rw [this]; exact add_mem hf hg
  | single g a =>
    have : IntegralHeckeForms.zO D.nexp i j b (MonoidAlgebra.single g a) x = a • (D.nexp.actG i j b g x) := by
      simp [IntegralHeckeForms.zO, MonoidAlgebra.map_single, MonoidAlgebra.lift_single]
    rw [this]; exact Submodule.smul_mem _ _ (hS g ⟨x, hx, rfl⟩)

theorem stmt6 (D : D7) (L : SizeData₂ D) (C : NChoice D) : ShareFromInputs D L C := by
  rintro ⟨hR, hG, hB, hT, hA, hS⟩ w j hj b
  have e0 := eSh_nonneg D
  have e1 := eSh_le D
  have r := hR w j hj b
  have bd := hB w j hj b
  have tr := hT w j hj b
  have k0 : 0 ≤ dK D (C.twI w) j b := Nat.cast_nonneg _
  have z0 : 0 ≤ d0 D (C.twI w) j b := Nat.cast_nonneg _
  refine ⟨?_, tr, ?_, ?_⟩
  · change dK D (C.twI w) j b / LiftErrorLocal.delq D ≤ 2 * d0 D (C.twI w) j b
    rcases le_or_gt (LiftErrorLocal.delq D) 0 with hδ | hδ
    · exact (div_nonpos_of_nonneg_of_nonpos k0 hδ).trans (by positivity)
    · rw [div_le_iff₀ hδ]
      have a1 : (1 - eSh D) * ((1 - eSh D) * dK D (C.twI w) j b) ≤
          (1 - eSh D) * ((Nat.card D.nexp.U : ℝ) * d0 D (C.twI w) j b) :=
        mul_le_mul_of_nonneg_left r (by linarith)
      have a2 : ((1 - eSh D) * (Nat.card D.nexp.U : ℝ)) * d0 D (C.twI w) j b ≤ LiftErrorLocal.delq D * d0 D (C.twI w) j b :=
        mul_le_mul_of_nonneg_right hG z0
      have a3 : (1 / 2) * dK D (C.twI w) j b ≤ (1 - eSh D) * ((1 - eSh D) * dK D (C.twI w) j b) := by
        have : (1 / 2 : ℝ) ≤ (1 - eSh D) * (1 - eSh D) := by nlinarith
        calc (1 / 2) * dK D (C.twI w) j b ≤ ((1 - eSh D) * (1 - eSh D)) * dK D (C.twI w) j b :=
              mul_le_mul_of_nonneg_right this k0
          _ = _ := by ring
      nlinarith
  · change d0 D (C.twI w) j b ≤ 2 * (D.what₂.D0 : ℝ)
    have hx : (1 : ℝ) ≤ L.sc.x ^ (L.sc.ez / 7) :=
      Real.one_le_rpow L.sc.one_lt_alt.le (by have := L.sc.ez_pos; positivity)
    have hE : Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) ≤ 1 / 2 := by
      have h1 : Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (by norm_num) h2
      exact h1.trans h3
    have : Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * d0 D (C.twI w) j b ≤ (1 / 2) * d0 D (C.twI w) j b :=
      mul_le_mul_of_nonneg_right hE z0
    have tr' : (dG D (C.twI w) j b : ℝ) = (D.what₂.D0 : ℝ) := by exact_mod_cast tr
    linarith
  · obtain ⟨c, hc⟩ := hA.1 (C.twI w) b
    rintro _ ⟨x, hx, rfl⟩
    have : IntegralHeckeForms.AO D.nexp (C.twI w) j b x = IntegralHeckeForms.zO D.nexp (C.twI w) j b c x := by
      simp only [IntegralHeckeForms.AO, IntegralHeckeForms.zO, IntegralHeckeForms.eO, IntegralHeckeForms.eG, hc, LinearMap.smul_apply, LinearMap.coe_restrictScalars,
        Nat.cast_smul_eq_nsmul]
      rw [map_nsmul, LinearMap.smul_apply]
    rw [this]
    exact zO_mem D _ j b (fun g => hS _ j hj b g) c x hx

theorem eG_comm (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (g : G0g D.nd) (x : D.nexp.Fm i j b) :
    D.nexp.actG i j b g (IntegralHeckeForms.eG D.nexp i j b x) = IntegralHeckeForms.eG D.nexp i j b (D.nexp.actG i j b g x) := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
    (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
    (D.nexp.eAlg_central i b (MonoidAlgebra.single g 1))
  rw [map_mul, map_mul, MonoidAlgebra.lift_single, one_smul] at h
  have h2 := congrArg (fun f => f x) h
  exact h2.symm

theorem hermFramePairNormalForm_frameSpan_le_of_generators (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : IntegralHeckeForms.V0 D.nexp i j b ≤ IntegralHeckeForms.Fm0 D.nexp i j b := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [IntegralHeckeForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, SetLike.mem_coe, LinearEquiv.coe_coe] at hy ⊢
  intro u
  rw [eG_comm, hy u, map_smul]

theorem span_Mj (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (hS : Submodule.span (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Mall D.nexp i j b : Set (D.nexp.Fm i j b)) =
      IntegralHeckeForms.Fm0 D.nexp i j b) : LiftErrorLocal.spK (LiftErrorLocal.Mj D i j b) = IntegralHeckeForms.V0 D.nexp i j b := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => hx.2
  · intro x hx
    have h1 : x ∈ Submodule.span (FractionRing (D.ntw.O i)) (IntegralHeckeForms.Mall D.nexp i j b : Set (D.nexp.Fm i j b)) := by
      rw [hS]; exact hermFramePairNormalForm_frameSpan_le_of_generators D i j b hx
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (D.ntw.O i))).1 h1
    rw [Submodule.span_eq] at hy
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hy, ?_⟩)
    have := Submodule.smul_mem (IntegralHeckeForms.V0 D.nexp i j b) (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) z) hx
    rwa [smul_smul, IsLocalization.mk'_spec', map_one, one_smul] at this

theorem stmt6b (D : D7) (C : NChoice D) : ShareRankFromInputs D C := by
  rintro ⟨hS, hT⟩ w j hj b
  refine ⟨?_, ?_⟩
  · unfold LiftErrorLocal.rkK LiftErrorLocal.spK
    rw [hS _ j hj b]
  · unfold LiftErrorLocal.rkK
    rw [span_Mj D _ j b (hS _ j hj b)]
    exact hT w j hj b

theorem vAdd_nonneg_int {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    0 ≤ vAdd la (a : K) := by
  unfold vAdd
  have h := la.valuation_le_one (K := K) a
  by_cases h0 : la.valuation K (a : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h
    simp at this
    omega

section Forms

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (W : WeightAlgebra.PJ D B P j)

def HomI (f : W.Forms) : Prop := (∃ w H, f = W.inc w H) ∧ ∀ la (y : W.Pt la), 0 ≤ W.vAt la y f

def SI : AddSubmonoid W.Forms := AddSubmonoid.closure {f | HomI W f}

theorem SI_int {f : W.Forms} (hf : f ∈ SI W) : ∀ la (y : W.Pt la), 0 ≤ W.vAt la y f := by
  unfold SI at hf
  induction hf using AddSubmonoid.closure_induction with
  | mem x hx => exact hx.2
  | zero => intro la y; rw [W.vAt_zero]; exact le_top
  | add x y _ _ hx hy => intro la z; exact (le_min (hx la z) (hy la z)).trans (W.vAt_add la z x y)

theorem HomI_mul {f g : W.Forms} (hf : HomI W f) (hg : HomI W g) : HomI W (f * g) := by
  obtain ⟨⟨w, F, rfl⟩, h1⟩ := hf
  obtain ⟨⟨w', G, rfl⟩, h2⟩ := hg
  refine ⟨?_, fun la y => ?_⟩
  · obtain ⟨H, hH⟩ := W.inc_mul w w' F G
    exact ⟨_, H, hH⟩
  · rw [W.vAt_mul]; exact add_nonneg (h1 la y) (h2 la y)

theorem SI_mul {f g : W.Forms} (hf : HomI W f) (hg : g ∈ SI W) : f * g ∈ SI W := by
  unfold SI at *
  induction hg using AddSubmonoid.closure_induction with
  | mem x hx => exact AddSubmonoid.subset_closure (HomI_mul W hf hx)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy

theorem emb_HomI {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} (hN : N ≤ B.Mlat j w) {f : W.Forms}
    (hf : f ∈ W.emb w N) : HomI W f := by
  obtain ⟨F, hF, rfl⟩ := hf
  exact ⟨⟨w, F, rfl⟩, (W.Mlat_eq w F).1 (hN hF)⟩

theorem pow_mul_SI {w w' : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)}
    {N' : Submodule (𝓞 B.KO) (B.Cusp j w')} (hN : N ≤ B.Mlat j w) (hN' : N' ≤ B.Mlat j w') (n : ℕ) :
    ∀ f ∈ W.emb w N ^ n * W.emb w' N', f ∈ SI W := by
  induction n with
  | zero =>
    intro f hf
    rw [pow_zero, one_mul] at hf
    exact AddSubmonoid.subset_closure (emb_HomI W hN' hf)
  | succ n ih =>
    intro f hf
    rw [pow_succ', mul_assoc] at hf
    induction hf using Submodule.mul_induction_on' with
    | mem_mul_mem a ha g hg => exact SI_mul W (emb_HomI W hN ha) (ih g hg)
    | add x _ y _ hx hy => exact add_mem hx hy

end Forms

theorem twOK_one (D : D7) (i : D.ntw.Tw) (k : ℕ) :
    IntegralHeckeForms.TwOK (X := D.ntw) i k ∅ (1 : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) := by
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_one]; exact isOpen_univ
  · intro g g' _; simp
  · intro g; simp [one_mem]
  · intro v A hA; simp
  · intro v _ A' _ σ _; rfl

theorem stmtLK (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : LinkLatticesFromInputs D X := by
  rintro ⟨hM, hG, hS⟩ w j h1 h2 b
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [X.toFm_sup w j b h1 h2]
    obtain ⟨S, hS'⟩ := (hM j h1 h2 (X.run j).ka).fg
    have : Submodule.span (D.ntw.O (nch.twI w)) (X.toFm w j b '' (X.B.Mlat j (X.run j).ka : Set _)) =
        Submodule.span (D.ntw.O (nch.twI w)) (X.toFm w j b '' (S : Set _)) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨F, hF, rfl⟩
        rw [SetLike.mem_coe, ← hS'] at hF
        induction hF using Submodule.span_induction with
        | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul a x _ hx =>
          obtain ⟨o, ho⟩ := (X.embK_int w b (a : X.B.KO)).1 (vAdd_nonneg_int _ a)
          have : X.toFm w j b (a • x) = o • X.toFm w j b x := by
            rw [← algebraMap_smul X.B.KO a x, map_smulₛₗ, ← algebraMap_smul (FractionRing (D.ntw.O (nch.twI w))) o, ho]
          rw [SetLike.mem_coe, this]; exact Submodule.smul_mem _ _ hx
      · refine Submodule.span_mono (Set.image_mono ?_)
        rw [← hS']; exact Submodule.subset_span
    rw [this]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · intro g x hx
    exact hG _ j (Finset.mem_Icc.2 ⟨h1, h2⟩) b g ⟨x, hx, rfl⟩
  · rw [X.toFm_sup w j b h1 h2]
    refine Submodule.span_mono (Set.image_mono ?_)
    intro F hF
    obtain ⟨s1, s2, s3, s4⟩ := hS j h1 h2
    refine ((X.W j h1 h2).Mlat_eq _ F).2 (SI_int (X.W j h1 h2) ?_)
    obtain ⟨pq, hpq, r, hr, e⟩ := Submodule.mem_sup.1 hF
    obtain ⟨p, hp, q, hq, e'⟩ := Submodule.mem_sup.1 hpq
    rw [← e, ← e']
    exact add_mem (add_mem (pow_mul_SI _ s1 s2 _ p hp) (pow_mul_SI _ s1 s3 _ q hq))
      (AddSubmonoid.subset_closure (emb_HomI _ s4 hr))

theorem link_from_inputs_holds (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X) : LinkFromInputs D X Z := by
  rintro ⟨hM, hG, hS, hT, hN, hK, hDt, hW⟩
  have hLK := stmtLK D X ⟨hM, hG, hS⟩
  refine ⟨fun i0 w hw j h1 h2 => ⟨fun b => ⟨(hLK w j h1 h2 b).1, (hLK w j h1 h2 b).2.1, (hLK w j h1 h2 b).2.2, ?_⟩, ?_⟩, hW⟩
  · exact Submodule.map_mono (hT.2 _ (hT.1 i0 w hw) j (Finset.mem_Icc.2 ⟨h1, h2⟩) b _ ∅ 1 (twOK_one D _ _) _ subset_rfl)
  · obtain ⟨c, c0, cv, cN⟩ := hN i0 w hw j h1 h2
    have hj : j ∈ LiftErrorLocal.lifts D := Finset.mem_Icc.2 ⟨h1, h2⟩
    refine ⟨c, c0, cv, fun b x hx => ?_⟩
    have hle : LiftErrorLocal.GSpan (X.ThN w j h1 h2 b) ≤
        (Z.ThK w j b).map (c b • (LinearMap.id : D.nexp.Fm (nch.twI w) j b →ₗ[D.ntw.O (nch.twI w)] _)) := by
      refine iSup_le fun g => ?_
      rintro _ ⟨n, hn, rfl⟩
      obtain ⟨z, hz, rfl⟩ := cN b n hn
      refine ⟨D.nexp.actG (nch.twI w) j b g z, hK i0 w hw j hj b g z hz, ?_⟩
      simp
    obtain ⟨z, hz, rfl⟩ := hle hx.1
    have hz0 : z ∈ IntegralHeckeForms.Fm0 D.nexp (nch.twI w) j b := by
      have h2' : (c b • z) ∈ IntegralHeckeForms.Fm0 D.nexp (nch.twI w) j b := by simpa using hx.2
      have hc : algebraMap (D.ntw.O (nch.twI w)) (FractionRing (D.ntw.O (nch.twI w))) (c b) ≠ 0 := by
        simpa using (c0 b)
      have := Submodule.smul_mem _ (algebraMap (D.ntw.O (nch.twI w)) (FractionRing (D.ntw.O (nch.twI w))) (c b))⁻¹ h2'
      rwa [← algebraMap_smul (FractionRing (D.ntw.O (nch.twI w))) (c b) z, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    refine ⟨_, hDt i0 w hw j hj b z ⟨hz, hz0⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [smul_comm]

theorem stmt_of (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X) (H : WeightAlgebra.KHyp)
    (C2 A2 CR CT CRd : ℝ) (h3 : CoveringRadiusFromTransference D X CRd) (h5 : GGFromIrreducibility D nch) : Stmt D L X Z H C2 A2 CR CT CRd := by
  rintro hC ⟨aI, aQ, aB, aRk, aG, a6, aSp, aS, ⟨aM, aT4, aNN, aK, aD, aW⟩, ⟨aRc, aRn, aR4, aRs, aRd⟩⟩
  have hS := stmtS D X aS
  have p5 := h5 aG
  have p6 := stmt6 D L nch a6
  have p6b := stmt6b D nch ⟨aSp, a6.2.2.2.1⟩
  exact ⟨stmt1 D X Z aI, stmt2 D X aQ, h3 aB aRk hC, gg_of_everyPlace D nch p5, share_of_everyPlace D nch p6, shareRank_of_everyPlace D nch p6b, hS,
    link_from_inputs_holds D X Z ⟨aM, a6.2.2.2.2.2, hS, aT4, aNN, aK, aD, aW⟩,
    run_conditions_holds D L X H C2 A2 CR CT CRd ⟨aRc, aRn, aR4, aRs, aRd, hS⟩,
    p5, p6, p6b, stmtLK D X ⟨aM, a6.2.2.2.2.2, hS⟩⟩

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc8 (XF x hx i))

def AdmF (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    admitted (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd

def ConclusionOnFamily (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    Conclusion₂ (Fm.D x i) (Fm.L x i) (XF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd

def AdmLAF : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    admissible_unitary_of_inputs (Fm.D x i) (XF x hx i) (ZF x hx i) ∧ SandwichExists (Fm.D x i) (XF x hx i)

def FamilyConclusionLA : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i) (XF x hx i) ∧ Conclusion2 (Fm.D x i) (XF x hx i)

theorem jointLAF : FamilyConclusionLA Fm XF = LiftErrorLocal.AdmLAF Fm XF := rfl

theorem stmtLAF (h : AdmLAF Fm XF ZF) : FamilyConclusionLA Fm XF := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h0 i => ⟨stmt1 _ _ _ (h x hx h0 i).1, stmt2 _ _ (h x hx h0 i).2⟩⟩

end Fam

def KudlaFamilyStatement (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
    (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc8 (XF x hx i)),
    AdmF Fm XF ZF H C2h A2 CR CRd → ConclusionOnFamily Fm XF H C2h A2 CR CRd

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ), 2 ≤ CRd → KudlaFamilyStatement H C2h A2 CR CRd Fm CH)

theorem familyStatement_of_pointwise {H : WeightAlgebra.KHyp} {C2h A2 CR CRd : ℝ} (hC : 2 ≤ CRd)
    (h : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (X : LiftErrorLocal.Loc D nch) (Z : Loc8 X) (CT : ℝ),
      Stmt D L X Z H C2h A2 CR CT CRd) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CH : ℝ) :
    KudlaFamilyStatement H C2h A2 CR CRd Fm CH := by
  rintro XF ZF ⟨x0, h0⟩
  exact ⟨x0, fun x hx hx0 i => h _ _ _ _ _ _ hC (h0 x hx hx0 i)⟩

theorem closedStatement_of_pointwise (𝒞 : Formalism.MainNotions.FamClass)
    (h : ∀ (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ), 2 ≤ CRd → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (X : LiftErrorLocal.Loc D nch)
      (Z : Loc8 X) (CT : ℝ), Stmt D L X Z H C2h A2 CR CT CRd) : ClosedAbsoluteShare 𝒞 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ H C2h A2 CR CRd hC =>
    familyStatement_of_pointwise hC (h H C2h A2 CR CRd hC) Fm CH⟩⟩

end Formalism.MainNotions.ThetaNormsAndLinks

end
