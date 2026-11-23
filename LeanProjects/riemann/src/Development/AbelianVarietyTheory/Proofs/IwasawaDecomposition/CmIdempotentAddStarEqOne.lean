import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : P.D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ P.D χ).choose

theorem isQ_qv : QForm.IsQ P.D.toPre ϖ (qv P hϖ) := fun χ => (QForm.exists_QVal hϖ P.D χ).choose_spec

def beF : LinearMap.BilinForm ℤ P.D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D (isQ_qv P hϖ) a b)
    (fun a a' b => by simp [map_add]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : P.D.toPre.X) : beF P hϖ a b = beF P hϖ b a := QForm.bOf_comm P.D a b

theorem beF_self (a : P.D.toPre.X) : beF P hϖ a a = 2 * qv P hϖ a :=
  (QForm.two_Q_eq hϖ P.D (isQ_qv P hϖ) a).symm

theorem beF_pos {a : P.D.toPre.X} (ha : a ≠ 0) : 0 < beF P hϖ a a := by
  have := QForm.Q_pos hϖ P.D (isQ_qv P hϖ) ha
  rw [beF_self]; omega

theorem beF_adj (x : 𝓞 E) (a b : P.D.toPre.X) : beF P hϖ (x • a) b = beF P hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ P.D GlobalTheory.abelianSchemeLaws_all.1 P.oD (isQ_qv P hϖ) x a b

theorem beF_w0 (a : P.D.toPre.X) : beF P hϖ a (H.w0 • a) = qv P hϖ a := by
  have h₁ := beF_adj P hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm P hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self P hϖ a
  omega

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

def tF (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b))

theorem isScalarForm_tF : letI := H.starRing; IsScalarForm (𝓞 E) (tF P hϖ) := by
  letI := H.starRing
  refine ⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩
  · simp only [tF, map_add, neg_add, zpow_add]
  · rw [tF, tF, beF_symm]
  · rw [tF, tF, beF_adj]; rfl

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist P.D.toPre H.w0 (tF P hϖ)

def oa0 : letI := H.starRing; (D0 P hϖ).OAct (𝓞 E) :=
  letI := H.starRing; twistAct (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.oD

theorem gen0 (a : P.D.toPre.X) : PsiUnitOn (D0 P hϖ) a Set.univ :=
  psiUnitOn_rescale_of_qVal T P.D.toPre ϖ hϖ a (qv P hϖ a) (isQ_qv P hϖ a) _ (by
    show ((piK hϖ ^ (-(beF P hϖ a (H.w0 • a))) : (FractionRing T.V)ˣ) : FractionRing T.V) = _
    rw [beF_w0, Units.val_zpow_eq_zpow_val]; rfl)

def rF (k : ℕ) (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b / k))

theorem isRootForm_rF {k : ℕ} (hk : ∀ a b, (k : ℤ) ∣ beF P hϖ a b) :
    letI := H.starRing; IsRootForm (𝓞 E) k (tF P hϖ) (rF P hϖ k) := by
  letI := H.starRing
  refine ⟨⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩, fun a b => ?_⟩
  · simp only [rF, map_add]
    rw [Int.add_ediv_of_dvd_left (hk a b), neg_add, zpow_add]
  · rw [rF, rF, beF_symm]
  · rw [rF, rF, beF_adj]; rfl
  · rw [rF, tF, ← zpow_natCast, ← zpow_mul, neg_mul, Int.ediv_mul_cancel (hk a b)]
    ext; simp

theorem psiRel0 : letI := H.starRing; PsiRel P.D.toPre (D0 P hϖ).psi fun y => tF P hϖ y (H.w0 • y) :=
  psiRel_rescale _ _

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)

theorem dvd_of_dvd {k : ℕ} (hk : k ∣ l.M') (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (a a' : P.D.toPre.X) :
    (k : ℤ) ∣ beF P hϖ a a' :=
  (Int.natCast_dvd_natCast.2 hk).trans ((dvd_mul_left _ _).trans (hdiv a a'))

def twistedLevelPointsOfLattice (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (v : D.La) :
    QkPt (D0 P hϖ) (FractionRing T.V) l.A :=
  letI := H.starRing
  qkScale (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) (psiRel0 P hϖ)
    (isRootForm_rF P hϖ (dvd_of_dvd P hϖ (Nat.dvd_lcm_right l.M l.A) hdiv)) _ (hL.1 v).choose

open Classical in

def eta0 (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (v : D.La) :
    QkPt (D0 P hϖ) (FractionRing T.V) l.M :=
  letI := H.starRing
  if hv : v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) then
    qkScale (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) (psiRel0 P hϖ)
      (isRootForm_rF P hϖ (dvd_of_dvd P hϖ (Nat.dvd_lcm_left l.M l.A) hdiv)) _ ((hL.2 v hv).choose)
  else GlobalTheory.TorusExt.qkZero (tauBimult_twist (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.D.tau_bimult) _ l.M

open scoped Classical in
variable (D β) in

def LieCl : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = H.rt0 →
    ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct)
      (spMap ((algebraMap (FractionRing T.V) F).comp (algebraMap T.V _))) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X =
        if τ H.rt = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) then D.p else D.q

def TateCl (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
    ∃ I : TateIsoQ D (D0 P hϖ) (oa0 P hϖ) F,
      (I.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (twistedLevelPointsOfLattice P hϖ Y y m hdiv hL a) q → Out.QkPt.Equiv (D0 P hϖ) F q (I.ev l.A a)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ q,
        QkExt (algebraMap _ F) (eta0 P hϖ Y y m hdiv hL a) q → Out.QkPt.Equiv (D0 P hϖ) F q (I.ev l.M a)

def arc (hX : Nontrivial P.D.toPre.X) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a')
    (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (hLie : LieCl P D β b) (hTate : TateCl P hϖ Y b y m hdiv hL) :
    ArcIn D l β T.V b :=
  letI := H.starRing
  { D₀ := D0 P hϖ
    oa := oa0 P hϖ
    nontriv := hX
    even := psiEven_twist (isScalarForm_tF P hϖ) H.w0 P.D.psi_even
    bimult := tauBimult_twist (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.D.tau_bimult
    gen := gen0 P hϖ
    w0 := psi_weight_zero_twist (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.w0
    be := beF P hϖ
    be_symm := beF_symm P hϖ
    be_pos := fun a ha => beF_pos P hϖ ha
    be_adj := beF_adj P hϖ
    be_dvd := hdiv
    eta := eta0 P hϖ Y y m hdiv hL
    etaA := twistedLevelPointsOfLattice P hϖ Y y m hdiv hL
    geom := fun F _ _ _ r z hr hz f hf => by
      subst hf
      obtain ⟨I, h₁, h₂, h₃⟩ := hTate F z hz
      exact ⟨hLie F r hr, I, h₁, h₂, h₃⟩ }

theorem arc_D₀ (hX) (hdiv) (hL) (hLie) (hTate) : (arc P hϖ Y b y m hX hdiv hL hLie hTate).D₀ = D0 P hϖ := rfl

end ThetaShiftProofs

end GlobalTheory.ArcBuild
