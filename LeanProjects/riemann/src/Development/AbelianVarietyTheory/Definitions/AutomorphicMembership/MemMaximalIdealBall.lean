import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

section Ball

variable {C : Type} [NormedField C] [IsUltrametricDist C]

instance ball_valuationRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationRing ↥(intO C) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total ‖(a : C)‖ ‖(b : C)‖ with h | h
  · by_cases hb : (b : C) = 0
    · refine ⟨0, Or.inl (Subtype.ext ?_)⟩
      simp [hb]
    · refine ⟨⟨a / b, ?_⟩, Or.inr (Subtype.ext ?_)⟩
      · change ‖(a : C) / b‖ ≤ 1
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (b : C) * (a / b) = a
        field_simp
  · by_cases ha : (a : C) = 0
    · refine ⟨0, Or.inr (Subtype.ext ?_)⟩
      simp [ha]
    · refine ⟨⟨b / a, ?_⟩, Or.inl (Subtype.ext ?_)⟩
      · change ‖(b : C) / a‖ ≤ 1
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (a : C) * (b / a) = b
        field_simp

instance ball_isLocalRing (C : Type) [NormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) :=
  ValuationRing.isLocalRing _

theorem mem_maximalIdeal_ball (a : ↥(intO C)) : a ∈ maximalIdeal ↥(intO C) ↔ ‖(a : C)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  constructor
  · intro h
    by_contra h1
    have h2 : ‖(a : C)‖ = 1 := le_antisymm ha (not_lt.1 h1)
    have h0 : (a : C) ≠ 0 := by rintro h0; simp [h0] at h2
    refine h (IsUnit.of_mul_eq_one ⟨(a : C)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ h0)))
    change ‖(a : C)⁻¹‖ ≤ 1
    simp [h2]
  · intro h hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have h1 : ‖(a : C)‖ * ‖(b : C)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, hb]; simp
    have h2 : ‖(b : C)‖ ≤ 1 := b.2
    nlinarith [norm_nonneg (a : C), norm_nonneg (b : C)]

def inclO (K : Subfield C) : ↥(intO ↥K) →+* ↥(intO C) :=
  (K.subtype.comp (intO ↥K).subtype).codRestrict (intO C) fun a => a.2

instance inclO_isLocalHom (K : Subfield C) : IsLocalHom (inclO K) :=
  ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((mem_maximalIdeal_ball (inclO K a)).2
      ((mem_maximalIdeal_ball a).1 ((mem_maximalIdeal _).2 h))) ha⟩

end Ball

def evAt {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure PtAt (Z : Mdl Y i₀) (C : SCF p) : Type where
  P : PointsOfFlagModel.PtC (Y Z.i) C
  z : Sp ↥(intO ↥C.S) ⟶ Z.X
  z_π : z ≫ Z.π = P.yt

namespace PtAt

variable {Z : Mdl Y i₀} {C : SCF p} (y : PtAt Z C)

def toPt : Z.Pt := ⟨C, y.P, y.z, y.z_π⟩

def gen : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ y.z

def red : Z.X := y.z (closedPoint ↥(intO ↥C.S))

def fnFld : Subfield ↥C.S :=
  (Subfield.closure {c : ↥C.S | ∃ (U : Z.X.Opens) (h : ⊤ ≤ y.z ⁻¹ᵁ U) (f : Γ(Z.X, U)),
    c = ((evAt y.z h f : ↥(intO ↥C.S)) : ↥C.S)}).topologicalClosure

end PtAt

structure Fam (Y : LocalSystem Xo p W) (i₀ : Idx H p) (C : SCF p) : Type where
  pt : ∀ Z : Mdl Y i₀, PtAt Z C
  compat : ∀ Z₁ Z₂ : Mdl Y i₀, Corr Z₁ Z₂ → NatImg Z₁ Z₂ (pt Z₁).gen (pt Z₂).gen

abbrev Trunc (O : Type) [CommRing O] (n : ℕ) : Type :=
  PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) ^ n}

def constTrunc (O : Type) [CommRing O] (n : ℕ) : PowerSeries O →+* Trunc O n :=
  (Ideal.Quotient.mk _).comp ((PowerSeries.C (R := O)).comp (PowerSeries.constantCoeff (R := O)))

def ConstVecs {X : Scheme.{0}} (t : SAB H X) {O : Type} [CommRing O] (x : Sp (PowerSeries O) ⟶ X)
    (w : Vecs Dw t (PowerSeries O)) : Prop :=
  ∀ n : ℕ, ∃ (G' : Over (Sp (Trunc O n))) (_ : GrpObj G') (φ φ₀ : G'.left ⟶ t.G.left),
    IsGrpPullback G' t.G (spMap (Ideal.Quotient.mk _) ≫ x) φ ∧ IsGrpPullback G' t.G (spMap (constTrunc O n) ≫ x) φ₀ ∧
    (∀ (B : Type) [CommRing B] (ψ : Trunc O n →+* B), ψ (Ideal.Quotient.mk _ PowerSeries.X) = 0 →
      ∀ g : Sp B ⟶ G'.left, g ≫ G'.hom = spMap ψ → g ≫ φ = g ≫ φ₀) ∧
    ∀ σ i, ∃ v : Sp (DualNumber (Trunc O n)) ⟶ G'.left,
      v ≫ G'.hom = spMap (algebraMap (Trunc O n) (DualNumber (Trunc O n))) ∧
      v ≫ φ = w.bc (Ideal.Quotient.mk _) σ i ∧ v ≫ φ₀ = w.bc (constTrunc O n) σ i

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

abbrev idx0 (ct : At S κ p) : Idx A.H p := ⟨κ.l, κ.c, κ.good p ct.hp⟩

def toBase (ct : At S κ p) (Z : ct.Mdl) : (ct.Y Z.i).X ⟶ (ct.Y (idx0 ct)).X :=
  (S.sys.clauses p ct.W ct.hp ct.hW).1.2.choose (idx0 ct) Z.i Z.dvd Z.le

structure DVP (ct : At S κ p) : Type where
  C : SCF p
  K : Subfield ↥C.S
  closed : IsClosed (K : Set ↥C.S)
  dvr : IsDiscreteValuationRing ↥(intO ↥K)
  dense : Dense {x : ↥C.S | IsAlgebraic ↥K x}
  fam : Fam ct.Y (idx0 ct) C
  rat : ∃ w : Sp ↥K ⟶ ct.YY.X, spMap K.subtype ≫ w = (fam.pt ct.YY).gen

variable {ct : At S κ p}

def ptK (Z : ct.Mdl) (y : DVP ct) : ct.Pt Z := (y.fam.pt Z).toPt

def redK (Z : ct.Mdl) (y : DVP ct) : ct.ZP Z := (y.fam.pt Z).red

def dvRho (y : DVP ct) : ℕ := Module.finrank (𝓞 D.host.E) (ct.Ylat (ptK ct.Xm y))

structure Ext (y : DVP ct) : Type where
  L : Subfield ↥y.C.S
  le : y.K ≤ L
  fin : (Subfield.inclusion le).Finite
  π : ↥(intO ↥L)
  irr : Irreducible π

variable {y : DVP ct}

abbrev Ext.O (e : Ext y) : Type := ↥(intO ↥e.L)

abbrev Ext.R (e : Ext y) : Type := PowerSeries e.O

def Ext.piU (e : Ext y) : e.R := PowerSeries.C e.π * PowerSeries.X

def vpi (e : Ext y) : ℝ := -Real.logb p ‖((e.π : ↥e.L) : ↥y.C.S)‖

def Chart (Z : ct.Mdl) (y : DVP ct) (e : Ext y) : Type := Sp e.R ⟶ Z.X

variable {Z : ct.Mdl} {e : Ext y}

def Chart.hom (χ : Chart Z y e) : Sp e.R ⟶ Z.X := χ

def chAt (χ : Chart Z y e) : Prop :=
  ∃ ev : e.R →+* e.O, (∀ x, ev (PowerSeries.C x) = x) ∧ ev PowerSeries.X = e.π ∧
    spMap (inclO e.L) ≫ spMap ev ≫ χ.hom = (y.fam.pt Z).z

def chOpen (χ : Chart Z y e) : Prop := ∀ q : Sp e.R, e.piU ∉ q.asIdeal → χ.hom q ∈ Z.opn

def chAbExact (χ : Chart Z y e) : Prop := ∀ q : Sp e.R, Z.abP (χ.hom q) ↔ PowerSeries.X ∉ q.asIdeal

def ArcData (χ : Chart Z y e) (b : Z.i.c.V ct.W →+* e.O) (a : ArcIn S.Dw Z.i.l (Z.i.c.V ct.W).subtype e.O b) : Prop :=
  (χ.hom ≫ Z.π) ≫ (ct.Y Z.i).s = spMap (PowerSeries.C (R := e.O)) ≫ spMap b ∧
    (ct.Y Z.i).HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := e.O)) PowerSeries.X (χ.hom ≫ Z.π)

def chModU (χ : Chart Z y e) : Prop :=
  ∃ (b : Z.i.c.V ct.W →+* e.O) (a : ArcIn S.Dw Z.i.l (Z.i.c.V ct.W).subtype e.O b) (y' : Sp e.O ⟶ (ct.Y Z.i).X),
    spMap (inclO e.L) ≫ y' = (y.fam.pt Z).P.yt ∧ y' ≫ (ct.Y Z.i).s = spMap b ∧
    (ct.Y Z.i).HasArcData a (Ideal.span {e.π}) (RingHom.id e.O) e.π y' ∧ ArcData χ b a

def chConst (χ : Chart Z y e) : Prop :=
  (∃ b a, ArcData χ b a) ∧ ∃ w : Vecs S.Dw (ct.Y Z.i).t e.R,
    (∀ σ i, IsTanAtG (ct.Y Z.i).t (χ.hom ≫ Z.π) (w σ i)) ∧ ConstVecs (ct.Y Z.i).t (χ.hom ≫ Z.π) w ∧
    ∀ (k : Type) [Field k] (φ : e.R →+* k), φ e.piU ≠ 0 → Z.FlagAt (spMap φ ≫ χ.hom) (w.bc φ)

def pbIdl (J : ct.Idl Z) (χ : Chart Z y e) : Ideal e.R :=
  ⨆ (U : Z.X.affineOpens) (h : ⊤ ≤ χ.hom ⁻¹ᵁ U.1), (J.1.ideal U).map (evAt χ.hom h)

def pbPrinc (J : ct.Idl Z) (χ : Chart Z y e) : Prop := (pbIdl J χ).IsPrincipal

def imgM (χ : Chart Z y e) : ct.ZP Z := χ.hom (closedPoint e.R)

def primeU (e : Ext y) : Sp e.R := (⟨Ideal.span {PowerSeries.X}, PowerSeries.span_X_isPrime⟩ : PrimeSpectrum e.R)

def imgU (χ : Chart Z y e) : ct.ZP Z := χ.hom (primeU e)

def RFam (y : DVP ct) (e : Ext y) : Type := Sp (Localization.Away e.piU) ⟶ (ct.Y (idx0 ct)).X

def chFam (χ : Chart Z y e) : RFam y e :=
  spMap (algebraMap e.R (Localization.Away e.piU)) ≫ χ.hom ≫ Z.π ≫ toBase ct Z

def ordGe (χ : Chart Z y e) (F : ct.Sh Z) (f : ct.Sec F) (a : ℝ) : Prop :=
  ∀ (U : Z.X.Opens) (_ : IsAffineOpen U) (h : ⊤ ≤ χ.hom ⁻¹ᵁ U) (k : ℕ) (g : Γ(F.toMod, U))
    (lam : Γ(F.toMod, U) →ₛₗ[evAt χ.hom h] e.R),
    (F.toMod.presheaf.map (homOfLE (inf_le_left : U ⊓ Z.genO ≤ U)).op).hom g =
      p ^ k • (F.toMod.presheaf.map (homOfLE (inf_le_right : U ⊓ Z.genO ≤ Z.genO)).op).hom f →
    ∀ n : ℕ, (n : ℝ) < a → PowerSeries.coeff n (lam g) = 0

def IsGenK (η : ct.Gen Z) (y : DVP ct) : Prop :=
  redK Z y = ct.gpt η ∧ ∃ h : (y.fam.pt Z).fnFld ≤ y.K, (Subfield.inclusion h).Finite

def GenEx (ct : At S κ p) : Prop := ∀ (Z : ct.Mdl) (η : ct.Gen Z), ∃ y : DVP ct, IsGenK η y

def GoodIff (ct : At S κ p) : Prop :=
  ∀ (Z : ct.Mdl) (x : ct.Pt Z), Subsingleton (ct.Ylat x) ↔ Z.abP (x.z (closedPoint ↥(intO ↥x.C.S)))

theorem nonempty_ext (y : DVP ct) : Nonempty (Ext y) := by
  haveI := y.dvr
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(intO ↥y.K)
  exact ⟨⟨y.K, le_rfl, RingHom.Finite.of_surjective _ fun x => ⟨x, rfl⟩, π, hπ⟩⟩

theorem vpi_pos (e : Ext y) : 0 < vpi e := by
  have h1 : ‖((e.π : ↥e.L) : ↥y.C.S)‖ < 1 :=
    (mem_maximalIdeal_ball e.π).1 ((mem_maximalIdeal _).2 e.irr.not_isUnit)
  have h0 : ((e.π : ↥e.L) : ↥y.C.S) ≠ 0 := fun h => e.irr.ne_zero (Subtype.ext (Subtype.ext h))
  have := Real.logb_neg (b := p) (by exact_mod_cast ct.hp.one_lt) (norm_pos_iff.2 h0) h1
  simp only [vpi]; linarith

theorem img_spz (χ : Chart Z y e) : ct.spz (imgU χ) (imgM χ) :=
  (specializes_closedPoint (primeU e : PrimeSpectrum e.R)).map χ.hom.continuous

end GlobalTheory.LocM.Cht
