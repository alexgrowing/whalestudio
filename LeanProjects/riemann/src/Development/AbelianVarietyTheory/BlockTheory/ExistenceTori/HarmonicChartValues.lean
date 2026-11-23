import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrimitiveGermFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames

section Formal

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def monVal (B : Germ.FB S d O) (h : Germ.PS S 2 d) (w0 : O) (k : ℤ) (f : Germ.PS S 1 d) {κ : Type} [Fintype κ]
    (u : κ → Fin d → S) (α : κ →₀ ℕ) : S :=
  MvPowerSeries.constantCoeff
    (Germ.DmonOf (B.FK S) u α (f * Germ.FB.expS S ((k : S) • B.hL S h w0)))

theorem monVal_natCast (B : Germ.FB S d O) (h : Germ.PS S 2 d) (w0 : O) (m : ℕ) (f : Germ.PS S 1 d)
    {κ : Type} [Fintype κ] (u : κ → Fin d → S) (α : κ →₀ ℕ) :
    monVal B h w0 (m : ℤ) f u α = B.nabVal S h w0 m f u (MvPolynomial.monomial α 1) := by
  classical
  nontriviality S
  simp [monVal, Germ.FB.nabVal, Germ.DpolyOf, MvPolynomial.support_monomial]

def IsBalBilin (B : Germ.FB S d O) (β : Germ.PS S 2 d) : Prop :=
  Germ.ev (n := 3) ![Germ.addOf (B.FK S) (Germ.pt S d 0) (Germ.pt S d 1), Germ.pt S d 2] β =
      Germ.ev (n := 3) ![Germ.pt S d 0, Germ.pt S d 2] β + Germ.ev (n := 3) ![Germ.pt S d 1, Germ.pt S d 2] β ∧
    Germ.ev (n := 3) ![Germ.pt S d 0, Germ.addOf (B.FK S) (Germ.pt S d 1) (Germ.pt S d 2)] β =
      Germ.ev (n := 3) ![Germ.pt S d 0, Germ.pt S d 1] β + Germ.ev (n := 3) ![Germ.pt S d 0, Germ.pt S d 2] β ∧
    Germ.ev (n := 2) ![Germ.pt S d 1, Germ.pt S d 0] β = β ∧
    ∀ a : O, Germ.ev (n := 2) ![Germ.comp1 (B.actK S a) (Germ.pt S d 0), Germ.pt S d 1] β =
      Germ.ev (n := 2) ![Germ.pt S d 0, Germ.comp1 (B.actK S (star a)) (Germ.pt S d 1)] β

def GaugeDiffSt (B : Germ.FB S d O) : Prop :=
  ∀ h h' : Germ.PS S 2 d, B.IsCanonGauge S h → B.IsCanonGauge S h' → IsBalBilin B (h' - h)

end Formal

section Rig

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S] {G : Over X₀} [GrpObj G] [IsCommMonObj G]
  {x : Sp S ⟶ X₀} {d : ℕ}

def IsRigAtZero (L : RigLB G) {j : JetPts G x d} (eL : FrameL G x L.L j) : Prop :=
  ∀ m, LB.Gen.Corr L.L _ _ _ _
    (LB.pullGen L.L _ _ (eL m) (algMap x (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S)).left)
    (Out.rigT G L.L L.rig (algO x S) 1)

end Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} (c : Coeff l)

@[reducible] def ratAlg (S : Type) [CommRing S] [Algebra c.F S] : Algebra ℚ S :=
  ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra

variable {c} {S : Type} [CommRing S] [Algebra c.F S]

abbrev FBar (H : Host E) (S : Type) [CommRing S] (d : ℕ) : Type :=
  @Germ.FB S _ d (𝓞 E) _ H.starRing

def letVec (y : FrPt Xo c S) (ℓ : Lt1 Dw) : Sp (DualNumber S) ⟶ Xo.univ.t.G.left := y.u ℓ.1 ℓ.2

def IsGaugedChart (y : FrPt Xo c S) {d : ℕ} (j : JetPts Xo.univ.t.G y.x d)
    (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d) (cf : Lt1 Dw → Fin d → S)
    (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j) : Prop :=
  letI := H.starRing
  letI := ratAlg c S
  IsChartOf Xo.univ.t y.x j B.G B.A (letVec y) cf ∧
    Realises Xo.univ.t y.x j e B ∧
    B.IsCanonGauge S h ∧
    IsFrameL Xo.univ.t y.x j e (B.A.act H.w0) eL ∧
    IsRigAtZero Xo.univ.t.PP eL

def chartVal (c : Coeff l) [Algebra c.F S] {d : ℕ} (B : FBar H S d) (cf : Lt1 Dw → Fin d → S)
    (h : Germ.PS S 2 d) (k : ℤ) (f : Germ.PS S 1 d) (α : Lt1 Dw →₀ ℕ) : S :=
  letI := H.starRing
  letI := ratAlg c S
  monVal B h H.w0 k f cf α

abbrev SecAt (y : FrPt Xo c S) (k : ℤ) : Type :=
  LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))

def IsNablaAt (y : FrPt Xo c S) (v : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S) : Prop :=
  ∃ (d : ℕ) (j : JetPts Xo.univ.t.G y.x d) (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d)
    (cf : Lt1 Dw → Fin d → S) (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j),
    IsGaugedChart y j e B cf h eL ∧
      ∀ (k : ℤ) (F : SecAt y k), ∃ f : Germ.PS S 1 d, IsGermIn eL k F f ∧
        ∀ α : Lt1 Dw →₀ ℕ, v k F α = chartVal c B cf h k f α

variable (Xo c)

def IsNablaPin (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), IsNablaAt y fun k F α => nab y k F α

variable {Xo}

def polyVal {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (v : Fin n → (Lt1 Dw →₀ ℕ) → S) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, v b (colOf m b)

def Harm (Dw : Datum H) (n : ℕ) : Submodule c.F (MvPolynomial (LtN Dw n) c.F) :=
  harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun _ => 1

variable (Xo)

def ChartExistsSt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
    ∃ (d : ℕ) (j : JetPts Xo.univ.t.G y.x d) (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d)
      (cf : Lt1 Dw → Fin d → S) (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j),
      IsGaugedChart y j e B cf h eL

def PinExistsSt : Prop := ∃ nab : NabV Xo c, IsNablaPin Xo c nab

def HarmIndepSt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (v v' : ∀ k : ℤ, SecAt y k → (Lt1 Dw →₀ ℕ) → S), IsNablaAt y v → IsNablaAt y v' →
    ∀ (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Harm c Dw n → ∀ (k : ℤ) (F : Fin n → SecAt y k),
      polyVal c P (fun b => v k (F b)) = polyVal c P fun b => v' k (F b)

def PinHarmSt : Prop :=
  ∀ nab : NabV Xo c, IsNablaPin Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ) (j : JetPts Xo.univ.t.G y.x d)
      (e : FrameFam Xo.univ.t.G y.x Xo.univ.t.PP.L j) (B : FBar H S d) (cf : Lt1 Dw → Fin d → S)
      (h : Germ.PS S 2 d) (eL : FrameL Xo.univ.t.G y.x Xo.univ.t.PP.L j), IsGaugedChart y j e B cf h eL →
      ∀ (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Harm c Dw n →
        ∀ (k : ℤ) (F : Fin n → SecAt y k) (f : Fin n → Germ.PS S 1 d), (∀ b, IsGermIn eL k (F b) (f b)) →
          polyVal c P (fun b => nab y k (F b)) = polyVal c P fun b => chartVal c B cf h k (f b)

def PinBaseChangeSt : Prop :=
  ∀ nab : NabV Xo c, IsNablaPin Xo c nab →
    ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z →
      ∀ g : ptO Xo z.x ⟶ ptO Xo y.x, g.left = spMap φ.toRingHom →
      ∀ (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Harm c Dw n →
        ∀ (k : ℤ) (F : Fin n → SecAt y k) (F' : Fin n → SecAt z k),
          (∀ b, Out.IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (g ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) →
          φ (polyVal c P fun b => nab y k (F b)) = polyVal c P fun b => nab z k (F' b)

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicChartValues
