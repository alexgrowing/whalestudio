import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

abbrev unitE : ℝ := p.Z.l3u

abbrev mainT : ℝ := p.Z.l3m i

abbrev dat : Datum p.T.Q.H := p.T.Q.Dw ((i : ℕ) + 1)

abbrev Gk : WTZ D.host.E := wtZ (wtA (p.κ i)) (p.κ i).n

abbrev Gs (s : ℤ) : WTZ D.host.E := shiftG (dat p i) (wtA (p.κ i)) (p.κ i).n s

abbrev uW : Weight (dat p i) := uWt (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)

abbrev uM : Weight (dat p i) := uMinus (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (cZero D ((i : ℕ) + 1))

abbrev kap : ℝ := sizeK (dat p i) (wtA (p.κ i)) (p.κ i).n

abbrev Cov : Type 1 := Deep p.T.toCore ((i : ℕ) + 1)

abbrev latDeep (Y : Cov p i) := Y.latOver (Gk p i) (typeK p.fw p.F.lv2 i)

def lenT (PP : ℝ) : ℕ := ⌈PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊

def zed (PP : ℝ) (u1 : Weight (dat p i)) : ℝ :=
  7 * ((dimFlag (dat p i) : ℝ) ^ 2 / lenT p i PP + dimFlag (dat p i) * rhoB (dat p i) u1)

def binT (PP : ℝ) : ℝ := ((lenT p i PP - 1).choose (dimFlag (dat p i)) : ℕ)

abbrev Quo (PP : ℝ) (u1 : Weight (dat p i)) : Prop := IsQuot (dat p i) (D.R.k - 1) (lenT p i PP) (cZero D ((i : ℕ) + 1)) (uW p i) u1

def muCore : ℝ := slope_sq (nrmK p.fw i) (latTypeK p.fw p.F.lv2 i)

def GramAt : Prop :=
  HasGram (nrmR p.R.toRealDat i) ∧ (latAll p.R.toRealDat i).FG ∧ latGood p.R.toRealDat p.F.lv2 i ≠ ⊥ ∧
    GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)

def RecAt : Prop :=
  Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤
    -slope_sq (nrmR p.R.toRealDat i) (latGood p.R.toRealDat p.F.lv2 i)

def CutAt : Prop :=
  eGood p.R.toRealDat i ∘ₗ eGood p.R.toRealDat i = eGood p.R.toRealDat i ∧
  (∀ σ x y, nrmR p.R.toRealDat i σ (eGood p.R.toRealDat i x + (y - eGood p.R.toRealDat i y)) ^ 2 =
    nrmR p.R.toRealDat i σ (eGood p.R.toRealDat i x) ^ 2 + nrmR p.R.toRealDat i σ (y - eGood p.R.toRealDat i y) ^ 2) ∧
  (∀ x ∈ latType p.R.toRealDat p.F.lv2 i,
    ((Fintype.card p.P.Gp : ℕ) : D.what₂.LL) • eGood p.R.toRealDat i x ∈ latType p.R.toRealDat p.F.lv2 i) ∧
  2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b

def BadAt : Prop :=
  (Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) : ℝ) ≤
    3 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i)

def LamAt (A : ℝ) : Prop := slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) ≤ L.sc.x ^ A * L.sc.b

def SizeAt (PP A : ℝ) : Prop :=
  1 ≤ L.sc.b ∧ L.sc.b ≤ unitE p ∧ unitE p ≤ L.sc.x ^ A * L.sc.b ∧ |mainT p i| ≤ L.sc.x ^ A * L.sc.b ∧
  |mainT p i| ≤ PP * kap p i ∧ L.sc.b ≤ PP * kap p i ∧
  ((i : ℕ) + 1 < D.R.m → (∃ u1, Quo p i PP u1) ∧ ∀ u1, Quo p i PP u1 →
    3 * dimFlag (dat p i) + 5 ≤ lenT p i PP ∧ 0 ≤ rhoB (dat p i) u1 ∧ rhoB (dat p i) u1 < 1 ∧ zed p i PP u1 < 1)

def MeasAt (C : ℝ) : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, ∃ c : ℝ, 0 < c ∧ |Real.log c| ≤ C * unitE p ∧
    ∀ f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n,
      nrmR p.R.toRealDat i σ ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) =
        c * petW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
          (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) f

def RatAt : Prop :=
  latType p.R.toRealDat p.F.lv2 i = Submodule.span (𝓞 D.what₂.LL)
    {y | y ∈ (p.R.toRealDat.FW i).MK ∧ y ∈ spType p.R.toRealDat p.F.lv2 i}

def CoreAt (C : ℝ) : Prop :=
  muCore p i - C * unitE p ≤
    slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)

def LowAt (C : ℝ) : Prop := -mainT p i - C * unitE p ≤ muCore p i

def AnchorAt (C : ℝ) : Prop :=
  |mainT p i - ∑ τ : Psi p.T.Q.H, (((dat p i).p : ℝ) - (dat p i).q) * anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ *
      (ofRecord D L p.Del p.h0).logOm| ≤ C * unitE p ∧
  (∑ τ : Psi p.T.Q.H, |(anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)|) * (dat p i).q * L.sc.L ≤ C * unitE p ∧
  (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.b

variable (Y : Cov p i)

def GoodCov : Prop :=
  Y.GoodL L.sc.L (391 * zBase L ^ 2) ∧
  (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) ∧
  ∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W ((i : ℕ) + 1)).rank = D.R.r, ∀ k, ModelW (D.sp.W ((i : ℕ) + 1)) hr ((Y.U σ).X k)

def DeepGoodAt : Prop :=
  Y.GoodAt (Gk p i) ∧ Y.GoodAt (Gs p i (-(cZero D ((i : ℕ) + 1)))) ∧ Y.GoodAt (Gs p i (cZero D ((i : ℕ) + 1))) ∧ Y.GoodAt (wtOf (dat p i) (uM p i) 0) ∧
    0 < Y.rk (Gs p i (-(cZero D ((i : ℕ) + 1)))) ∧ Finite (Comp Y.d.Xo₂ Y.d.c₂) ∧ Nonempty (Comp Y.d.Xo₂ Y.d.c₂) ∧
    ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) (uM p i) 0)

def RingAt : Prop :=
  slope_sq (Y.nrm (Gk p i)) (latDeep p i Y) - 2 * L.sc.b ≤ muCore p i

def MapsAt : Prop :=
  ∃ (n : ℕ) (φ : Fin n → Y.V (Gs p i (-(cZero D ((i : ℕ) + 1)))) →ₗ[Y.d.c₂.F] Y.V (Gk p i)),
    (∀ h, ∀ f ∈ latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1)))), φ h f ∈ latDeep p i Y) ∧ (∀ f, (∀ h, φ h f = 0) → f = 0) ∧
    (∀ σ f, ∑ h, Y.nrm (Gk p i) σ (φ h f) ^ 2 ≤ Real.exp (2 * L.sc.b) * Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1)))) σ f ^ 2) ∧
    n * Formalism.HN.rkK (latDeep p i Y) ≤ Y.rk (Gs p i (cZero D ((i : ℕ) + 1)))

def RkAt (PP : ℝ) : Prop :=
  (Y.rk (Gs p i (cZero D ((i : ℕ) + 1))) : ℝ) ≤ (1 + L.sc.b / (PP * kap p i)) * Y.rk (Gs p i (-(cZero D ((i : ℕ) + 1))))

def GminAt (PP : ℝ) : Prop :=
  ∃ s : Set (Y.V (Gk p i)), s ⊆ (latDeep p i Y : Set (Y.V (Gk p i))) ∧
    (∀ y ∈ s, ∀ σ, Y.nrm (Gk p i) σ y ≤ Real.exp (PP * kap p i)) ∧
    (latDeep p i Y : Set (Y.V (Gk p i))) ⊆ (Submodule.span Y.d.c₂.F s : Set (Y.V (Gk p i)))

def FlatDegAt : Prop := GlobalTheory.FlatLine.FlatDegree Y.U (xiR D) (ofRecord D L p.Del p.h0).logOm

def FlatAt (C : ℝ) : Prop :=
  Y.mu (wtOf (dat p i) (uM p i) 0) - mainT p i - C * unitE p ≤ Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1))))

def UAt (C : ℝ) : Prop := -(C * unitE p) ≤ Y.mu (wtOf (dat p i) (uM p i) 0)

def DegAt (u1 : Weight (dat p i)) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ Z, δ ≤ Y.dg u1 Z ∧ Y.dg u1 Z ≤ δ / (1 - rhoB (dat p i) u1)

def ShareAt (PP : ℝ) (u1 : Weight (dat p i)) : Prop :=
  ∀ Z, binT p i PP * Y.dg u1 Z ≤ Y.rkC (uM p i) Z ∧ (1 - zed p i PP u1) * Y.rkC (uM p i) Z ≤ binT p i PP * Y.dg u1 Z

def HeightAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  ∃ (cs cc X : ℝ) (sl : Comp Y.d.Xo₂ Y.d.c₂ → ℝ), 0 ≤ cs ∧ 0 ≤ cc ∧ 0 ≤ X ∧
    (∀ Z, 0 ≤ Y.ht u1 Z + cs) ∧ (∀ Z, (1 - rhoB (dat p i) u1) * max 0 (sl Z + cs) ≤ Y.ht u1 Z + cs + cc) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Y.d.Xo₂ Y.d.c₂) : ℝ) ∧
    lenT p i PP * X ≤ C * unitE p ∧ lenT p i PP * cc ≤ C * unitE p ∧
    cs * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def HSAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  ∃ A R : ℝ, 0 < A ∧ 0 ≤ R ∧ A * Real.log (max A 1) + R ≤ C * unitE p ∧
    ∀ Z, binT p i PP * Y.dg u1 Z * (lenT p i PP * Y.ht u1 Z - 3 * (dimFlag (dat p i) + 1) * |Y.ht u1 Z| -
      A * Real.log (2 + |Y.ht u1 Z|) - R) ≤ Y.degC (uM p i) Z

def SumAt : Prop :=
  2 * ((∑ᶠ Z, Y.degC (uM p i) Z) / ∑ᶠ Z, Y.rkC (uM p i) Z) ≤ Y.mu (wtOf (dat p i) (uM p i) 0)

def RecTied (D : D7) (L : SizeData₂ D) : Prop := GlobalTheory.FinalJoin2.FieldSmall D L ∧ GlobalTheory.GLq.ESerTie D

theorem core_eq_FO : p.T.Q.c.F = FO D := (GlobalTheory.FinalJoin2.FO_eq_coeff p.T.Q p.fw.laws.pins.2.2.1).symm

theorem RecTied.core_size (h : RecTied D L) : fieldSz p.T.Q.c.F ≤ 2 * Formalism.MainNotions.WeightAlgebra.PO D L := by
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* p.T.Q.c.F := (IntermediateField.equivOfEq (core_eq_FO p).symm).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ p.T.Q.c.F :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr p.T.Q.c.F := NumberField.discr_eq_discr_of_ringEquiv _ e
  obtain ⟨a, b⟩ := h.1
  unfold fieldSz
  rw [← h1, ← h2]
  linarith

theorem two_PO_le (D : D7) (L : SizeData₂ D) (hL : 2 ≤ L.sc.L) : 2 * Formalism.MainNotions.WeightAlgebra.PO D L ≤ 217 * zBase L ^ 2 := by
  have hn : 1 ≤ D.R.ord := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f Ranks.n; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  unfold Formalism.MainNotions.WeightAlgebra.PO zBase
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.r : ℝ) = r at *
  generalize L.sc.L = l at *
  have a1 : f * r ^ 2 * l * 2 ≤ f * r ^ 2 * l * (f * l) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have a2 : f ^ 2 * l * 2 ≤ f ^ 2 * l * (r ^ 2 * l) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul hr hr zero_le_one (by linarith)]) (by positivity)
  nlinarith

theorem RecTied.core_size_le (h : RecTied D L) (hL : 2 ≤ L.sc.L) : fieldSz p.T.Q.c.F ≤ 217 * zBase L ^ 2 :=
  (h.core_size p).trans (two_PO_le D L hL)

theorem goodCov_iff : GoodCov p i Y ↔ Y.GoodL L.sc.L (391 * zBase L ^ 2) :=
  ⟨fun h => h.1, fun h => ⟨h, h.unit, h.modelW⟩⟩

def RowsT : Prop := p.Rows ∧ RecTied D L

def EvTied {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p : Pt Fm x hx ι), RowsT p → Q x hx ι p

theorem evTied_iff {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop) :
    EvTied Fm Q ↔ EvPt Fm fun x hx ι p => RecTied (Fm.D x ι) (Fm.L x ι) → Q x hx ι p :=
  exists_congr fun _ => ⟨fun h x hx hle ι p a b => h x hx hle ι p ⟨a, b⟩, fun h x hx hle ι p a => h x hx hle ι p a.1 a.2⟩

theorem EvTied.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop}
    (h : EvTied Fm Q) (h' : EvTied Fm Q') : EvTied Fm fun x hx ι p => Q x hx ι p ∧ Q' x hx ι p := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  exact ⟨max a b, fun x hx hle ι p hp =>
    ⟨h x hx ((le_max_left _ _).trans hle) ι p hp, h' x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩

def FamilyCompatibility {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ ι : Fm.Ix x, RecTied (Fm.D x ι) (Fm.L x ι)

def Lifts (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (PP C : ℝ), Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ C : ℝ, 0 ≤ C ∧ EvTied Fm fun x hx ι p => ∀ i, Q Fm x hx ι p i (Fm.parT x hx ι).PP C

def Covers (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (_Y : Cov p i) (PP C : ℝ), Prop) : Prop :=
  Lifts fun Fm x hx ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y PP C

def Gram : Prop := Lifts fun _ _ _ _ p i _ _ => GramAt p i

def Rec : Prop := Lifts fun _ _ _ _ p i _ _ => RecAt p i

def Cut : Prop := Lifts fun _ _ _ _ p i _ _ => CutAt p i

def Bad : Prop := Lifts fun _ _ _ _ p i _ _ => BadAt p i

def abelian₂ : Prop := Lifts fun _ _ _ _ p i _ C => LamAt p i C

def Size : Prop := Lifts fun _ _ _ _ p i PP C => SizeAt p i PP C

def Meas : Prop := Lifts fun _ _ _ _ p i _ C => MeasAt p i C

def Rat : Prop := Lifts fun _ _ _ _ p i _ _ => RatAt p i

def CoreLe : Prop := Lifts fun _ _ _ _ p i _ C => CoreAt p i C

def Low : Prop := Lifts fun _ _ _ _ p i _ C => LowAt p i C

def Anchor : Prop := Lifts fun _ _ _ _ p i _ C => AnchorAt p i C

def LowDef : Prop := Lifts fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → LowAt p i C

def DeepEx : Prop := Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
  ∃ Y : Cov p i, GoodCov p i Y

def DeepGood : Prop := Covers fun _ _ _ _ p i Y _ _ => DeepGoodAt p i Y

def Ring : Prop := Covers fun _ _ _ _ p i Y _ _ => RingAt p i Y

def Maps : Prop := Covers fun _ _ _ _ p i Y _ _ => MapsAt p i Y

def Rk : Prop := Covers fun _ _ _ _ p i Y PP _ => RkAt p i Y PP

def Gmin : Prop := Covers fun _ _ _ _ p i Y PP _ => GminAt p i Y PP

def FlatDeg : Prop := Covers fun _ _ _ _ p i Y _ _ => FlatDegAt p i Y

def Flat : Prop := Covers fun _ _ _ _ p i Y _ C => FlatAt p i Y C

def ULow : Prop := Covers fun _ _ _ _ p i Y _ C => UAt p i Y C

def SumC : Prop := Covers fun _ _ _ _ p i Y _ _ => SumAt p i Y

def Deg : Prop := Covers fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → DegAt p i Y u1

def Share : Prop := Covers fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1

def Height : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C u1

def HS : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HSAt p i Y PP C u1

def CovolX : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ EvTied Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)

theorem CovolX.covol (h : CovolX)
    (ht : Closed FamHyp fun Fm _ => EvPt Fm fun x _ ι _ => RecTied (Fm.D x ι) (Fm.L x ι)) : Covol :=
  Closed.imp (Closed.and h ht) fun _ _ _ ⟨⟨C0, h0, a, h⟩, b, h'⟩ => ⟨C0, h0, max a b, fun x hx hle ι p hp =>
    h x hx ((le_max_left _ _).trans hle) ι p ⟨hp, h' x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩

example (h : Low) : LowDef :=
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i _ => h x hx hle ι p hp i⟩

example (h : Formalism.MainNotions.WeightAlgebra.PO D L < 0) : ¬ RecTied D L := fun h' =>
  absurd ((Real.log_natCast_nonneg _).trans h'.1.1) (not_le.2 h)

end GlobalTheory.CovTop

end
