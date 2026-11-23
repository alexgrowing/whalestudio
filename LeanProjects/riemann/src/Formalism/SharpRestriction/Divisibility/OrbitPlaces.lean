import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Formalism.LocalRingCardinality.DataKerI
import Development.AutomorphicArithmetic.OrbitLabellings.ColDefs

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.OrbitPlaces

instance instFactRes (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

abbrev Pl (D : D7) : Type := Bool × HH D

def KGe0 (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (i : ℕ) (s : ℝ) : Prop :=
  ∀ x ∈ ((D.fm u).lat i).L, ∃ y, (D.fm u).emb (i + 1) y = (D.mem u).C.K i ((D.fm u).emb i x) ∧
    VGe D w ((D.fm u).lat (i + 1)).L y s

def KGeTw {D : D7} (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (s : ℝ) : Prop :=
  ∀ x ∈ ((T.fm u μ).lat i).L, ∃ y, (T.fm u μ).emb (i + 1) y = (D.chTw u μ).K i ((T.fm u μ).emb i x) ∧
    VGe D w ((T.fm u μ).lat (i + 1)).L y s

def KGe {D : D7} (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (s : ℝ) : Prop :=
  (μ = D.what₂.mu0 → KGe0 D u w i s) ∧ (μ ≠ D.what₂.mu0 → KGeTw T u μ w i s)

def ValuationComposition (D : D7) (T : TwForms D) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl) (s : ℕ → ℝ), (∀ i < D.R.m, KGe T u μ w i (s (i + 1))) →
    ∀ x ∈ (D.fm u).S 0 w, ColGe T u μ w x (∑ j ∈ SizeData₂.lifts D, s j)

structure Ent (D : D7) where

  nu : D.what₂.Word → ℕ → Pl D → YoungDiagram

  nu_row : ∀ u i, i < D.R.m → ∀ z r, (((nu u i z).rowLen r : ℕ) : ℝ) =
    if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0

  nu_rows : ∀ u i z, (nu u i z).colLen 0 ≤ D.R.N i

  Th : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
    MvPowerSeries (Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]

  ep : ∀ w : D.what₂.places.Pl, ℂ_[D.what₂.places.resChar w]

  be : ∀ w : D.what₂.places.Pl, Pl D → MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]

  sg : ∀ w : D.what₂.places.Pl, Pl D → ℂ_[D.what₂.places.resChar w]

variable {D : D7}

def Ent.size (E : Ent D) (u : D.what₂.Word) (i : ℕ) (z : Pl D) : ℝ := ((E.nu u i z).cells.card : ℝ)

def Ent.row (E : Ent D) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (r : ℕ) : ℝ := ((E.nu u i z).rowLen r : ℝ)

def Ent.cap (E : Ent D) (u : D.what₂.Word) (i : ℕ) (z : Pl D) : ℝ := if IsTopPl D z then E.row u i z 1 else E.row u i z 0

def EntGe (E : Ent D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (B : ℝ) : Prop :=
  ∀ (L : (D.chTw u μ).cls i) (L' : (D.chTw u μ).cls (i + 1)),
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.nu u i) (E.Th u μ w i L L') B

def LevelFree (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∧
    D.what₂.places.resChar w ∉ Dx.Qp μ

theorem levelFree_iff (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) :
    LevelFree Dx u μ w ↔ LevFree Dx u μ w := Iff.rfl

def KForm (E : Ent D) (Dx : DivX D) (T : TwForms D) (sp : ℝ) : Prop :=
  DGamDef D → ∀ u μ (w : D.what₂.places.Pl), DV.Used D μ → LevelFree Dx u μ w → ∀ i < D.R.m, ∀ B : ℝ, EntGe E u μ w i B →
    KGe T u μ w i (B - (if i = 0 then 1 - sp else 1) * vDG D u w)

section Layer

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (w : D.what₂.places.Pl)

def KG (i : ℕ) (s : ℝ) : Prop :=
  ∀ x ∈ (M.lat i).L, ∃ y, M.emb (i + 1) y = C.K i (M.emb i x) ∧ VGe D w (M.lat (i + 1)).L y s

structure ValLat where
  val : ∀ i, C.cls i → AddSubgroup (C.Y i → ℂ)
  val_smul : ∀ i c (r : D.what₂.LL), r ∈ intW D.what₂.places w → ∀ f ∈ val i c, D.what₂.embLL r • f ∈ val i c
  lat_iff : ∀ i, i ≤ D.R.m → ∀ φ : C.cls i → C.Y i → ℂ,
    (∃ x ∈ locW D.what₂.places w (M.lat i).L, M.emb i x = φ) ↔ (φ ∈ M.Fi i ∧ ∀ c, φ c ∈ val i c)

variable {M w}

def PairGe (V : ValLat M w) (i : ℕ) (s : ℝ) : Prop :=
  ∃ a : D.what₂.LL, (a = 0 ∨ ur D w s ≤ (vAdd (D.plEq w) a : ℝ)) ∧
    ∀ (c : C.cls i) (c' : C.cls (i + 1)), ∀ f ∈ V.val i c, ∃ g ∈ V.val (i + 1) c', C.Kmap i c c' f = D.what₂.embLL a • g

end Layer

structure Vals (D : D7) (Dx : DivX D) (T : TwForms D) where
  v0 : ∀ u (w : D.what₂.places.Pl), LevelFree Dx u D.what₂.mu0 w → ValLat (D.fm u) w
  vT : ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → ValLat (T.fm u μ) w

def EntPair (E : Ent D) (Dx : DivX D) (T : TwForms D) (V : Vals D Dx T) : Prop :=
  (∀ u (w : D.what₂.places.Pl) (hL : LevelFree Dx u D.what₂.mu0 w), ∀ i < D.R.m, ∀ B : ℝ, EntGe E u D.what₂.mu0 w i B →
    PairGe (V.v0 u w hL) i B) ∧
  ∀ u μ, DV.Used D μ → μ ≠ D.what₂.mu0 → ∀ (w : D.what₂.places.Pl) (hL : LevelFree Dx u μ w), ∀ i < D.R.m, ∀ B : ℝ, EntGe E u μ w i B →
    PairGe (V.vT u μ w hL) i B

def KFi (D : D7) (T : TwForms D) : Prop :=
  (∀ u, ∀ i < D.R.m, ∀ φ ∈ (D.fm u).Fi i, (D.mem u).C.K i φ ∈ (D.fm u).Fi (i + 1)) ∧
    ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (T.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (T.fm u μ).Fi (i + 1)

def Stab0 (D : D7) : Prop :=
  (∀ u c, Nat.card ((D.mem u).C.stab 0 c) = 1) ∧ ∀ u μ, DV.Used D μ → ∀ c, Nat.card ((D.chTw u μ).stab 0 c) = 1

def SupSpansPsiPart (D : D7) (sp : ℝ) : Prop := sp = 0 ∨ (sp = 1 ∧ Stab0 D)

def ConclusionW (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Pl D → YoungDiagram) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    product_zeroth_first_parts.KvalGe N0 N1 l nu Th B ↔ product_zeroth_first_parts.ExpansionCoeffValuationGe N0 N1 l nu Th B

def WeightsFromStandardBasis (D : D7) : Prop := product_zeroth_first_parts.MinorProdSpanHasCompl → ConclusionW D

def orbMap (D : D7) (p : ℕ) (z : Pl D) (s : ZMod (nP D p)) : Pl D := posPl D p z s.val

def backPl (D : D7) (p : ℕ) (z : Pl D) (e : ℕ) : Pl D := posPl D p z (e * (nP D p - 1))

def IsReps (D : D7) (p : ℕ) (R : Finset (Pl D)) : Prop := ∀ z, ∃! r, r ∈ R ∧ ∃ e : ℕ, posPl D p r e = z

structure OrbOK (D : D7) (p : ℕ) : Prop where
  five : 5 ≤ p
  even : Even (nP D p)
  two : 2 ≤ nP D p

def logPl (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) : MvPowerSeries (Pl D × β) ℂ_[p] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then (((p : ℂ_[p]) ^ e)⁻¹) else 0

def restr (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  fun m => MvPowerSeries.coeff (m.mapDomain fun v => (orbMap D p z v.1, v.2)) Th

def restr1 (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  fun m => MvPowerSeries.coeff (m.mapDomain fun v => (z, v.2)) Th

def orbLoc (E : Ent D) (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) : product_zeroth_first_parts.Loc where
  J := { l := p, five_le_l := h.five, d := nP D p, d_even := h.even, two_le_d := h.two, N0 := D.R.N i, N1 := D.R.N (i + 1),
         Th := Th }
  rank_lt_alt := product_zeroth_first_parts.N_pred_lt D.R (i + 1) (Nat.le_add_left 1 i)
  nu := fun s => E.nu u i (orbMap D p z s)
  nu_rows := fun s => E.nu_rows u i (orbMap D p z s)
  TT := Finset.univ.filter fun s : ZMod (nP D p) => IsTopPl D (orbMap D p z s)

def oneLoc (E : Ent D) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod 1 × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) : product_zeroth_first_parts.Loc1 where
  J := { l := p, five_le_l := h5, N0 := D.R.N i, N1 := D.R.N (i + 1), Th := Th }
  rank_lt_alt := product_zeroth_first_parts.N_pred_lt D.R (i + 1) (Nat.le_add_left 1 i)
  nu := E.nu u i z
  nu_rows := E.nu_rows u i z

def OrbitThetaExpansion (Lc : product_zeroth_first_parts.Loc) (ep sg : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]) : Prop :=
  ∃ U : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
    Lc.Tht ep = U * MvPowerSeries.subst (jetLogG Lc.l Lc.d (β := Fin Lc.N0 × Fin Lc.N1))
      (product_zeroth_first_parts.expS ℂ_[Lc.l] (sg • Lc.beSum be))

def OrbGe (E : Ent D) (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (ep sg : ℂ_[p])
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (β : ℝ) : Prop :=
  ∀ Th, OrbitThetaExpansion (orbLoc E p h u i z Th) ep sg be →
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s => E.nu u i (orbMap D p z s)) Th β

def OneGe (E : Ent D) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (β : ℝ) : Prop :=
  ∀ Th, (oneLoc E p h5 u i z Th).AdmB →
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun _ : ZMod 1 => E.nu u i z) Th β

def beAll (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ r ∈ R, sg r • ∑ a : Fin N0, ∑ b : Fin N1,
    MvPowerSeries.subst (fun s : ZMod (nP D p) =>
      (MvPowerSeries.X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])) (be r)

def BeOK (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (Pl D)) (ep : ℂ_[p]) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) : Prop :=
  ‖ep‖ = 1 ∧ (∀ r ∈ R, sg r = 1 ∨ sg r = -1) ∧
    ∀ r ∈ R, product_zeroth_first_parts.B1 p (nP D p) (be r) ∧ product_zeroth_first_parts.B2 p (nP D p) (be r) ∧ product_zeroth_first_parts.B3 p (nP D p) (be r) ∧ product_zeroth_first_parts.B4 p (nP D p) (be r)

def ThetaExpansionAllPlaces (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (ep : ℂ_[p]) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  ∃ U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
    MvPowerSeries.subst (fun v : Pl D × Fin N0 × Fin N1 => MvPowerSeries.C ep * logPl D p v) Th =
      U * MvPowerSeries.subst (logPl D p (β := Fin N0 × Fin N1)) (product_zeroth_first_parts.expS ℂ_[p] (beAll D p R sg be))

def ThetaExpansionRealPlaces (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  ∃ ep0 : ℂ_[p], ‖ep0‖ = 1 ∧ ∃ be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p],
    (∀ z, product_zeroth_first_parts.B1 p 2 (be z) ∧ product_zeroth_first_parts.B2 p 2 (be z) ∧ product_zeroth_first_parts.B3 p 2 (be z) ∧ product_zeroth_first_parts.B4 p 2 (be z)) ∧
    ∃ ep : Pl D → ℂ_[p], (∀ z, ‖ep z‖ = 1) ∧ ∃ sg : Pl D → ℂ_[p], (∀ z, sg z = 1 ∨ sg z = -1) ∧
    ∃ U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
      MvPowerSeries.subst (fun v : Pl D × Fin N0 × Fin N1 => MvPowerSeries.C ep0 * logPl D p v) Th =
        U * MvPowerSeries.subst (logPl D p (β := Fin N0 × Fin N1))
          (product_zeroth_first_parts.expS ℂ_[p] (∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
            MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
                (MvPowerSeries.X (z, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
              else MvPowerSeries.C (ep z) * MvPowerSeries.X (z, a, b)) (be z)))

def EvenConditionsAllReal (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  UpperTheory.G2.HasThetaProductForm p (nP D p) (posPl D p) Th

def OrbitsAddLowerBound (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ R : Finset (Pl D), IsReps D p R →
    ∀ (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]), BeOK D p R ep sg be →
    ∀ β : Pl D → ℝ, (∀ r ∈ R, OrbGe E p h u i r ep (sg r) (be r) (β r)) →
    ∀ Th, ThetaExpansionAllPlaces D p R ep sg be Th → product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (∑ r ∈ R, β r)

def OrbitsAddAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m →
    ∀ β : Pl D → ℝ, (∀ z, OneGe E p h5 u i z (β z)) →
    ∀ Th, ThetaExpansionRealPlaces D p Th → product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (∑ z, β z)

def OrbitRestriction (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (R : Finset (Pl D)), IsReps D p R →
    ∀ (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]), BeOK D p R ep sg be →
    ∀ Th, ThetaExpansionAllPlaces D p R ep sg be Th → ∀ r ∈ R, OrbitThetaExpansion (orbLoc E p h u i r (restr D p r Th)) ep (sg r) (be r)

def OrbitRestrictionAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ),
    ∀ Th, ThetaExpansionRealPlaces D p Th → ∀ z, (oneLoc E p h5 u i z (restr1 D p z Th)).AdmB

variable {L : SizeData₂ D}

def repsPl (X : Inst D L) (p : ℕ) : Finset (Pl D) :=
  if IsSg D p then (reps X p).image (fun t => ((false, t) : Pl D))
  else (reps X p).image (fun t => ((false, t) : Pl D)) ∪ (reps X p).image (fun t => ((true, t) : Pl D))

def topsOrb (D : D7) (p : ℕ) (r : Pl D) : ℕ :=
  (Finset.univ.filter fun s : ZMod (nP D p) => IsTopPl D (orbMap D p r s)).card

def g0Pl (X : Inst D L) (K : Consts) (p j : ℕ) (r : Pl D) : ℝ :=
  if r.1 = false then max (g0 X K (aL L) (bL L) p j r.2) 0 else 0

def errF (L : SizeData₂ D) (K : Consts) (ce : ErrC) (j p : ℕ) (r : Pl D) : ℝ :=
  gam p * (topsOrb D p r : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
    ce.c6 * (∑ s : ZMod (nP D p), wPl D j (orbMap D p r s)) / (p : ℝ) +
    (nP D p : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) * (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
    (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
      K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)

def betaI (X : Inst D L) (K : Consts) (ce : ErrC) (j p : ℕ) (r : Pl D) : ℝ :=
  if r ∈ kindA D p then g0Pl X K p j r else g0Pl X K p j r + FOrb D j p r - errF L K ce j p r

structure Shape (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : Ent D) : Prop where

  wpos : ∀ i < D.R.m, ∀ z, 0 < wPl D (i + 1) z

  low : ∀ u, ∀ i < D.R.m, ∀ z, ¬ IsTopPl D z → 0 ≤ E.size u i z - ((D.R.k : ℝ) - 1) * wPl D (i + 1) z ∧
    E.size u i z - ((D.R.k : ℝ) - 1) * wPl D (i + 1) z ≤ 4 * wPl D (i + 1) z

  top : ∀ u, ∀ i < D.R.m, ∀ z, IsTopPl D z →
    0 ≤ E.size u i z - E.row u i z 0 - (((D.R.k : ℝ) - 1) * wPl D (i + 1) z - 2 * wPl D (i + 1) z) ∧
    E.size u i z - E.row u i z 0 - (((D.R.k : ℝ) - 1) * wPl D (i + 1) z - 2 * wPl D (i + 1) z) ≤ 4 * wPl D (i + 1) z

  top1 : ∀ u, ∀ i < D.R.m, ∀ z, IsTopPl D z → 2 * wPl D (i + 1) z ≤ E.row u i z 0

  sizeA : ∀ u, ∀ i < D.R.m, ∀ z, E.size u i z ≤ L.sc.a ^ 2

  rankA : 2 * Real.logb 5 (L.sc.a ^ 2) + 2 ≤ (D.R.k : ℝ) - 1

  xa : L.sc.X'' D.R.n ≤ L.sc.a ∧ 1 < L.sc.a

  capW : ∀ u, ∀ i < D.R.m, ∀ z, E.cap u i z ≤ L.sc.b + L.etaSz + 1 + 3 * L.Sc

  alG : ∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, al L (aL L) t ≤ E.row u i (false, t) 0 - E.row u i (false, t) 1

  capG : ∀ u, ∀ i < D.R.m, ∀ z, E.cap u i z ≤ fillG X (bL L) (i + 1) z + cG L

structure CLarge (C6 Cd : ℝ) (K : Consts) (ce : ErrC) : Prop where

  nonneg : 0 ≤ Cd

  c6 : C6 ≤ ce.c6

  dl1 : 3 * Cd ≤ 1 + K.dl1

  dl1nn : 0 ≤ K.dl1
  dl2 : 0 ≤ K.dl2

  dig : 3 * Cd ≤ ce.dig

theorem cLarge_of_fixed {K : Consts} {ce : ErrC} (h6 : ce.c6 = 12) (hd : ce.dig = 3) (h1 : K.dl1 = 5) (h2 : 0 ≤ K.dl2) :
    CLarge 11 1 K ce :=
  ⟨by norm_num, by rw [h6]; norm_num, by rw [h1]; norm_num, by rw [h1]; norm_num, h2, by rw [hd]; norm_num⟩

theorem nEven (D : D7) (i : ℕ) : Even (D.R.N i * D.R.N (i + 1)) := by
  have h : Even (D.R.N i) := by
    show Even (D.R.k + i * (D.R.t + 1))
    exact D.R.k_even.add (D.R.t_odd.add_one.mul_left i)
  exact h.mul_right _

def OrbitParityCond (D : D7) : Prop :=
  (∀ p : ℕ, p.Prime → ((IsResidueClassZero D p ∧ HEv D p) ∨ IsSg D p) → OrbOK D p) ∧
    ∀ p : ℕ, p.Prime → IsResidueClassZero D p → 5 ≤ p

def TypePrimeNotDiscriminant (D : D7) : Prop := ∀ i, D.host.g i ≠ D.host.d

def EvenConditionsInert (E : Ent D) (Dx : DivX D) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w →
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
    ∀ R, IsReps D (D.what₂.places.resChar w) R → BeOK D (D.what₂.places.resChar w) R (E.ep w) (E.sg w) (E.be w) ∧
      ∀ i < D.R.m, Even (D.R.N i * D.R.N (i + 1)) → ∀ L L', ThetaExpansionAllPlaces D (D.what₂.places.resChar w) R (E.ep w) (E.sg w) (E.be w) (E.Th u μ w i L L')

def EvenConditionsAtC (E : Ent D) (Dx : DivX D) : Prop :=
  (∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → IsResidueClassZero D (D.what₂.places.resChar w) →
    hP D (D.what₂.places.resChar w) = 0 → ∀ i < D.R.m, Even (D.R.N i * D.R.N (i + 1)) → ∀ L L', ThetaExpansionRealPlaces D (D.what₂.places.resChar w) (E.Th u μ w i L L')) ∧
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → IsCs D (D.what₂.places.resChar w) →
    ∀ i < D.R.m, Even (D.R.N i * D.R.N (i + 1)) → ∀ L L', EvenConditionsAllReal D (D.what₂.places.resChar w) (E.Th u μ w i L L')

def Cor2 (Lo : product_zeroth_first_parts.Loc) (C6 Cd : ℝ) : Prop :=
  ∀ a : ℝ, Lo.HidaSetting a →
    ∀ (k : ℕ) (w E : ZMod Lo.d → ℝ), 3 ≤ k → (∀ s, 0 < w s) →
      (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ Lo.TT → (Lo.Dl s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ Lo.TT → (Lo.Dl s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      product_zeroth_first_parts.KvalGe Lo.N0 Lo.N1 Lo.l Lo.nu Lo.Th
        ((∑ s ∈ Lo.TT, Lo.baseTerm s) + lpF Lo.l Lo.d (fun s => ((k : ℝ) - 1) * w s) -
          C6 * (∑ s, w s) / (Lo.l : ℝ) - product_zeroth_first_parts.gam Lo.l * (∑ s ∈ Lo.TT, (Lo.Wc s : ℝ)) -
          Cd * ((Lo.d : ℝ) * Lo.N0 * Lo.N1 * (Real.logb Lo.l a + 1)))

theorem corollary_two_same_constant (Lo : product_zeroth_first_parts.Loc) (C : ℝ) : Cor2 Lo C C ↔ Lo.Cor C := Iff.rfl

def OrbitLetterBoundsAll (C6 Cd : ℝ) : Prop :=
  (∀ Lo : product_zeroth_first_parts.Loc, Lo.AdmB → Lo.ThmA Cd ∧ Cor2 Lo C6 Cd) ∧ ∀ Lo : product_zeroth_first_parts.Loc1, Lo.AdmB → Lo.ThmOne Cd

theorem twoConstantBounds_of_one {C : ℝ} (h : product_zeroth_first_parts.ExportAllConjugates C) : OrbitLetterBoundsAll C C := h

def OrbitBoundWithoutOperator (E : Ent D) (X : Inst D L) (K : Consts) : Prop :=
  ∀ (w : D.what₂.places.Pl) (h : OrbOK D (D.what₂.places.resChar w)), IsResidueClassZero D (D.what₂.places.resChar w) →
    hP D (D.what₂.places.resChar w) ≠ 0 → (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ t0 ∈ reps X (D.what₂.places.resChar w),
      OrbGe E (D.what₂.places.resChar w) h u i (false, t0) (E.ep w) (E.sg w (false, t0)) (E.be w (false, t0))
        (max (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) (i + 1) t0) 0)

def JetIntegralityBis (E : Ent D) (Dx : DivX D) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d → ∀ i < D.R.m,
    Even (D.R.N i * D.R.N (i + 1)) → EntGe E u μ w i 0

def ShapeD (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧ ∃ ut : HH D → ℂ_[p], (∀ t, ‖ut t‖ ≤ 1) ∧
    ∃ sg' : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      (∀ m, ‖(m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m sg'‖ ≤ 1) ∧
      Th = product_zeroth_first_parts.expS ℂ_[p] (-(S • ∑ t : HH D, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]))) * sg'

def ThetaKernelShapeAtD (E : Ent D) (Dx : DivX D) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
    ∀ i < D.R.m, ∀ L L', ShapeD D (D.what₂.places.resChar w) (E.Th u μ w i L L')

def OrbitValuationBound (E : Ent D) (X : Inst D L) (K : Consts) (ce : ErrC) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p), ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → (p : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ u, ∀ i < D.R.m, ∀ r ∈ repsPl X p, r ∈ kindBC D p →
    ∀ (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) →
      product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be →
      OrbGe E p h u i r ep sg be (g0Pl X K p (i + 1) r + FOrb D (i + 1) p r - errF L K ce (i + 1) p r)

def EntriesAtInert (E : Ent D) (Dx : DivX D) (X : Inst D L) (K : Consts) (ce : ErrC) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w →
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
    (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n → ∀ i < D.R.m,
      EntGe E u μ w i (∑ r ∈ repsPl X (D.what₂.places.resChar w), betaI X K ce (i + 1) (D.what₂.places.resChar w) r)

def EntriesAtC (E : Ent D) (Dx : DivX D) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → IsResidueClassZero D (D.what₂.places.resChar w) →
    hP D (D.what₂.places.resChar w) = 0 → (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n → ∀ i < D.R.m,
      EntGe E u μ w i (product_zeroth_first_parts.rho (D.what₂.places.resChar w) * (∑ z : Pl D, E.size u i z) -
        C * ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * (Real.logb (D.what₂.places.resChar w) (L.sc.a ^ 2) + 1)))

def lowCs (L : SizeData₂ D) (j p : ℕ) : ℝ :=
  (∑ z ∈ kindBC D p, FOrb D j p z) / (nP D p : ℝ) -
    ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ^ 3 - 8 * (∑ z ∈ kindBC D p, wPl D j z) / p -
    3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a

def ScaledGeneratorsInSup (E : Ent D) (L : SizeData₂ D) (K : Consts) (ce : ErrC) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → IsCs D p → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m,
    (∀ Th, EvenConditionsAllReal D p Th → product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (lowCs L (i + 1) p)) ∧
    (ce.Large → FInert D (i + 1) p - EatI L K ce (i + 1) p ≤ lowCs L (i + 1) p)

def EntriesAtDiscriminant (E : Ent D) (Dx : DivX D) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
    ∀ i < D.R.m, EntGe E u μ w i (-((∑ t : HH D, ctD D u (i + 1) t) / 2))

def OrbitSumBound (X : Inst D L) (K : Consts) (ce : ErrC) : Prop :=
  ∀ p : ℕ, p.Prime → ((IsResidueClassZero D p ∧ HEv D p) ∨ IsSg D p) → ∀ j ∈ SizeData₂.lifts D,
    (∑ t0 ∈ reps X p, max (g0 X K (aL L) (bL L) p j t0) 0) + FInert D j p - EatI L K ce j p ≤
      ∑ r ∈ repsPl X p, betaI X K ce j p r

def ValuationSumBound (E : Ent D) (L : SizeData₂ D) (ce : ErrC) (C : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m,
    FInert D (i + 1) p - EatC L ce (i + 1) p ≤ product_zeroth_first_parts.rho p * (∑ z : Pl D, E.size u i z) -
      C * ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * (Real.logb p (L.sc.a ^ 2) + 1))

def OneLiftInertBound (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D)
    (ce : ErrC) (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) ≠ 0) ∨ IsSg D (D.what₂.places.resChar w)) →
    ¬ Exc D (D.what₂.places.resChar w) → (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ i < D.R.m,
      KGe T u μ w i (WeilJacquetShalikaLaw.g0S X K (D.what₂.places.resChar w) (i + 1) + (L.F (i + 1) w - ES L Xe K ce u (i + 1) w) +
        (if i = 0 then sp else 0) * vDG D u w)

def OneLiftAtC (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC)
    (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    IsResidueClassZero D (D.what₂.places.resChar w) → hP D (D.what₂.places.resChar w) = 0 → ¬ Exc D (D.what₂.places.resChar w) →
    (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ i < D.R.m,
      KGe T u μ w i ((L.F (i + 1) w - EatC L ce (i + 1) (D.what₂.places.resChar w) - vDG D u w) +
        (if i = 0 then sp else 0) * vDG D u w)

def OneLiftAtDiscriminant (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC)
    (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ i < D.R.m,
      KGe T u μ w i ((L.F (i + 1) w - EatD D (i + 1) - vDG D u w) + (if i = 0 then sp else 0) * vDG D u w)

def NoOperatorOrbitBound (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D)
    (ce : ErrC) (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) ≠ 0) ∨ IsSg D (D.what₂.places.resChar w)) →
    ¬ Exc D (D.what₂.places.resChar w) → (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x ((∑ j ∈ SizeData₂.lifts D, WeilJacquetShalikaLaw.g0S X K (D.what₂.places.resChar w) j) + lowS L Xe K ce sp u w)

def JetConsequence (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC)
    (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    IsResidueClassZero D (D.what₂.places.resChar w) → hP D (D.what₂.places.resChar w) = 0 → ¬ Exc D (D.what₂.places.resChar w) →
    (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x ((∑ j ∈ SizeData₂.lifts D, (L.F j w - EatC L ce j (D.what₂.places.resChar w) - vDG D u w)) + sp * vDG D u w)

def ValuationAtDiscriminant (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC)
    (sp : ℝ) : Prop :=
  L.FDef → ErrDefs D L Xe lev K ce → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x ((∑ j ∈ SizeData₂.lifts D, (L.F j w - EatD D j - vDG D u w)) + sp * vDG D u w)

def LiftIntegrality (D : D7) (Dx : DivX D) (T : TwForms D) (sp : ℝ) : Prop :=
  DGamDef D → ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ D.host.d →
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
    D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ i < D.R.m,
    KGe0 D u w i (-((if i = 0 then 1 - sp else 1) * vDG D u w)) ∧
    ∀ μ, DV.Used D μ → μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ →
      KGeTw T u μ w i (-((if i = 0 then 1 - sp else 1) * vDG D u w))

theorem noOperatorOrbit_iff (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D)
    (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : WeilJacquetShalikaLaw.OrbitsWithoutOperator D L X K Dx T lev Xe ce sp = NoOperatorOrbitBound D L X K Dx T lev Xe ce sp := rfl

theorem orbitBoundAtC_iff (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D)
    (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : WeilJacquetShalikaLaw.MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp = JetConsequence D L K Dx T lev Xe ce sp := rfl

theorem valuationAtDiscriminant_iff (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D)
    (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : WeilJacquetShalikaLaw.LossAtDiscriminant D L K Dx T lev Xe ce sp = ValuationAtDiscriminant D L K Dx T lev Xe ce sp := rfl

theorem liftIntegrality_iff (D : D7) (Dx : DivX D) (T : TwForms D) (sp : ℝ) : WeilJacquetShalikaLaw.IsotypicPartsInternalDirectSum D Dx T sp = LiftIntegrality D Dx T sp := rfl

def JetTie (E : Ent D) (Dx : DivX D) (Xp : product_zeroth_first_parts.Prov D) : Prop :=
  (∀ u μ (w : D.what₂.places.Pl) (h : OrbOK D (D.what₂.places.resChar w)), LevelFree Dx u μ w →
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
    ∀ i < D.R.m, ∀ L L' z, ∃ σ : D.jet.Sit, D.jet.jOf σ = i + 1 ∧
      Xp.loc σ = orbLoc E (D.what₂.places.resChar w) h u i z (restr D (D.what₂.places.resChar w) z (E.Th u μ w i L L'))) ∧
  ∀ u μ (w : D.what₂.places.Pl) (h5 : 5 ≤ D.what₂.places.resChar w), LevelFree Dx u μ w →
    IsResidueClassZero D (D.what₂.places.resChar w) → hP D (D.what₂.places.resChar w) = 0 →
    ∀ i < D.R.m, ∀ L L' z, ∃ σ : D.jet.Sit1, D.jet.j1Of σ = i + 1 ∧
      Xp.loc1 σ = oneLoc E (D.what₂.places.resChar w) h5 u i z (restr1 D (D.what₂.places.resChar w) z (E.Th u μ w i L L'))

def AdmK (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : Ent D) (ce : ErrC) (C6 Cd : ℝ) : Prop :=
  OrbitParityCond D ∧ TypePrimeNotDiscriminant D ∧ EvenConditionsInert E Dx ∧ EvenConditionsAtC E Dx ∧ OrbitLetterBoundsAll C6 Cd ∧ OrbitBoundWithoutOperator E X K ∧ JetIntegralityBis E Dx ∧ ThetaKernelShapeAtD E Dx ∧
    Shape D L X E ∧ CLarge C6 Cd K ce

def admitted (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (E : Ent D) (ce : ErrC) (sp C6 Cd : ℝ) :
    Prop :=
  KForm E Dx T sp ∧ AdmK D L X K Dx E ce C6 Cd

def AdmV (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (E : Ent D) (V : Vals D Dx T) (ce : ErrC)
    (sp C6 Cd : ℝ) : Prop :=
  EntPair E Dx T V ∧ KFi D T ∧ SupSpansPsiPart D sp ∧ AdmK D L X K Dx E ce C6 Cd

def Conclusion₂ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (T : TwForms D) (E : Ent D) (lev : LevelData D)
    (Xe : ErrX D) (ce : ErrC) (sp C : ℝ) : Prop :=
  ValuationComposition D T ∧ OrbitsAddLowerBound E ∧ OrbitsAddAtConjugate E ∧ OrbitRestriction E ∧ OrbitRestrictionAtConjugate E ∧ OrbitValuationBound E X K ce ∧ EntriesAtInert E Dx X K ce ∧ EntriesAtC E Dx L C ∧
    EntriesAtDiscriminant E Dx ∧ OrbitSumBound X K ce ∧ ValuationSumBound E L ce C ∧ OneLiftInertBound D L X K Dx T lev Xe ce sp ∧ OneLiftAtC D L K Dx T lev Xe ce sp ∧
    OneLiftAtDiscriminant D L K Dx T lev Xe ce sp ∧ NoOperatorOrbitBound D L X K Dx T lev Xe ce sp ∧ JetConsequence D L K Dx T lev Xe ce sp ∧
    ValuationAtDiscriminant D L K Dx T lev Xe ce sp ∧ LiftIntegrality D Dx T sp

def Stmt (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (C6 Cd : ℝ) : Prop :=
  ∀ (T : TwForms D) (E : Ent D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC), ∀ sp ∈ ({0, 1} : Set ℝ),
    admitted D L X K Dx T E ce sp C6 Cd → Conclusion₂ D L X K Dx T E lev Xe ce sp Cd

def LiftBoundsWithValues (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (C6 Cd : ℝ) : Prop :=
  ∀ (T : TwForms D) (E : Ent D) (V : Vals D Dx T) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC), ∀ sp ∈ ({0, 1} : Set ℝ),
    AdmV D L X K Dx T E V ce sp C6 Cd → KForm E Dx T sp ∧ Conclusion₂ D L X K Dx T E lev Xe ce sp Cd

def KudlaFamilyStatement (C6 Cd : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (_hx : Fm.x1 < x) (i : Fm.Ix x), Stmt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK (Fm.X x i) C6 Cd

theorem val_nat_nonneg (w : D.what₂.places.Pl) (n : ℕ) : (0 : WithTop ℤ) ≤ D.what₂.places.val w (n : D.what₂.LL) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    simp

theorem val_int_nonneg (w : D.what₂.places.Pl) (z : ℤ) : (0 : WithTop ℤ) ≤ D.what₂.places.val w (z : D.what₂.LL) := by
  cases z with
  | ofNat n => simpa using val_nat_nonneg w n
  | negSucc n =>
    rw [Int.cast_negSucc, AddValuation.map_neg]
    exact val_nat_nonneg w (n + 1)

theorem val_coprime (w : D.what₂.places.Pl) (n : ℕ) (h : Nat.Coprime n (D.what₂.places.resChar w)) :
    D.what₂.places.val w (n : D.what₂.LL) = 0 := by
  have hb : ((n : ℤ) * Nat.gcdA n (D.what₂.places.resChar w) +
      (D.what₂.places.resChar w : ℤ) * Nat.gcdB n (D.what₂.places.resChar w)) = 1 := by
    have := Nat.gcd_eq_gcd_ab n (D.what₂.places.resChar w)
    rw [Nat.Coprime.gcd_eq_one h] at this
    simpa using this.symm
  have hb' : ((n : D.what₂.LL) * ((Nat.gcdA n (D.what₂.places.resChar w) : ℤ) : D.what₂.LL) +
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) * ((Nat.gcdB n (D.what₂.places.resChar w) : ℤ) : D.what₂.LL)) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hb
  have hm := AddValuation.map_add (D.what₂.places.val w)
    ((n : D.what₂.LL) * ((Nat.gcdA n (D.what₂.places.resChar w) : ℤ) : D.what₂.LL))
    (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) * ((Nat.gcdB n (D.what₂.places.resChar w) : ℤ) : D.what₂.LL))
  rw [hb', AddValuation.map_one] at hm
  have hp : (0 : WithTop ℤ) < D.what₂.places.val w
      (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) * ((Nat.gcdB n (D.what₂.places.resChar w) : ℤ) : D.what₂.LL)) := by
    rw [AddValuation.map_mul, D.what₂.places.val_resChar w]
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast D.what₂.places.ramIdx_pos w) (val_int_nonneg w _)
  have h1 : D.what₂.places.val w ((n : D.what₂.LL) * ((Nat.gcdA n (D.what₂.places.resChar w) : ℤ) : D.what₂.LL)) ≤ 0 := by
    rcases min_le_iff.1 hm with h | h
    · exact h
    · exact absurd h (not_le.2 hp)
  rw [AddValuation.map_mul] at h1
  exact le_antisymm (le_trans (le_add_of_nonneg_right (val_int_nonneg w _)) h1) (val_nat_nonneg w n)

theorem vAdd_mul (w : D.what₂.places.Pl) {a b : D.what₂.LL} (ha : a ≠ 0) (hb : b ≠ 0) :
    vAdd (D.plEq w) (a * b) = vAdd (D.plEq w) a + vAdd (D.plEq w) b := by
  have h := (D.what₂.places.val w).map_mul a b
  rw [D.val_eq w _ (mul_ne_zero ha hb), D.val_eq w _ ha, D.val_eq w _ hb, ← WithTop.coe_add] at h
  exact WithTop.coe_injective h

theorem vAdd_one (w : D.what₂.places.Pl) : vAdd (D.plEq w) (1 : D.what₂.LL) = 0 := by
  have h := (D.what₂.places.val w).map_one
  rw [D.val_eq w _ one_ne_zero] at h
  exact_mod_cast h

theorem p_ne (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero

theorem vAdd_p (w : D.what₂.places.Pl) :
    vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (p_ne w)] at h
  exact WithTop.coe_injective h

theorem vAdd_pow (w : D.what₂.places.Pl) (k : ℕ) :
    vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k) = (k : ℤ) * (D.what₂.places.ramIdx w : ℤ) := by
  induction k with
  | zero => simp [vAdd_one]
  | succ k ih =>
    rw [pow_succ, vAdd_mul w (pow_ne_zero _ (p_ne w)) (p_ne w), ih, vAdd_p]
    push_cast; ring

section Layer

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {w : D.what₂.places.Pl}

theorem classSum (V : ValLat M w) {i : ℕ} (hi : i < D.R.m) {s : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hdiv : ∀ c, Nat.card (C.stab i c) ∣ n) (hF : ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1)) (hP : PairGe V i s) :
    KG M w i (s - (padicValNat (D.what₂.places.resChar w) n : ℝ)) := by
  intro x hx
  obtain ⟨a, ha, hpair⟩ := hP
  have hφ := (V.lat_iff i hi.le (M.emb i x)).1 ⟨x, Submodule.subset_span hx, rfl⟩
  by_cases ha0 : a = 0
  · refine ⟨0, ?_, 0, 0, Submodule.zero_mem _, by simp, Or.inl rfl⟩
    rw [map_zero]
    funext c'
    show (0 : C.Y (i + 1) → ℂ) = ∑ c, C.wt i c • C.Kmap i c c' (M.emb i x c)
    symm
    refine Finset.sum_eq_zero fun c _ => ?_
    obtain ⟨g, _, hg⟩ := hpair c c' _ (hφ.2 c)
    rw [hg, ha0, map_zero, zero_smul, smul_zero]
  · choose g hgmem hg using fun c c' => hpair c c' _ (hφ.2 c)
    have hpp := D.what₂.places.resChar_prime w
    obtain ⟨k, hk⟩ : ∃ k, k = padicValNat (D.what₂.places.resChar w) n := ⟨_, rfl⟩
    obtain ⟨n', hn'⟩ : ∃ n', n' = n / D.what₂.places.resChar w ^ n.factorization (D.what₂.places.resChar w) := ⟨_, rfl⟩
    have hfac : n.factorization (D.what₂.places.resChar w) = k := by rw [hk, Nat.factorization_def n hpp]
    have hprod : D.what₂.places.resChar w ^ k * n' = n := by
      rw [hn', ← hfac]; exact Nat.ordProj_mul_ordCompl_eq_self n _
    have hcop : Nat.Coprime n' (D.what₂.places.resChar w) := by
      rw [hn']; exact (Nat.coprime_ordCompl hpp hn).symm
    have hn'0 : n' ≠ 0 := by rintro rfl; simp at hprod; exact hn hprod.symm
    have hcard : ∀ c, Nat.card (C.stab i c) ≠ 0 := fun c => Nat.card_pos.ne'
    have hq : ∀ c, n / Nat.card (C.stab i c) * Nat.card (C.stab i c) = D.what₂.places.resChar w ^ k * n' := fun c => by
      rw [hprod]; exact Nat.div_mul_cancel (hdiv c)
    have hq0 : ∀ c, n / Nat.card (C.stab i c) ≠ 0 := fun c h0 => by
      have := hq c; rw [h0, zero_mul, hprod] at this; exact hn this.symm
    let r : C.cls i → D.what₂.LL := fun c => ((n / Nat.card (C.stab i c) : ℕ) : D.what₂.LL) * ((n' : ℕ) : D.what₂.LL)⁻¹
    have hr : ∀ c, r c ∈ intW D.what₂.places w := fun c => by
      show (0 : WithTop ℤ) ≤ D.what₂.places.val w (r c)
      rw [AddValuation.map_mul, AddValuation.map_inv, val_coprime w n' hcop, neg_zero, add_zero]
      exact val_nat_nonneg w _
    let pk : D.what₂.LL := ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k
    have hpk : pk ≠ 0 := pow_ne_zero _ (p_ne w)
    have hwt : ∀ c, C.wt i c = D.what₂.embLL (pk⁻¹ * r c) := fun c => by
      have e1 : ((n / Nat.card (C.stab i c) : ℕ) : ℂ) * ((Nat.card (C.stab i c) : ℕ) : ℂ) =
          ((D.what₂.places.resChar w : ℕ) : ℂ) ^ k * ((n' : ℕ) : ℂ) := by exact_mod_cast hq c
      have c1 : ((Nat.card (C.stab i c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hcard c)
      have c2 : ((n / Nat.card (C.stab i c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hq0 c)
      have c3 : ((D.what₂.places.resChar w : ℕ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hpp.ne_zero)
      have c4 : ((n' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn'0
      show (((Nat.card (C.stab i c) : ℕ) : ℂ))⁻¹ = _
      simp only [pk, r, map_mul, map_inv₀, map_pow, map_natCast]
      field_simp
      linear_combination (-1 : ℂ) * e1
    let b : D.what₂.LL := a * pk⁻¹
    have hb0 : b ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hpk)
    let ψ : C.cls (i + 1) → C.Y (i + 1) → ℂ := fun c' => ∑ c, D.what₂.embLL (r c) • g c c'
    have hK : C.K i (M.emb i x) = D.what₂.embLL b • ψ := by
      funext c'
      show ∑ c, C.wt i c • C.Kmap i c c' (M.emb i x c) = D.what₂.embLL b • ∑ c, D.what₂.embLL (r c) • g c c'
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hg c c', hwt c, smul_smul, smul_smul, ← map_mul, ← map_mul]
      congr 2
      simp only [b]; ring
    have hbC : D.what₂.embLL b ≠ 0 := (map_ne_zero D.what₂.embLL).2 hb0
    have hψF : ψ ∈ M.Fi (i + 1) := by
      have : ψ = (D.what₂.embLL b)⁻¹ • C.K i (M.emb i x) := by rw [hK, smul_smul, inv_mul_cancel₀ hbC, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hF _ hφ.1)
    obtain ⟨z, hz, hzψ⟩ := (V.lat_iff (i + 1) hi ψ).2
      ⟨hψF, fun c' => AddSubgroup.sum_mem _ fun c _ => V.val_smul _ _ _ (hr c) _ (hgmem c c')⟩
    refine ⟨b • z, ?_, b, z, hz, rfl, Or.inr ?_⟩
    · rw [LinearMap.map_smulₛₗ, hzψ, hK]
    · have h1 := ha.resolve_left ha0
      have h2 : vAdd (D.plEq w) a = vAdd (D.plEq w) b + (k : ℤ) * (D.what₂.places.ramIdx w : ℤ) := by
        rw [← vAdd_pow w k, ← vAdd_mul w hb0 hpk]
        congr 1
        simp only [b]; rw [mul_assoc, inv_mul_cancel₀ hpk, mul_one]
      rw [← hk]
      have h3 : (vAdd (D.plEq w) a : ℝ) = (vAdd (D.plEq w) b : ℝ) + (k : ℝ) * (D.what₂.places.ramIdx w : ℝ) := by
        exact_mod_cast h2
      unfold ur at h1 ⊢
      nlinarith [h1, h3]

end Layer

theorem kform_of (E : Ent D) (Dx : DivX D) (T : TwForms D) (V : Vals D Dx T) (hE : EntPair E Dx T V) (hK : KFi D T)
    {sp : ℝ} (hsp : sp = 0 ∨ (sp = 1 ∧ Stab0 D)) : KForm E Dx T sp := by
  intro hG u μ w hUs hL i hi B hB
  have key0 : B - (if i = 0 then 1 - sp else 1) * vDG D u w = B - vDG D u w ∨ (i = 0 ∧ sp = 1 ∧ Stab0 D) := by
    by_cases h0 : i = 0
    · rcases hsp with h | h
      · left; rw [if_pos h0, h]; ring
      · right; exact ⟨h0, h.1, h.2⟩
    · left; rw [if_neg h0]; ring
  refine ⟨fun hμ => ?_, fun hμ => ?_⟩
  · subst hμ
    have hE' := hE.1 u w hL i hi B hB
    rcases key0 with h | ⟨h0, h1, hS⟩
    · rw [h]
      exact classSum (V.v0 u w hL) hi (D.mem u).C.DGam_pos.ne' (fun c => (D.mem u).C.dvd_DGam i hi.le c) (hK.1 u i hi) hE'
    · subst h0
      have := classSum (V.v0 u w hL) hi one_ne_zero (fun c => by rw [hS.1 u c]) (hK.1 u 0 hi) hE'
      have e : B - (if (0 : ℕ) = 0 then 1 - sp else 1) * vDG D u w =
          B - (padicValNat (D.what₂.places.resChar w) 1 : ℝ) := by simp [h1]
      rw [e]
      exact this
  · have hE' := hE.2 u μ hUs hμ w hL i hi B hB
    rcases key0 with h | ⟨h0, h1, hS⟩
    · rw [h]
      have := classSum (V.vT u μ w hL) hi (D.chTw u μ).DGam_pos.ne' (fun c => (D.chTw u μ).dvd_DGam i hi.le c) (hK.2 u μ hUs i hi)
        hE'
      rw [hG.one u u μ] at this
      exact this
    · subst h0
      have := classSum (V.vT u μ w hL) hi one_ne_zero (fun c => by rw [hS.2 u μ hUs c]) (hK.2 u μ hUs 0 hi) hE'
      have e : B - (if (0 : ℕ) = 0 then 1 - sp else 1) * vDG D u w =
          B - (padicValNat (D.what₂.places.resChar w) 1 : ℝ) := by simp [h1]
      rw [e]
      exact this

theorem mem_intW (w : D.what₂.places.Pl) {a : D.what₂.LL} (ha : a ≠ 0) (h : 0 ≤ vAdd (D.plEq w) a) :
    a ∈ intW D.what₂.places w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w a
  rw [D.val_eq w _ ha]
  exact_mod_cast h

section V
variable {w : D.what₂.places.Pl} {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
  {Λ : Submodule (𝓞 D.what₂.LL) V}

theorem VGe.zero (s : ℝ) : VGe D w Λ (0 : V) s := ⟨0, 0, Submodule.zero_mem _, by simp, Or.inl rfl⟩

theorem locW_smul {z : V} (hz : z ∈ locW D.what₂.places w Λ) {c : D.what₂.LL} (hc : c ∈ intW D.what₂.places w) :
    c • z ∈ locW D.what₂.places w Λ :=
  (locW D.what₂.places w Λ).smul_mem ⟨c, hc⟩ hz

theorem VGe.torsion_combination_smul_eq_zero {s : ℝ} {a1 a2 : D.what₂.LL} {z1 z2 : V} (h1 : z1 ∈ locW D.what₂.places w Λ)
    (h2 : z2 ∈ locW D.what₂.places w Λ) (n1 : a1 ≠ 0) (n2 : a2 ≠ 0) (v1 : ur D w s ≤ (vAdd (D.plEq w) a1 : ℝ))
    (hle : vAdd (D.plEq w) a1 ≤ vAdd (D.plEq w) a2) : VGe D w Λ (a1 • z1 + a2 • z2) s := by
  have hc : a1⁻¹ * a2 ≠ 0 := mul_ne_zero (inv_ne_zero n1) n2
  have hv : vAdd (D.plEq w) a2 = vAdd (D.plEq w) a1 + vAdd (D.plEq w) (a1⁻¹ * a2) := by
    rw [← vAdd_mul w n1 hc, mul_inv_cancel_left₀ n1]
  refine ⟨a1, z1 + (a1⁻¹ * a2) • z2, Submodule.add_mem _ h1 (locW_smul h2 (mem_intW w hc (by omega))), ?_, Or.inr v1⟩
  rw [smul_add, smul_smul, mul_inv_cancel_left₀ n1]

theorem VGe.add {s : ℝ} {y1 y2 : V} (h1 : VGe D w Λ y1 s) (h2 : VGe D w Λ y2 s) : VGe D w Λ (y1 + y2) s := by
  obtain ⟨a1, z1, hz1, rfl, ha1⟩ := h1
  obtain ⟨a2, z2, hz2, rfl, ha2⟩ := h2
  by_cases n1 : a1 = 0
  · subst n1; rw [zero_smul, zero_add]; exact ⟨a2, z2, hz2, rfl, ha2⟩
  by_cases n2 : a2 = 0
  · subst n2; rw [zero_smul, add_zero]; exact ⟨a1, z1, hz1, rfl, ha1⟩
  have v1 := ha1.resolve_left n1
  have v2 := ha2.resolve_left n2
  rcases le_total (vAdd (D.plEq w) a1) (vAdd (D.plEq w) a2) with h | h
  · exact VGe.torsion_combination_smul_eq_zero hz1 hz2 n1 n2 v1 h
  · rw [add_comm]; exact VGe.torsion_combination_smul_eq_zero hz2 hz1 n2 n1 v2 h

theorem VGe.smul {s s0 : ℝ} {y : V} (h : VGe D w Λ y s) {c : D.what₂.LL}
    (hc : c = 0 ∨ ur D w s0 ≤ (vAdd (D.plEq w) c : ℝ)) : VGe D w Λ (c • y) (s0 + s) := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨c * a, z, hz, by rw [smul_smul], ?_⟩
  by_cases n1 : c = 0
  · left; rw [n1, zero_mul]
  by_cases n2 : a = 0
  · left; rw [n2, mul_zero]
  right
  rw [vAdd_mul w n1 n2]
  have h1 := hc.resolve_left n1
  have h2 := ha.resolve_left n2
  have : ur D w (s0 + s) = ur D w s0 + ur D w s := by unfold ur; ring
  rw [this]; push_cast; linarith

end V

section Chain
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (w : D.what₂.places.Pl)

theorem KG.loc {i : ℕ} {s : ℝ} (h : KG M w i s) (z : (M.lat i).V) (hz : z ∈ locW D.what₂.places w (M.lat i).L) :
    ∃ y, M.emb (i + 1) y = C.K i (M.emb i z) ∧ VGe D w (M.lat (i + 1)).L y s := by
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by rw [map_zero, map_zero]; exact ((C.Klin i).map_zero).symm, VGe.zero s⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, e1, v1⟩ := hx
    obtain ⟨y2, e2, v2⟩ := hy
    exact ⟨y1 + y2, by rw [map_add, map_add, e1, e2]; exact ((C.Klin i).map_add _ _).symm, VGe.add v1 v2⟩
  | smul r x _ hx =>
    obtain ⟨y1, e1, v1⟩ := hx
    refine ⟨(r : D.what₂.LL) • y1, ?_, ?_⟩
    · rw [Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e1]
      exact ((C.Klin i).map_smul _ _).symm
    · obtain ⟨a, z, hz, rfl, ha⟩ := v1
      exact ⟨a, (r : D.what₂.LL) • z, locW_smul hz r.2, by rw [smul_comm], ha⟩

theorem KG.step {i : ℕ} {s s0 : ℝ} (h : KG M w i s) (x : (M.lat i).V) (hx : VGe D w (M.lat i).L x s0) :
    ∃ y, M.emb (i + 1) y = C.K i (M.emb i x) ∧ VGe D w (M.lat (i + 1)).L y (s0 + s) := by
  obtain ⟨a, z, hz, rfl, ha⟩ := hx
  obtain ⟨y, e, v⟩ := h.loc M w z hz
  refine ⟨a • y, ?_, VGe.smul v ha⟩
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e]
  exact ((C.Klin i).map_smul _ _).symm

theorem chain_ge (s : ℕ → ℝ) (n : ℕ) (h : ∀ i < n, KG M w i (s (i + 1))) (x : (M.lat 0).V)
    (hx : x ∈ locW D.what₂.places w (M.lat 0).L) :
    ∃ y, M.emb n y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap n (M.emb 0 x) ∧ VGe D w (M.lat n).L y (∑ j ∈ Finset.Icc 1 n, s j) := by
  induction n with
  | zero =>
    refine ⟨x, rfl, 1, x, hx, (one_smul _ _).symm, Or.inr ?_⟩
    rw [vAdd_one]; simp [ur]
  | succ n ih =>
    obtain ⟨y, e, v⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨y', e', v'⟩ := (h n (Nat.lt_succ_self n)).step M w y v
    refine ⟨y', ?_, ?_⟩
    · rw [e', e]; rfl
    · rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]; exact v'

end Chain

theorem base_map_mem_local_lattice (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V)
    (hx2 : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L) : T.e0 u μ x ∈ locW D.what₂.places w ((T.fm u μ).lat 0).L := by
  unfold locW at hx2 ⊢
  induction hx2 using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ((T.twist_preserves_base_lattice u μ x).1 hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul]
    exact Submodule.smul_mem _ r hx

theorem compose (D : D7) (T : TwForms D) : ValuationComposition D T := by
  intro u μ w s h x hx
  refine ⟨fun hμ => ?_, fun hμ => ?_⟩
  · exact chain_ge (D.fm u) w s D.R.m (fun i hi => (h i hi).1 hμ) x hx
  · have hx' := base_map_mem_local_lattice T u μ w x hx
    obtain ⟨y, e, v⟩ := chain_ge (T.fm u μ) w s D.R.m (fun i hi => (h i hi).2 hμ) (T.e0 u μ x) hx'
    exact ⟨y, by rw [e, T.embed_mul_block_embedding]; rfl, v⟩

theorem bs_iter (X : Inst D L) (h t : HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem bs_idem (X : Inst D L) (h t : HH D) : X.bs h (X.bs h t) = X.bs h t := by
  obtain ⟨i, hi⟩ := X.bs_orb h t
  have := bs_iter X h (X.bs h t) i
  rw [hi] at this
  exact this.symm

theorem mem_reps {X : Inst D L} {p : ℕ} {t : HH D} : t ∈ reps X p ↔ X.bs (stepP D p) t = t := by
  unfold reps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s, _, rfl⟩; exact bs_idem X _ s
  · intro h; exact ⟨t, Finset.mem_univ _, h⟩

theorem posPl_eq (D : D7) (p : ℕ) (b : Bool) (t : HH D) (e : ℕ) :
    posPl D p (b, t) e = (xor b (decide (IsSg D p ∧ Odd e)), t + e • hP D p) := rfl

theorem isReps_repsPl (X : Inst D L) (p : ℕ) : IsReps D p (repsPl X p) := by
  rintro ⟨β, t⟩
  by_cases hs : IsSg D p
  · have hst : stepP D p = 2 • hP D p := if_pos hs
    have hR : ∀ r : Pl D, r ∈ repsPl X p ↔ r.1 = false ∧ X.bs (2 • hP D p) r.2 = r.2 := by
      intro r
      unfold repsPl
      rw [if_pos hs, Finset.mem_image]
      constructor
      · rintro ⟨s, hs', rfl⟩; exact ⟨rfl, by rw [← hst]; exact mem_reps.1 hs'⟩
      · rintro ⟨h1, h2⟩; exact ⟨r.2, mem_reps.2 (by rw [hst]; exact h2), Prod.ext h1.symm rfl⟩
    cases β with
    | false =>
      obtain ⟨i, hi⟩ := X.bs_orb (2 • hP D p) t
      refine ⟨(false, X.bs (2 • hP D p) t), ⟨(hR _).2 ⟨rfl, bs_idem X _ t⟩, 2 * i, ?_⟩, ?_⟩
      · rw [posPl_eq]
        have : ¬ (IsSg D p ∧ Odd (2 * i)) := fun h => (Nat.not_odd_iff_even.2 (even_two_mul i)) h.2
        rw [decide_eq_false this, mul_comm, mul_smul, hi]; rfl
      · rintro ⟨b, t1⟩ ⟨hr, e, he⟩
        obtain ⟨h1, h2⟩ := (hR _).1 hr
        simp only at h1 h2
        subst h1
        rw [posPl_eq] at he
        have he1 := congrArg Prod.fst he
        have he2 : t1 + e • hP D p = t := congrArg Prod.snd he
        have hev : Even e := by
          by_contra hne
          have : IsSg D p ∧ Odd e := ⟨hs, Nat.not_even_iff_odd.1 hne⟩
          simp [this] at he1
        obtain ⟨c, rfl⟩ := hev
        have : t = t1 + c • (2 • hP D p) := by rw [← he2, ← mul_smul, mul_two]
        rw [this, bs_iter, h2]
    | true =>
      obtain ⟨i, hi⟩ := X.bs_orb (2 • hP D p) (t - hP D p)
      refine ⟨(false, X.bs (2 • hP D p) (t - hP D p)), ⟨(hR _).2 ⟨rfl, bs_idem X _ _⟩, 2 * i + 1, ?_⟩, ?_⟩
      · rw [posPl_eq]
        have : IsSg D p ∧ Odd (2 * i + 1) := ⟨hs, odd_two_mul_add_one i⟩
        rw [decide_eq_true this, add_smul, one_smul, ← add_assoc, mul_comm, mul_smul, hi]; simp
      · rintro ⟨b, t1⟩ ⟨hr, e, he⟩
        obtain ⟨h1, h2⟩ := (hR _).1 hr
        simp only at h1 h2
        subst h1
        rw [posPl_eq] at he
        have he1 := congrArg Prod.fst he
        have he2 : t1 + e • hP D p = t := congrArg Prod.snd he
        have hod : Odd e := by
          by_contra hne
          have : ¬ (IsSg D p ∧ Odd e) := fun h => hne h.2
          simp [this] at he1
        obtain ⟨c, rfl⟩ := hod
        have : t - hP D p = t1 + c • (2 • hP D p) := by
          rw [← he2, add_smul, one_smul, ← mul_smul, mul_comm c 2]; abel
        rw [this, bs_iter, h2]
  · have hst : stepP D p = hP D p := if_neg hs
    have hR : ∀ r : Pl D, r ∈ repsPl X p ↔ X.bs (hP D p) r.2 = r.2 := by
      intro r
      unfold repsPl
      rw [if_neg hs, Finset.mem_union, Finset.mem_image, Finset.mem_image]
      constructor
      · rintro (⟨s, hs', rfl⟩ | ⟨s, hs', rfl⟩) <;> (rw [← hst]; exact mem_reps.1 hs')
      · intro h2
        have hm : r.2 ∈ reps X p := mem_reps.2 (by rw [hst]; exact h2)
        cases hb : r.1 with
        | false => exact Or.inl ⟨r.2, hm, Prod.ext hb.symm rfl⟩
        | true => exact Or.inr ⟨r.2, hm, Prod.ext hb.symm rfl⟩
    have hdec : ∀ e : ℕ, decide (IsSg D p ∧ Odd e) = false := fun e => decide_eq_false fun h => hs h.1
    obtain ⟨i, hi⟩ := X.bs_orb (hP D p) t
    refine ⟨(β, X.bs (hP D p) t), ⟨(hR _).2 (bs_idem X _ t), i, ?_⟩, ?_⟩
    · rw [posPl_eq, hdec, hi]; simp
    · rintro ⟨b, t1⟩ ⟨hr, e, he⟩
      have h2 := (hR _).1 hr
      simp only at h2
      rw [posPl_eq, hdec] at he
      have he1 : xor b false = β := congrArg Prod.fst he
      have he2 : t1 + e • hP D p = t := congrArg Prod.snd he
      rw [Bool.xor_false] at he1
      rw [← he2, bs_iter, h2, he1]

theorem one_mem_lifts (D : D7) : 1 ∈ SizeData₂.lifts D := by
  unfold SizeData₂.lifts; rw [Finset.mem_Icc]; exact ⟨le_refl 1, by have := D.R.two_le_m; omega⟩

theorem sum_ite_one (D : D7) (c : ℝ) : ∑ j ∈ SizeData₂.lifts D, (if j = 1 then c else 0) = c := by
  rw [Finset.sum_ite_eq' (SizeData₂.lifts D) 1 (fun _ => c)]; simp [one_mem_lifts D]

theorem noOp_of {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp : ℝ}
    (hc : ValuationComposition D T) (hl : OneLiftInertBound D L X K Dx T lev Xe ce sp) : NoOperatorOrbitBound D L X K Dx T lev Xe ce sp := by
  intro hF hE u w hT hI hX hX2 μ hUs hQ x hx
  have h := hc u μ w (fun j => WeilJacquetShalikaLaw.g0S X K (D.what₂.places.resChar w) j + (L.F j w - ES L Xe K ce u j w) +
        (if j = 1 then sp else 0) * vDG D u w) (fun i hi => by
          have := hl hF hE u w hT hI hX hX2 μ hUs hQ i hi
          simpa using this) x hx.1
  have e : (∑ j ∈ SizeData₂.lifts D, (WeilJacquetShalikaLaw.g0S X K (D.what₂.places.resChar w) j + (L.F j w - ES L Xe K ce u j w) +
        (if j = 1 then sp else 0) * vDG D u w)) = (∑ j ∈ SizeData₂.lifts D, WeilJacquetShalikaLaw.g0S X K (D.what₂.places.resChar w) j) + lowS L Xe K ce sp u w := by
    unfold lowS
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_ite_one]
    ring
  rw [e] at h
  exact h

theorem int_of {E : Ent D} {Dx : DivX D} {T : TwForms D} {sp : ℝ} (hk : KForm E Dx T sp) (hi : JetIntegralityBis E Dx) :
    LiftIntegrality D Dx T sp := by
  intro hG u w hd hg hT i him
  refine ⟨?_, ?_⟩
  · have hL : LevelFree Dx u D.what₂.mu0 w := ⟨hT, hg, by rw [Dx.degreeZero_partial_set_empty]; simp⟩
    have := (hk hG u D.what₂.mu0 w (Or.inl rfl) hL i him 0 (hi u D.what₂.mu0 w hL hd i him (nEven D i))).1 rfl
    simpa using this
  · intro μ hUs hμ hQ
    have hL : LevelFree Dx u μ w := ⟨hT, hg, hQ⟩
    have := (hk hG u μ w hUs hL i him 0 (hi u μ w hL hd i him (nEven D i))).2 hμ
    simpa using this

theorem VGe.mono {w : D.what₂.places.Pl} {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    {Λ : Submodule (𝓞 D.what₂.LL) V} {y : V} {s s' : ℝ} (h : VGe D w Λ y s) (hs : s' ≤ s) : VGe D w Λ y s' := by
  obtain ⟨a, z, hz, hy, ha⟩ := h
  refine ⟨a, z, hz, hy, ha.imp id fun h => le_trans ?_ h⟩
  unfold ur
  exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

theorem KGe.mono {T : TwForms D} {u μ} {w : D.what₂.places.Pl} {i : ℕ} {s s' : ℝ} (h : KGe T u μ w i s) (hs : s' ≤ s) :
    KGe T u μ w i s' :=
  ⟨fun hμ x hx => by obtain ⟨y, hy, hv⟩ := h.1 hμ x hx; exact ⟨y, hy, VGe.mono hv hs⟩,
   fun hμ x hx => by obtain ⟨y, hy, hv⟩ := h.2 hμ x hx; exact ⟨y, hy, VGe.mono hv hs⟩⟩

theorem succ_mem_lifts {i : ℕ} (hi : i < D.R.m) : i + 1 ∈ SizeData₂.lifts D := by
  unfold SizeData₂.lifts; rw [Finset.mem_Icc]; omega

theorem not_g_of_not_exc {p : ℕ} (h : ¬ Exc D p) : p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  intro hp
  apply h
  unfold Exc
  rw [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  · exact Dvd.intro_left _ rfl

theorem liftI_of {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Ent D} {lev : LevelData D} {Xe : ErrX D}
    {ce : ErrC} {sp : ℝ} (hk : KForm E Dx T sp) (he : EntriesAtInert E Dx X K ce) (hs : OrbitSumBound X K ce)
    (ho : OrbitParityCond D) (hb : EvenConditionsAtC E Dx) (hS : ScaledGeneratorsInSup E L K ce) :
    OneLiftInertBound D L X K Dx T lev Xe ce sp := by
  intro hF hE u w hT hI hX hX2 μ hUs hQ i hi
  have hg := not_g_of_not_exc hX
  have hL : LevelFree Dx u μ w := ⟨hT, hg, hQ⟩
  have hg0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [h])
  have hg1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [h])
  have hin : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) := hI.imp (fun h => h.1) id
  have hr : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by
    rcases hin with h | h
    · have h3 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := h
      rw [h3]; simp
    · have h3 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal := h
      rw [h3]; simp
  have hc : ¬ (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0) := by
    rintro ⟨h1, h2⟩
    rcases hI with h | h
    · exact h.2 h2
    · have h3 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := h1
      have h4 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal := h
      rw [h4] at h3; simp at h3
  have eF : L.F (i + 1) w = FInert D (i + 1) (D.what₂.places.resChar w) := by
    rw [hF (i + 1) (succ_mem_lifts hi) w]
    unfold Fval FvalP SizeData₂.gTypes
    rw [if_neg hg, if_neg hr, if_pos ⟨hin, hX2⟩]
  have eE : ES L Xe K ce u (i + 1) w = vDG D u w + EatI L K ce (i + 1) (D.what₂.places.resChar w) := by
    unfold ES Eval vDG
    simp only [if_neg hT, if_neg hg0, if_neg hg1, if_neg hr, if_pos (And.intro hin hX2), if_neg hc]
  by_cases hcs : IsCs D (D.what₂.places.resChar w)
  · obtain ⟨h1, h2⟩ := hS _ (ho.2 _ (D.what₂.places.resChar_prime w) hcs.1) hcs hX2 u i hi
    refine (hk hE.dgam u μ w hUs hL i hi _ (fun Lc Lc' => h1 _ (hb.2 u μ w hL hcs i hi (nEven D i) Lc Lc'))).mono ?_
    have hsum := h2 hE.large
    rw [eF, eE, WeilJacquetShalikaLaw.g0S, if_pos hcs]
    by_cases h0 : i = 0
    · simp only [if_pos h0]; linarith
    · simp only [if_neg h0]; linarith
  have hI' : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w) :=
    hI.imp (fun h => ⟨h.1, ((class_zero_trichotomy h.1).resolve_right (fun h' => h'.elim h.2 hcs))⟩) id
  refine (hk hE.dgam u μ w hUs hL i hi _ (he u μ w hL hI' hX2 i hi)).mono ?_
  have hsum := hs _ (D.what₂.places.resChar_prime w) hI' (i + 1) (succ_mem_lifts hi)
  rw [eF, eE, WeilJacquetShalikaLaw.g0S, if_neg hcs]
  by_cases h0 : i = 0
  · simp only [if_pos h0]; linarith
  · simp only [if_neg h0]; linarith

theorem liftC_of {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Ent D} {lev : LevelData D} {Xe : ErrX D}
    {ce : ErrC} {sp C : ℝ} (hk : KForm E Dx T sp) (ho : OrbitParityCond D) (he : EntriesAtC E Dx L C) (hs : ValuationSumBound E L ce C) :
    OneLiftAtC D L K Dx T lev Xe ce sp := by
  intro hF hE u w hT hc0 hh hX hX2 μ hUs hQ i hi
  have hg := not_g_of_not_exc hX
  have hL : LevelFree Dx u μ w := ⟨hT, hg, hQ⟩
  refine (hk hE.dgam u μ w hUs hL i hi _ (he u μ w hL hc0 hh hX2 i hi)).mono ?_
  have hsum := hs _ (D.what₂.places.resChar_prime w) (ho.2 _ (D.what₂.places.resChar_prime w) hc0) hc0 hh hX2 u i hi
  have hr : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by
    have h3 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := hc0
    rw [h3]; simp
  have eF : L.F (i + 1) w = FInert D (i + 1) (D.what₂.places.resChar w) := by
    rw [hF (i + 1) (succ_mem_lifts hi) w]
    unfold Fval FvalP SizeData₂.gTypes
    rw [if_neg hg, if_neg hr, if_pos ⟨Or.inl hc0, hX2⟩]
  rw [eF]
  by_cases h0 : i = 0
  · simp only [if_pos h0]; linarith
  · simp only [if_neg h0]; linarith

theorem liftD_of {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Ent D} {lev : LevelData D} {Xe : ErrX D}
    {ce : ErrC} {sp : ℝ} (hk : KForm E Dx T sp) (hgd : TypePrimeNotDiscriminant D) (he : EntriesAtDiscriminant E Dx) :
    OneLiftAtDiscriminant D L K Dx T lev Xe ce sp := by
  intro hF hE u w hT hd μ hUs hQ i hi
  have hpd := cls_ramD hd
  have hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hgd 0 (h.symm.trans hpd)
    · exact hgd 1 (h.symm.trans hpd)
  have hL : LevelFree Dx u μ w := ⟨hT, hg, hQ⟩
  refine (hk hE.dgam u μ w hUs hL i hi _ (he u μ w hL hd i hi)).mono ?_
  have eF : L.F (i + 1) w = FRamD D (i + 1) := by
    rw [hF (i + 1) (succ_mem_lifts hi) w]
    unfold Fval FvalP SizeData₂.gTypes
    rw [if_neg hg, if_pos hd]
  have hsup : ∑ t : HH D, ctD D u (i + 1) t ≤
      Finset.univ.sup' ⟨D.u₀, Finset.mem_univ _⟩ fun u : D.what₂.Word => ∑ t : HH D, ctD D u (i + 1) t :=
    Finset.le_sup' (fun u : D.what₂.Word => ∑ t : HH D, ctD D u (i + 1) t) (Finset.mem_univ u)
  rw [eF]
  unfold EatD
  by_cases h0 : i = 0
  · simp only [if_pos h0]; linarith
  · simp only [if_neg h0]; linarith

theorem sum_shape (D : D7) (f : ℕ → ℝ) (c : ℝ) :
    ∑ j ∈ SizeData₂.lifts D, (f j + (if j = 1 then c else 0)) = (∑ j ∈ SizeData₂.lifts D, f j) + c := by
  rw [Finset.sum_add_distrib, sum_ite_one]

theorem c_of {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp : ℝ}
    (hc : ValuationComposition D T) (hl : OneLiftAtC D L K Dx T lev Xe ce sp) : JetConsequence D L K Dx T lev Xe ce sp := by
  intro hF hE u w hT hc0 hh hX hX2 μ hUs hQ x hx
  have h := hc u μ w (fun j => (L.F j w - EatC L ce j (D.what₂.places.resChar w) - vDG D u w) +
        (if j = 1 then sp * vDG D u w else 0)) (fun i hi => by
          have := hl hF hE u w hT hc0 hh hX hX2 μ hUs hQ i hi
          by_cases h0 : i = 0
          · simpa [h0] using this
          · simpa [h0] using this) x hx.1
  rw [sum_shape] at h
  exact h

theorem atD_of {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp : ℝ}
    (hc : ValuationComposition D T) (hl : OneLiftAtDiscriminant D L K Dx T lev Xe ce sp) : ValuationAtDiscriminant D L K Dx T lev Xe ce sp := by
  intro hF hE u w hT hd μ hUs hQ x hx
  have h := hc u μ w (fun j => (L.F j w - EatD D j - vDG D u w) +
        (if j = 1 then sp * vDG D u w else 0)) (fun i hi => by
          have := hl hF hE u w hT hd μ hUs hQ i hi
          by_cases h0 : i = 0
          · simpa [h0] using this
          · simpa [h0] using this) x hx.1
  rw [sum_shape] at h
  exact h

theorem entI_of {X : Inst D L} {K : Consts} {Dx : DivX D} {E : Ent D} {ce : ErrC}
    (hR : ∀ p, IsReps D p (repsPl X p)) (ho : OrbitParityCond D) (hb : EvenConditionsInert E Dx) (ha : OrbitsAddLowerBound E) (hf : OrbitValuationBound E X K ce)
    (hA : OrbitBoundWithoutOperator E X K) : EntriesAtInert E Dx X K ce := by
  intro u μ w hL hI hX i hi Lc Lc'
  have hok := ho.1 _ (D.what₂.places.resChar_prime w) hI
  obtain ⟨hbe, hth⟩ := hb u μ w hL hI _ (hR _)
  refine ha _ hok u i hi _ (hR _) (E.ep w) (E.sg w) (E.be w) hbe _ ?_ _ (hth i hi (nEven D i) Lc Lc')
  intro r hr
  unfold betaI
  by_cases hk : r ∈ kindA D (D.what₂.places.resChar w)
  · rw [if_pos hk]
    have hk' := (Finset.mem_filter.1 hk).2
    have hc0 : IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) ≠ 0 :=
      (hI.resolve_right hk'.1).imp id HEv.ne_zero
    have hr' : r.2 ∈ reps X (D.what₂.places.resChar w) := by
      unfold repsPl at hr
      rw [if_neg hk'.1, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
      rcases hr with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact ht
      · exact ht
    have := hA w hok hc0.1 hc0.2 hX u i hi r.2 hr'
    have e : r = (false, r.2) := Prod.ext hk'.2 rfl
    unfold g0Pl
    rw [if_pos hk'.2]
    rw [e]
    exact this
  · rw [if_neg hk]
    have hbc : r ∈ kindBC D (D.what₂.places.resChar w) := by
      unfold kindBC
      unfold kindA at hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hk ⟨Finset.mem_univ _, hcon.1, by cases h : r.1 <;> simp_all⟩
    obtain ⟨h1, h2, h3⟩ := hbe
    obtain ⟨b1, b2, b3, b4⟩ := h3 r hr
    exact hf _ hok (hI.imp (fun h => ⟨h.1, h.2.ne_zero⟩) id) hX u i hi r hr hbc (E.ep w) (E.sg w r) (E.be w r) h1 (h2 r hr) b1 b2 b3 b4

theorem nP_eq_one {p : ℕ} (h1 : IsResidueClassZero D p) (h2 : hP D p = 0) : nP D p = 1 := by
  have hs : ¬ IsSg D p := by
    intro h
    have h3 : D.host.cls p = PrimeClass.inertClass := h1
    have h4 : D.host.cls p = PrimeClass.signal := h
    rw [h4] at h3; simp at h3
  unfold nP
  rw [if_neg hs, h2, addOrderOf_zero]

theorem card_Pl (D : D7) : (Fintype.card (Pl D) : ℝ) = (D.R.f : ℝ) := by
  have h : Fintype.card D.R.A = D.R.ord := D.R.card_A
  simp [Pl, HH, Fintype.card_prod, Ranks.f, Ranks.n, h]

theorem entC_of {X : Inst D L} {Dx : DivX D} {E : Ent D} {C6 C : ℝ}
    (ho : OrbitParityCond D) (hb : EvenConditionsAtC E Dx) (ha : OrbitsAddAtConjugate E) (hall : OrbitLetterBoundsAll C6 C) (hS : Shape D L X E) : EntriesAtC E Dx L C := by
  intro u μ w hL hc0 hh hX i hi Lc Lc'
  have h5 := ho.2 _ (D.what₂.places.resChar_prime w) hc0
  have := ha _ h5 (nP_eq_one hc0 hh) u i hi
    (fun z => product_zeroth_first_parts.rho (D.what₂.places.resChar w) * E.size u i z -
      C * ((D.R.N i : ℝ) * D.R.N (i + 1) * (Real.logb (D.what₂.places.resChar w) (L.sc.a ^ 2) + 1)))
    (fun z Th hTh => hall.2 (oneLoc E _ h5 u i z Th) hTh (L.sc.a ^ 2)
      ⟨le_trans hX (le_trans hS.xa.1 (by nlinarith [hS.xa.2])), hS.sizeA u i hi z⟩) _ (hb.1 u μ w hL hc0 hh i hi (nEven D i) Lc Lc')
  have e : (∑ z : Pl D, (product_zeroth_first_parts.rho (D.what₂.places.resChar w) * E.size u i z -
      C * ((D.R.N i : ℝ) * D.R.N (i + 1) * (Real.logb (D.what₂.places.resChar w) (L.sc.a ^ 2) + 1)))) =
      product_zeroth_first_parts.rho (D.what₂.places.resChar w) * (∑ z : Pl D, E.size u i z) -
        C * ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * (Real.logb (D.what₂.places.resChar w) (L.sc.a ^ 2) + 1)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Pl]
    ring
  rw [e] at this
  exact this

theorem sum_zmod (n : ℕ) [NeZero n] (g : ℕ → ℝ) : ∑ s : ZMod n, g s.val = ∑ a ∈ Finset.range n, g a := by
  refine Finset.sum_bij (fun s _ => s.val) (fun s _ => Finset.mem_range.2 (ZMod.val_lt s))
    (fun a _ b _ h => ZMod.val_injective n h) ?_ (fun _ _ => rfl)
  intro a ha
  exact ⟨(a : ZMod n), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.1 ha)⟩

theorem sum_orb (p : ℕ) (f : Pl D → ℝ) (R : Finset (Pl D)) (hR : IsReps D p R) :
    ∑ r ∈ R, ∑ s : ZMod (nP D p), f (orbMap D p r s) = ∑ z, f z := by
  have hpos : 0 < nP D p := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 : ∑ x ∈ R ×ˢ Finset.range (nP D p), f (posPl D p x.1 x.2) = ∑ z : Pl D, f z := by
    refine Finset.sum_bij (fun x _ => posPl D p x.1 x.2) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨r, a⟩ hx ⟨r', b⟩ hx' h
      rw [Finset.mem_product, Finset.mem_range] at hx hx'
      have hr : r = r' := (hR (posPl D p r a)).unique ⟨hx.1, a, rfl⟩ ⟨hx'.1, b, h.symm⟩
      subst hr
      rw [posPl_inj D p r a b hx.2 hx'.2 h]
    · intro z _
      obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
      exact ⟨(r, e % nP D p), Finset.mem_product.2 ⟨hr, Finset.mem_range.2 (Nat.mod_lt _ hpos)⟩,
        by rw [posPl_mod, he]⟩
  rw [← h1, Finset.sum_product]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact sum_zmod (nP D p) (fun a => f (posPl D p r a))

theorem fst_posPl {p : ℕ} (hs : ¬ IsSg D p) (z : Pl D) (e : ℕ) : (posPl D p z e).1 = z.1 := by
  obtain ⟨b, t⟩ := z
  rw [posPl_eq, decide_eq_false (fun h => hs h.1)]; simp

theorem memA_orb (p : ℕ) (r : Pl D) (s : ZMod (nP D p)) : orbMap D p r s ∈ kindA D p ↔ r ∈ kindA D p := by
  unfold kindA orbMap
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← fst_posPl h1 r s.val]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [fst_posPl h1 r s.val]; exact h2⟩

theorem memBC_iff (p : ℕ) (z : Pl D) : z ∈ kindBC D p ↔ z ∉ kindA D p := by
  unfold kindA kindBC
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : IsSg D p
  · constructor
    · intro _ h2; exact h2.1 h
    · intro _; exact Or.inl h
  · constructor
    · rintro (h1 | h1) h2
      · exact h h1
      · rw [h1] at h2; simp at h2
    · intro h2
      right
      cases hz : z.1 with
      | true => rfl
      | false => exact absurd ⟨h, hz⟩ h2

theorem sum_orbBC (p : ℕ) (f : Pl D → ℝ) (R : Finset (Pl D)) (hR : IsReps D p R) :
    ∑ r ∈ R.filter (fun r => r ∉ kindA D p), ∑ s : ZMod (nP D p), f (orbMap D p r s) = ∑ z ∈ kindBC D p, f z := by
  have h := sum_orb p (fun z => if z ∉ kindA D p then f z else 0) R hR
  rw [Finset.sum_filter]
  have e2 : ∑ z ∈ kindBC D p, f z = ∑ z, (if z ∉ kindA D p then f z else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext z; simp [memBC_iff]
  rw [e2, ← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r ∈ kindA D p
  · simp [hr, memA_orb]
  · simp [hr, memA_orb]

theorem sum_orbA (p j : ℕ) (R : Finset (Pl D)) (hR : IsReps D p R) :
    (∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ) = ∑ r ∈ R.filter (fun r => r ∈ kindA D p), FOrb D j p r := by
  have hn : (nP D p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have h := sum_orb p (fun z => if z ∈ kindA D p then FOrb D j p z else 0) R hR
  have e2 : ∑ z ∈ kindA D p, FOrb D j p z = ∑ z, (if z ∈ kindA D p then FOrb D j p z else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext z; simp
  rw [e2, ← h, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r ∈ kindA D p
  · have hc : ∀ s : ZMod (nP D p), (if orbMap D p r s ∈ kindA D p then FOrb D j p (orbMap D p r s) else 0) = FOrb D j p r :=
      fun s => by rw [if_pos ((memA_orb p r s).2 hr)]; exact FOrb_step D j p r s.val
    rw [if_pos hr, Finset.sum_congr rfl (fun s _ => hc s), Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hn]
  · simp [hr, memA_orb]

theorem card_BC (p : ℕ) (R : Finset (Pl D)) (hR : IsReps D p R) :
    ∑ _r ∈ R.filter (fun r => r ∉ kindA D p), (nP D p : ℝ) = ((kindBC D p).card : ℝ) := by
  have h := sum_orbBC p (fun _ => (1 : ℝ)) R hR
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h ⊢
  exact h

theorem tops_BC (p : ℕ) (R : Finset (Pl D)) (hR : IsReps D p R) :
    ∑ r ∈ R.filter (fun r => r ∉ kindA D p), (topsOrb D p r : ℝ) = ((topsBC D p).card : ℝ) := by
  have h := sum_orbBC p (fun z => if IsTopPl D z then (1 : ℝ) else 0) R hR
  have e1 : ∀ r : Pl D, (topsOrb D p r : ℝ) = ∑ s : ZMod (nP D p), (if IsTopPl D (orbMap D p r s) then (1 : ℝ) else 0) := by
    intro r; unfold topsOrb; rw [Finset.card_filter]; push_cast; rfl
  have e2 : ((topsBC D p).card : ℝ) = ∑ z ∈ kindBC D p, (if IsTopPl D z then (1 : ℝ) else 0) := by
    unfold topsBC; rw [Finset.card_filter]; push_cast; rfl
  rw [e2, ← h]
  exact Finset.sum_congr rfl fun r _ => e1 r

theorem sum_g0Pl (X : Inst D L) (K : Consts) (p j : ℕ) :
    ∑ r ∈ repsPl X p, g0Pl X K p j r = ∑ t0 ∈ reps X p, max (g0 X K (aL L) (bL L) p j t0) 0 := by
  have inj : ∀ b : Bool, Function.Injective (fun t : HH D => ((b, t) : Pl D)) := fun b x y h => (Prod.ext_iff.1 h).2
  unfold repsPl
  by_cases hs : IsSg D p
  · rw [if_pos hs, Finset.sum_image (fun x _ y _ h => inj false h)]
    exact Finset.sum_congr rfl fun t _ => by simp [g0Pl]
  · rw [if_neg hs, Finset.sum_union, Finset.sum_image (fun x _ y _ h => inj false h),
      Finset.sum_image (fun x _ y _ h => inj true h)]
    · have : ∑ t ∈ reps X p, g0Pl X K p j (true, t) = 0 := Finset.sum_eq_zero fun t _ => by simp [g0Pl]
      rw [this, add_zero]
      exact Finset.sum_congr rfl fun t _ => by simp [g0Pl]
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨t, _, rfl⟩ := ha
      obtain ⟨t', _, h⟩ := hb
      simp at h

theorem sumI (X : Inst D L) (K : Consts) (ce : ErrC) : OrbitSumBound X K ce := by
  intro p _ hI j _
  have hR := isReps_repsPl X p
  have hc : ¬ (IsResidueClassZero D p ∧ hP D p = 0) := by
    rintro ⟨h1, h2⟩
    rcases hI with h | h
    · exact h.2.ne_zero h2
    · have h3 : D.host.cls p = PrimeClass.inertClass := h1
      have h4 : D.host.cls p = PrimeClass.signal := h
      rw [h4] at h3; simp at h3
  have eF : FInert D j p = ∑ r ∈ repsPl X p, FOrb D j p r := by
    unfold FInert; rw [if_neg hc]; exact sum_orbits D j p _ hR
  have eB : ∑ r ∈ repsPl X p, betaI X K ce j p r = (∑ r ∈ repsPl X p, g0Pl X K p j r) +
      ∑ r ∈ (repsPl X p).filter (fun r => r ∉ kindA D p), (FOrb D j p r - errF L K ce j p r) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold betaI
    by_cases hr : r ∈ kindA D p
    · simp [hr]
    · simp [hr]; ring
  have eS : ∑ r ∈ repsPl X p, FOrb D j p r = (∑ r ∈ (repsPl X p).filter (fun r => r ∈ kindA D p), FOrb D j p r) +
      ∑ r ∈ (repsPl X p).filter (fun r => r ∉ kindA D p), FOrb D j p r :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have eE : ∑ r ∈ (repsPl X p).filter (fun r => r ∉ kindA D p), errF L K ce j p r =
      gam p * ((topsBC D p).card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) +
      ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
        (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
      (K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
        K.dl2 * ((topsBC D p).card : ℝ) * Real.logb p (2 * L.sc.a) ^ 2) := by
    rw [← tops_BC p _ hR, ← card_BC p _ hR, ← sum_orbBC p (wPl D j) _ hR]
    unfold errF
    simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [eB, sum_g0Pl, Finset.sum_sub_distrib, eE, eF, eS]
  unfold EatI
  rw [sum_orbA p j _ hR]
  have hm := le_max_right (0 : ℝ) (∑ r ∈ (repsPl X p).filter (fun r => r ∈ kindA D p), FOrb D j p r)
  have hx : EatX L ce j p = 0 := EatX_of_not L ce j (fun h => by
    rcases hI with h' | h'
    · exact h'.2.not_isCs h
    · have h3 : D.host.cls p = PrimeClass.inertClass := h.1
      have h4 : D.host.cls p = PrimeClass.signal := h'
      rw [h4] at h3; simp at h3)
  linarith

def Core (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : Ent D) (ce : ErrC) (C : ℝ) : Prop :=
  OrbitsAddLowerBound E ∧ OrbitsAddAtConjugate E ∧ OrbitRestriction E ∧ OrbitRestrictionAtConjugate E ∧ OrbitValuationBound E X K ce ∧ EntriesAtDiscriminant E Dx ∧ ValuationSumBound E L ce C ∧ ScaledGeneratorsInSup E L K ce

theorem lift_bounds_of_kernelForm {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Ent D} {lev : LevelData D} {Xe : ErrX D}
    {ce : ErrC} {sp C6 C : ℝ} (hk : KForm E Dx T sp) (hA : AdmK D L X K Dx E ce C6 C) (hC : Core D L X K Dx E ce C) :
    Conclusion₂ D L X K Dx T E lev Xe ce sp C := by
  obtain ⟨ho, hgd, hb, hbc, hall, ha', hint, _, hS, _⟩ := hA
  obtain ⟨c2, c3, c4, c5, c6, c7, c9, c10⟩ := hC
  have c1 := compose D T
  have c8 := sumI X K ce
  have eI := entI_of (isReps_repsPl X) ho hb c2 c6 ha'
  have eC := entC_of ho hbc c3 hall hS
  have lI : OneLiftInertBound D L X K Dx T lev Xe ce sp := liftI_of hk eI c8 ho hbc c10
  have lC : OneLiftAtC D L K Dx T lev Xe ce sp := liftC_of hk ho eC c9
  have lD : OneLiftAtDiscriminant D L K Dx T lev Xe ce sp := liftD_of hk hgd c7
  exact ⟨c1, c2, c3, c4, c5, c6, eI, eC, c7, c8, c9, lI, lC, lD, noOp_of c1 lI, c_of c1 lC, atD_of c1 lD, int_of hk hint⟩

theorem lift_bounds_of_essential {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Ent D} {lev : LevelData D}
    {Xe : ErrX D} {ce : ErrC} {sp C6 C : ℝ} (hA : admitted D L X K Dx T E ce sp C6 C) (hC : Core D L X K Dx E ce C) :
    Conclusion₂ D L X K Dx T E lev Xe ce sp C :=
  lift_bounds_of_kernelForm hA.1 hA.2 hC

theorem kernelAdm_of_values {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Ent D} {V : Vals D Dx T} {ce : ErrC} {sp C6 C : ℝ}
    (hA : AdmV D L X K Dx T E V ce sp C6 C) : admitted D L X K Dx T E ce sp C6 C :=
  ⟨kform_of E Dx T V hA.1 hA.2.1 hA.2.2.1, hA.2.2.2⟩

theorem stmtV_of_stmt {X : Inst D L} {K : Consts} {Dx : DivX D} {C6 C : ℝ} (h : Stmt D L X K Dx C6 C) : LiftBoundsWithValues D L X K Dx C6 C :=
  fun T E _ lev Xe ce sp hsp hA => ⟨(kernelAdm_of_values hA).1, h T E lev Xe ce sp hsp (kernelAdm_of_values hA)⟩

section Ker

variable {Dx : DivX D} {T : TwForms D}

def ofKer (hν : NuRowOK D) (Ek : KerEnt D Dx T) (ep : ∀ w : D.what₂.places.Pl, ℂ_[D.what₂.places.resChar w])
    (be : ∀ w : D.what₂.places.Pl, Pl D → MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w])
    (sg : ∀ w : D.what₂.places.Pl, Pl D → ℂ_[D.what₂.places.resChar w]) : Ent D where
  nu := nuD D
  nu_row := hν
  nu_rows := nuD_rows D
  Th := Ek.Th
  ep := ep
  be := be
  sg := sg

def KmapRat (Ek : KerEnt D Dx T) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl), DV.Used D μ → LevFree Dx u μ w → ∀ i < D.R.m, ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (v : Ek.VQ u μ i c), ∃ v' : Ek.VQ u μ (i + 1) c', Ek.ev u μ (i + 1) c' v' = (D.chTw u μ).Kmap i c c' (Ek.ev u μ i c v)

def Mu0Tie (D : D7) (T : TwForms D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (i : ℕ), i < D.R.m → ∀ s : ℝ, KGeTw T u D.what₂.mu0 w i s → KGe0 D u w i s

def KernelFormRational (hν : NuRowOK D) (Ek : KerEnt D Dx T) (sp : ℝ) : Prop :=
  ConclusionW D → Ek.UnUnit → KmapRat Ek → KFi D T → SupSpansPsiPart D sp → ∀ ep be sg, KForm (ofKer hν Ek ep be sg) Dx T sp

theorem vAdd_inv (w : D.what₂.places.Pl) {a : D.what₂.LL} (ha : a ≠ 0) :
    vAdd (D.plEq w) a⁻¹ = - vAdd (D.plEq w) a := by
  have h := vAdd_mul w ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, vAdd_one] at h
  omega

theorem vAdd_npow (w : D.what₂.places.Pl) {a : D.what₂.LL} (ha : a ≠ 0) (k : ℕ) :
    vAdd (D.plEq w) (a ^ k) = (k : ℤ) * vAdd (D.plEq w) a := by
  induction k with
  | zero => simp [vAdd_one]
  | succ k ih =>
    rw [pow_succ, vAdd_mul w (pow_ne_zero _ ha) ha, ih]
    push_cast; ring

theorem mem_intW_iff (w : D.what₂.places.Pl) {a : D.what₂.LL} (ha : a ≠ 0) :
    a ∈ intW D.what₂.places w ↔ 0 ≤ vAdd (D.plEq w) a := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w a ↔ _
  rw [D.val_eq w _ ha, ← WithTop.coe_zero, WithTop.coe_le_coe]

section Norm

variable (w : D.what₂.places.Pl) (iL : D.what₂.LL →+* ℂ_[D.what₂.places.resChar w])
  (hint : ∀ x, x ∈ intW D.what₂.places w ↔ ‖iL x‖ ≤ 1)

include hint in
theorem norm_le_iff {X Y : D.what₂.LL} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ‖iL X‖ ≤ ‖iL Y‖ ↔ vAdd (D.plEq w) Y ≤ vAdd (D.plEq w) X := by
  have hYn : 0 < ‖iL Y‖ := norm_pos_iff.2 ((map_ne_zero iL).2 hY)
  have h1 : ‖iL (X * Y⁻¹)‖ = ‖iL X‖ / ‖iL Y‖ := by rw [map_mul, map_inv₀, norm_mul, norm_inv, div_eq_mul_inv]
  rw [← div_le_one hYn, ← h1, ← hint, mem_intW_iff w (mul_ne_zero hX (inv_ne_zero hY)),
    vAdd_mul w hX (inv_ne_zero hY), vAdd_inv w hY]
  constructor <;> intro h <;> omega

theorem norm_p : ‖iL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)‖ = ((D.what₂.places.resChar w : ℕ) : ℝ)⁻¹ := by
  rw [map_natCast]
  have h : ‖(((D.what₂.places.resChar w : ℚ_[D.what₂.places.resChar w]) : ℚ_[D.what₂.places.resChar w]) :
      ℂ_[D.what₂.places.resChar w])‖ = ‖(D.what₂.places.resChar w : ℚ_[D.what₂.places.resChar w])‖ :=
    PadicComplex.norm_extends' _ _
  have h2 : (((D.what₂.places.resChar w : ℚ_[D.what₂.places.resChar w]) : ℚ_[D.what₂.places.resChar w]) :
      ℂ_[D.what₂.places.resChar w]) = (D.what₂.places.resChar w : ℂ_[D.what₂.places.resChar w]) := by simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p

include hint in

theorem le_vAdd_of_norm_le {b : D.what₂.LL} (hb : b ≠ 0) {B : ℝ}
    (h : ‖iL b‖ ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-B)) : ur D w B ≤ (vAdd (D.plEq w) b : ℝ) := by
  obtain ⟨k1, k2, hn⟩ : ∃ k1 k2 : ℕ, vAdd (D.plEq w) b = (k1 : ℤ) - (k2 : ℤ) :=
    ⟨(vAdd (D.plEq w) b).toNat, (-(vAdd (D.plEq w) b)).toNat, by omega⟩
  have hp0 := p_ne w
  have hP1 : (1 : ℝ) < ((D.what₂.places.resChar w : ℕ) : ℝ) := by exact_mod_cast (D.what₂.places.resChar_prime w).one_lt
  have hP0 : (0 : ℝ) < ((D.what₂.places.resChar w : ℕ) : ℝ) := lt_trans one_pos hP1
  have hX : b ^ D.what₂.places.ramIdx w * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb) (pow_ne_zero _ hp0)
  have hY : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k1 ≠ 0 := pow_ne_zero _ hp0
  have hv : vAdd (D.plEq w) (b ^ D.what₂.places.ramIdx w * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k2) =
      vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k1) := by
    rw [vAdd_mul w (pow_ne_zero _ hb) (pow_ne_zero _ hp0), vAdd_npow w hb, vAdd_pow, vAdd_pow, hn]
    ring
  have hE : ‖iL (b ^ D.what₂.places.ramIdx w * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k2)‖ =
      ‖iL (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k1)‖ :=
    le_antisymm ((norm_le_iff w iL hint hX hY).2 hv.symm.le) ((norm_le_iff w iL hint hY hX).2 hv.le)
  rw [map_mul, map_pow, map_pow, map_pow, norm_mul, norm_pow, norm_pow, norm_pow, norm_p] at hE
  have hinv : ∀ k : ℕ, (((D.what₂.places.resChar w : ℕ) : ℝ)⁻¹) ^ k = ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-(k : ℝ)) := fun k => by
    rw [Real.rpow_neg hP0.le, Real.rpow_natCast, inv_pow]
  have hle : ‖iL b‖ ^ D.what₂.places.ramIdx w ≤
      ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-B * (D.what₂.places.ramIdx w : ℝ)) := by
    rw [Real.rpow_mul hP0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h _
  rw [hinv, hinv] at hE
  have h3 : ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-(k1 : ℝ)) ≤
      ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-B * (D.what₂.places.ramIdx w : ℝ) + -(k2 : ℝ)) := by
    rw [Real.rpow_add hP0, ← hE]
    exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hP0.le _)
  have h4 := (Real.rpow_le_rpow_left_iff hP1).1 h3
  have h5 : (vAdd (D.plEq w) b : ℝ) = (k1 : ℝ) - (k2 : ℝ) := by exact_mod_cast hn
  unfold ur
  rw [h5]
  linarith

end Norm

def EntK (E : KerEnt D Dx T) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (B : ℝ) : Prop :=
  ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    product_zeroth_first_parts.ExpansionCoeffValuationGe (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nuD D u i) (E.Th u μ w i c c') B

theorem kgeTw_of (E : KerEnt D Dx T) (hU : E.UnUnit) (hR : KmapRat E) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    (hUs : DV.Used D μ) (hL : LevFree Dx u μ w) {i : ℕ} (hi : i < D.R.m) {B : ℝ} (hE : EntK E u μ w i B) {n : ℕ} (hn : n ≠ 0)
    (hdiv : ∀ c, Nat.card ((D.chTw u μ).stab i c) ∣ n)
    (hF : ∀ φ ∈ (T.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (T.fm u μ).Fi (i + 1)) :
    KGeTw T u μ w i (B - (padicValNat (D.what₂.places.resChar w) n : ℝ)) := by
  intro x hx
  obtain ⟨hFi, hv⟩ := (E.lat_S u μ w hL i hi ((T.fm u μ).emb i x)).1 ⟨x, Submodule.subset_span hx, rfl⟩
  choose v hvev hvint using hv
  choose v' hv' using fun c c' => hR u μ w hUs hL i hi c c' (v c)
  have hP1 : (1 : ℝ) < ((D.what₂.places.resChar w : ℕ) : ℝ) := by exact_mod_cast (D.what₂.places.resChar_prime w).one_lt
  have hP0 : (0 : ℝ) < ((D.what₂.places.resChar w : ℕ) : ℝ) := lt_trans one_pos hP1

  have hB : ∀ c c' I, ‖E.prT u μ w i c' (v' c c') I‖ ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-B) := by
    intro c c' I
    rw [E.kform u μ w hL i hi c c' (v c) (v' c c') (hv' c c') I, norm_mul, hU u μ w hL i hi c c', one_mul]
    obtain ⟨cf, hcf, heq⟩ := hE c c' I
    have heq' : KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c')
        (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I) = cf.sum fun J a =>
          a • MvPolynomial.map (Int.castRingHom ℂ_[D.what₂.places.resChar w]) (KM.nablaX (D.R.N i) (nuD D u i) J) := heq
    rw [heq', Finsupp.sum, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hP0.le _) fun J _ => ?_
    rw [map_smul, smul_eq_mul, norm_mul]
    calc ‖cf J‖ * _ ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (-B) * 1 :=
          mul_le_mul (hcf J) (hvint c J) (norm_nonneg _) (Real.rpow_nonneg hP0.le _)
      _ = _ := mul_one _

  obtain ⟨a, hav⟩ := D.what₂.places.val_surj w ⌈ur D w B⌉
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hav
    exact WithTop.top_ne_coe hav
  have hva : vAdd (D.plEq w) a = ⌈ur D w B⌉ := by
    rw [D.val_eq w _ ha0] at hav
    exact WithTop.coe_injective hav
  have hBa : ∀ c c' I, ‖E.iL w a⁻¹‖ * ‖E.prT u μ w i c' (v' c c') I‖ ≤ 1 := by
    intro c c' I
    obtain ⟨b0, hb0⟩ := E.prT_val u μ w hL i hi c' (v' c c') I
    have han : 0 < ‖E.iL w a‖ := norm_pos_iff.2 ((map_ne_zero (E.iL w)).2 ha0)
    rw [map_inv₀, norm_inv, hb0, inv_mul_le_iff₀ han, mul_one]
    by_cases hb : b0 = 0
    · rw [hb, map_zero, norm_zero]; exact han.le
    · refine (norm_le_iff w (E.iL w) (E.iL_int w) hb ha0).2 ?_
      have h1 := le_vAdd_of_norm_le w (E.iL w) (E.iL_int w) hb (hb0 ▸ hB c c' I)
      rw [hva]
      exact Int.ceil_le.2 h1

  have hpp := D.what₂.places.resChar_prime w
  obtain ⟨k, hk⟩ : ∃ k, k = padicValNat (D.what₂.places.resChar w) n := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n', n' = n / D.what₂.places.resChar w ^ n.factorization (D.what₂.places.resChar w) := ⟨_, rfl⟩
  have hfac : n.factorization (D.what₂.places.resChar w) = k := by rw [hk, Nat.factorization_def n hpp]
  have hprod : D.what₂.places.resChar w ^ k * n' = n := by
    rw [hn', ← hfac]; exact Nat.ordProj_mul_ordCompl_eq_self n _
  have hcop : Nat.Coprime n' (D.what₂.places.resChar w) := by
    rw [hn']; exact (Nat.coprime_ordCompl hpp hn).symm
  have hn'0 : n' ≠ 0 := by rintro rfl; simp at hprod; exact hn hprod.symm
  have hcard : ∀ c, Nat.card ((D.chTw u μ).stab i c) ≠ 0 := fun c => Nat.card_pos.ne'
  have hq : ∀ c, n / Nat.card ((D.chTw u μ).stab i c) * Nat.card ((D.chTw u μ).stab i c) =
      D.what₂.places.resChar w ^ k * n' := fun c => by
    rw [hprod]; exact Nat.div_mul_cancel (hdiv c)
  have hq0 : ∀ c, n / Nat.card ((D.chTw u μ).stab i c) ≠ 0 := fun c h0 => by
    have := hq c; rw [h0, zero_mul, hprod] at this; exact hn this.symm
  let r : (D.chTw u μ).cls i → D.what₂.LL := fun c =>
    ((n / Nat.card ((D.chTw u μ).stab i c) : ℕ) : D.what₂.LL) * ((n' : ℕ) : D.what₂.LL)⁻¹
  have hr : ∀ c, r c ∈ intW D.what₂.places w := fun c => by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w (r c)
    rw [AddValuation.map_mul, AddValuation.map_inv, val_coprime w n' hcop, neg_zero, add_zero]
    exact val_nat_nonneg w _
  let pk : D.what₂.LL := ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k
  have hpk : pk ≠ 0 := pow_ne_zero _ (p_ne w)
  have hwt : ∀ c, (D.chTw u μ).wt i c = D.what₂.embLL (pk⁻¹ * r c) := fun c => by
    have e1 : ((n / Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ) * ((Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ) =
        ((D.what₂.places.resChar w : ℕ) : ℂ) ^ k * ((n' : ℕ) : ℂ) := by exact_mod_cast hq c
    have c1 : ((Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hcard c)
    have c2 : ((n / Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hq0 c)
    have c3 : ((D.what₂.places.resChar w : ℕ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hpp.ne_zero)
    have c4 : ((n' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn'0
    show (((Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ))⁻¹ = _
    simp only [pk, r, map_mul, map_inv₀, map_pow, map_natCast]
    field_simp
    linear_combination (-1 : ℂ) * e1
  let b : D.what₂.LL := a * pk⁻¹
  have hb0 : b ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hpk)
  let V' : ∀ c' : (D.chTw u μ).cls (i + 1), E.VQ u μ (i + 1) c' := fun c' => ∑ c, (r c * a⁻¹) • v' c c'
  let ψ : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ := fun c' => E.ev u μ (i + 1) c' (V' c')
  have hK : (D.chTw u μ).K i ((T.fm u μ).emb i x) = D.what₂.embLL b • ψ := by
    funext c'
    show ∑ c, (D.chTw u μ).wt i c • (D.chTw u μ).Kmap i c c' ((T.fm u μ).emb i x c) =
      D.what₂.embLL b • E.ev u μ (i + 1) c' (∑ c, (r c * a⁻¹) • v' c c')
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hvev c, ← hv' c c', hwt c, LinearMap.map_smulₛₗ, smul_smul, ← map_mul]
    congr 2
    simp only [b]
    field_simp
  have hbC : D.what₂.embLL b ≠ 0 := (map_ne_zero D.what₂.embLL).2 hb0
  have hψF : ψ ∈ (T.fm u μ).Fi (i + 1) := by
    have : ψ = (D.what₂.embLL b)⁻¹ • (D.chTw u μ).K i ((T.fm u μ).emb i x) := by
      rw [hK, smul_smul, inv_mul_cancel₀ hbC, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (hF _ hFi)
  have hV' : ∀ c' I, ‖E.prT u μ w i c' (V' c') I‖ ≤ 1 := by
    intro c' I
    show ‖E.prT u μ w i c' (∑ c, (r c * a⁻¹) • v' c c') I‖ ≤ 1
    rw [map_sum, Finset.sum_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun c _ => ?_
    rw [LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, norm_mul, mul_assoc]
    calc ‖E.iL w (r c)‖ * (‖E.iL w a⁻¹‖ * ‖E.prT u μ w i c' (v' c c') I‖) ≤ 1 * 1 :=
          mul_le_mul ((E.iL_int w _).1 (hr c)) (hBa c c' I) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
      _ = 1 := mul_one _
  obtain ⟨z, hz, hzψ⟩ := (E.levelFree_lattice_condition u μ w hL i hi ψ).2 ⟨hψF, fun c' => ⟨V' c', rfl, hV' c'⟩⟩
  refine ⟨b • z, ?_, b, z, hz, rfl, Or.inr ?_⟩
  · rw [LinearMap.map_smulₛₗ, hzψ, hK]
  · have h1 : ur D w B ≤ (vAdd (D.plEq w) a : ℝ) := by rw [hva]; exact Int.le_ceil _
    have h2 : vAdd (D.plEq w) a = vAdd (D.plEq w) b + (k : ℤ) * (D.what₂.places.ramIdx w : ℤ) := by
      rw [← vAdd_pow w k, ← vAdd_mul w hb0 hpk]
      congr 1
      simp only [b]; rw [mul_assoc, inv_mul_cancel₀ hpk, mul_one]
    rw [← hk]
    have h3 : (vAdd (D.plEq w) a : ℝ) = (vAdd (D.plEq w) b : ℝ) + (k : ℝ) * (D.what₂.places.ramIdx w : ℝ) := by
      exact_mod_cast h2
    unfold ur at h1 ⊢
    nlinarith [h1, h3]

theorem K_heq {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C C' : ColumnChain R ι hc} (h : C = C') (i : ℕ)
    {φ : C.cls i → C.Y i → ℂ} {φ' : C'.cls i → C'.Y i → ℂ} (hφ : HEq φ φ') : HEq (C.K i φ) (C'.K i φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem eMu0_symm_loc (T : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (j : ℕ) (hj : j ≤ D.R.m)
    (z : ((T.fm u D.what₂.mu0).lat j).V) (hz : z ∈ locW D.what₂.places w ((T.fm u D.what₂.mu0).lat j).L) :
    (T.eMu0 u j hj).symm z ∈ locW D.what₂.places w ((D.fm u).lat j).L := by
  unfold locW at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span ((T.eMu0_lat u j hj _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hx))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul]
    exact Submodule.smul_mem _ r hx

theorem kernelValuation_of_twisted (T : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl) {i : ℕ} (hi : i < D.R.m) {s : ℝ}
    (h : KGeTw T u D.what₂.mu0 w i s) : KGe0 D u w i s := by
  intro x hx
  obtain ⟨y', e', a, z', hz', rfl, ha⟩ := h _ ((T.eMu0_lat u i hi.le x).1 hx)
  refine ⟨(T.eMu0 u (i + 1) hi).symm (a • z'), ?_, a, (T.eMu0 u (i + 1) hi).symm z',
    eMu0_symm_loc T u w (i + 1) hi z' hz', by rw [map_smul], ha⟩
  have h1 := T.eMu0_emb u (i + 1) hi ((T.eMu0 u (i + 1) hi).symm (a • z'))
  rw [LinearEquiv.apply_symm_apply] at h1
  have h3 := K_heq (D.memberColumns_twistedChain_base u) i (T.eMu0_emb u i hi.le x)
  exact eq_of_heq (h1.symm.trans ((heq_of_eq e').trans h3))

def SB (E : KerEnt D Dx T) : Prop :=
  ∀ u μ (w : D.what₂.places.Pl) (i : ℕ) c c' (B : ℝ),
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nuD D u i) (E.Th u μ w i c c') B →
    product_zeroth_first_parts.ExpansionCoeffValuationGe (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nuD D u i) (E.Th u μ w i c c') B

theorem kform_of_ker (E : KerEnt D Dx T) (Ee : Ent D) (hν : ∀ u i, Ee.nu u i = nuD D u i) (hTh : Ee.Th = E.Th)
    (hSB : SB E) (hU : E.UnUnit) (hR : KmapRat E) (hK : KFi D T) {sp : ℝ} (hsp : SupSpansPsiPart D sp) : KForm Ee Dx T sp := by
  intro hG u μ w hUs hL i hi B hB
  have hEK : EntK E u μ w i B := by
    intro c c'
    have := hB c c'
    rw [hν u i, hTh] at this
    exact hSB u μ w i c c' B this
  have key : KGeTw T u μ w i (B - (if i = 0 then 1 - sp else 1) * vDG D u w) := by
    by_cases h0 : i = 0 ∧ sp = 1
    · obtain ⟨h0, h1⟩ := h0
      have hS : Stab0 D := by
        rcases hsp with h | h
        · rw [h1] at h; norm_num at h
        · exact h.2
      subst h0
      have := kgeTw_of E hU hR hUs hL hi hEK one_ne_zero (fun c => by rw [hS.2 u μ hUs c]) (hK.2 u μ hUs 0 hi)
      have e : B - (if (0 : ℕ) = 0 then 1 - sp else 1) * vDG D u w =
          B - (padicValNat (D.what₂.places.resChar w) 1 : ℝ) := by simp [h1]
      rw [e]
      exact this
    · have e : B - (if i = 0 then 1 - sp else 1) * vDG D u w = B - vDG D u w := by
        by_cases hi0 : i = 0
        · have hs0 : sp = 0 := by
            rcases hsp with h | h
            · exact h
            · exact absurd ⟨hi0, h.1⟩ h0
          rw [if_pos hi0, hs0]; ring
        · rw [if_neg hi0]; ring
      rw [e]
      have := kgeTw_of E hU hR hUs hL hi hEK (D.chTw u μ).DGam_pos.ne' (fun c => (D.chTw u μ).dvd_DGam i hi.le c) (hK.2 u μ hUs i hi)
      rw [hG.one u u μ] at this
      exact this
  refine ⟨fun hμ => ?_, fun _ => key⟩
  subst hμ
  exact kernelValuation_of_twisted T u w hi key

theorem stmtK (hν : NuRowOK D) (Ek : KerEnt D Dx T) (sp : ℝ) : KernelFormRational hν Ek sp := by
  intro hW hU hR hK hsp ep be sg
  exact kform_of_ker Ek (ofKer hν Ek ep be sg) (fun _ _ => rfl) rfl
    (fun u μ w i c c' B h => (hW _ _ _ _ _ B).1 h) hU hR hK hsp

end Ker

end Formalism.MainNotions.OrbitPlaces

end
