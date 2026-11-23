import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataForced

open Formalism.MainNotions.G NumberField

noncomputable section

namespace Formalism.BasicNotions

instance factResChar (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((MvPolynomial.coeff μ P : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def nuD (D : D7) (u : D.what₂.Word) (i : ℕ) (z : Bool × HH D) : YoungDiagram where
  cells := ((Finset.range (D.R.N i)) ×ˢ (Finset.range ⌈DV.nuRow D u (i + 1) (tauPl D z) 0⌉₊)).filter
    fun x => ∀ r' ≤ x.1, (x.2 : ℝ) < DV.nuRow D u (i + 1) (tauPl D z) r'
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    have hb1 : b.1 ≤ a.1 := hba.1
    have hb2 : b.2 ≤ a.2 := hba.2
    refine ⟨⟨lt_of_le_of_lt hb1 h1, lt_of_le_of_lt hb2 h2⟩, fun r' hr' => ?_⟩
    exact lt_of_le_of_lt (by exact_mod_cast hb2) (h3 r' (le_trans hr' hb1))

theorem nuD_rows (D : D7) (u : D.what₂.Word) (i : ℕ) (z : Bool × HH D) : (nuD D u i z).colLen 0 ≤ D.R.N i := by
  by_contra hlt
  have hmem : (D.R.N i, 0) ∈ nuD D u i z := YoungDiagram.mem_iff_lt_colLen.2 (not_le.1 hlt)
  have : (D.R.N i, 0) ∈ (nuD D u i z).cells := hmem
  simp only [nuD, Finset.mem_filter, Finset.mem_product, Finset.mem_range, lt_irrefl, false_and] at this

def NuRowOK (D : D7) : Prop :=
  ∀ u i, i < D.R.m → ∀ z r, (((nuD D u i z).rowLen r : ℕ) : ℝ) =
    if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0

def LevFree {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∧
    D.what₂.places.resChar w ∉ Dx.Qp μ

open Classical in

def lamV {p : ℕ} [Fact p.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  if h : x ∈ algebraicClosure ℚ ℂ then lam ⟨x, h⟩ else 0

structure KerEnt (D : D7) (Dx : DivX D) (Tw : TwForms D) where

  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_lam : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x)
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

  Th : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
    MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]

  VQ : ∀ u μ (i : ℕ), (D.chTw u μ).cls i → Type
  [vqAcg : ∀ u μ i c, AddCommGroup (VQ u μ i c)]
  [vqMod : ∀ u μ i c, Module D.what₂.LL (VQ u μ i c)]
  ev : ∀ u μ i c, VQ u μ i c →ₛₗ[D.what₂.embLL] ((D.chTw u μ).Y i → ℂ)
  ev_inj : ∀ u μ i c, Function.Injective (ev u μ i c)

  prS : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i), VQ u μ i c →ₛₗ[iL w]
    Module.Dual ℂ_[D.what₂.places.resChar w]
      (MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N i)) ℂ_[D.what₂.places.resChar w])

  prT : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)), VQ u μ (i + 1) c' →ₛₗ[iL w]
    (KM.ColChoice (D.R.N (i + 1)) (nuD D u i) → ℂ_[D.what₂.places.resChar w])

  prT_val : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ c' (v' : VQ u μ (i + 1) c') I,
    ∃ b : D.what₂.LL, ‖prT u μ w i c' v' I‖ = ‖iL w b‖

  lat_S : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ,
    (∃ x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L, (Tw.fm u μ).emb i x = φ) ↔
      (φ ∈ (Tw.fm u μ).Fi i ∧ ∀ c, ∃ v : VQ u μ i c, ev u μ i c v = φ c ∧
        ∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
          ‖prS u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1)

  levelFree_lattice_condition : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m →
    ∀ φ : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ,
    (∃ y ∈ locW D.what₂.places w ((Tw.fm u μ).lat (i + 1)).L, (Tw.fm u μ).emb (i + 1) y = φ) ↔
      (φ ∈ (Tw.fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : VQ u μ (i + 1) c', ev u μ (i + 1) c' v' = φ c' ∧
        ∀ I, ‖prT u μ w i c' v' I‖ ≤ 1)

  un : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) → ℂ_[D.what₂.places.resChar w]
  un_ne : ∀ u μ w i c c', un u μ w i c c' ≠ 0

  kform : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (v : VQ u μ i c) (v' : VQ u μ (i + 1) c'),
    ev u μ (i + 1) c' v' = (D.chTw u μ).Kmap i c c' (ev u μ i c v) →
    ∀ I, prT u μ w i c' v' I =
      un u μ w i c c' *
        prS u μ w i c v (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (Th u μ w i c c')
          (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))

attribute [instance] KerEnt.vqAcg KerEnt.vqMod

namespace KerEnt

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

def UnUnit : Prop :=
  ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ c c', ‖E.un u μ w i c c'‖ = 1

def valS (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) :
    Set ((D.chTw u μ).Y i → ℂ) :=
  E.ev u μ i c '' {v | ∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
    ‖E.prS u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1}

def valT (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) :
    Set ((D.chTw u μ).Y (i + 1) → ℂ) :=
  E.ev u μ (i + 1) c' '' {v' | ∀ I, ‖E.prT u μ w i c' v' I‖ ≤ 1}

end KerEnt

def linAt {σ κ : Type*} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries κ ℂ_[p] :=
  MvPowerSeries.subst (fun k : σ => ∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * MvPowerSeries.X x) F

def posJ {D : D7} (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) :
    (j : ℕ) → ((Σ v : Fin (Fl.Pj j).nV, Fin ((Fl.Pj j).n' v)) ≃ D.what₂.Tau)
  | 0 => Gt.gat_pos u w h
  | _ + 1 => Gt.gat_pos u w h

def rhoMat {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (τ : D.what₂.Tau)
    (g : ∀ v, Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v)) :
    Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
  (g ((posJ Gt u w h Fl j).symm τ).1).map fun y =>
    Kp.iK ((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1
      ((((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val) y))

open Classical in

def ThAtServed {D : D7} {Dx : DivX D} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word}
    {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)}
    {Lv : Levels Fl} {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (E : KerEnt D Dx Tw) : Prop :=
  Kp.lam = E.lam w ∧
  ∃ g : ∀ (j : ℕ) (_ : Lv.comp j × (Fl.Pj j).Tup) (v : Fin (Fl.Pj j).nV),
      Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v),
    (∀ j, j ≤ D.R.m → ∀ La : Lv.comp j × (Fl.Pj j).Tup, (Fl.Pj j).IsLatTup La.2 →
      ∀ v, IsUnit (g j La v).det ∧ La.2 v = colSpan ((Fl.Pj j).W v) (g j La v)) ∧
    ∀ j, j < D.R.m → ∀ (hN : (Fl.Pj j).m + 1 = D.R.N j) (hN' : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1))
      (La : Lv.comp j × (Fl.Pj j).Tup) (La' : Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup),
      (Fl.Pj j).IsLatTup La.2 → (Fl.Pj (j + 1)).IsLatTup La'.2 →
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u (D.what₂.muAt w) w j (Kp.cls j La.1 La.2) (Kp.cls (j + 1) La'.1 La'.2) =
          linAt (fun (k : D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1))
              (x : (Bool × HH D) × Fin (D.R.N j) × Fin (D.R.N (j + 1))) =>
            if tauPl D x.1 = k.1 then
              (if IsTypeV ((posJ Gt u w h Fl j).symm k.1).2 then
                c0 k.1 * (rhoMat Kp (j + 1) k.1 (g (j + 1) La')) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat Kp j k.1 (g j La))⁻¹) (Fin.cast hN.symm x.2.1) k.2.2
              else
                c0 k.1 * (((rhoMat Kp (j + 1) k.1 (g (j + 1) La'))⁻¹).transpose) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat Kp j k.1 (g j La)).transpose) (Fin.cast hN.symm x.2.1) k.2.2)
            else 0) (Kp.Th j La La')

end Formalism.BasicNotions
