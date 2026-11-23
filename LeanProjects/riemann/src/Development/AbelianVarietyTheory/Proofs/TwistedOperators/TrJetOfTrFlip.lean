import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.SignedHC Formalism.L2.Ker Matrix MvPolynomial

namespace GlobalTheory.RowEx.Jet

section One

variable {D : D7}

variable (D) in

abbrev Raw (S T : HSp D) : Type := Finset (Pl D.host.E) × AE D × (WO S T → ℂ) × GA D S

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

abbrev homO (S T : HSp D) (LS : Lat S) (LT : Lat T) : AddSubgroup (WO S T) := latO S T (LS : Set _) (LT : Set _) fun _ => True

def Ok (ov : Pl D.host.E → Prop) (S T : HSp D) (LS : Lat S) (LT : Lat T) (r : Raw D S T) : Prop :=
  (∀ w ∈ r.1, ov w) ∧ IsIdemSum r.2.1 r.1 ∧ IsSBHalf r.2.1 (homO S T LS LT) r.2.2.1 ∧
    (∃ c : AE D, mt _ r.2.2.2 = c • (1 : Matrix _ _ (AE D))) ∧
    ∃ (P' : Finset (Pl D.host.E)) (e' : AE D), IsIdemSum e' P' ∧ SuppAt e' _ r.2.2.2 ∧ ∀ w ∈ P',
      FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∨ FractionalIdeal.count D.host.E w D.host.AAbar ≠ 0

def raw {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {t : T} {p : Pair T} (d : FinDatum G t p) :
    Raw D (G.pS p) (G.pT p) := (d.P, d.e, d.fn, d.z)

def overPl (S0 : Finset (Pl D.host.F)) (Q : Finset (Pl D.host.E)) (w : Pl D.host.E) : Prop :=
  w.under (𝓞 D.host.F) ∈ S0 ∨ ∃ w' ∈ Q, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F)

def datEquiv {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) (p : Pair T) :
    FinDatum G t p ≃ Subtype (Ok (overPl G.pl.S0 (L.Q t)) (G.pS p) (G.pT p) (G.latS p) (G.latT p)) where
  toFun d := ⟨raw d, d.P_over, d.e_is, d.sb, d.z_cen, d.z_supp⟩
  invFun r := ⟨r.1.1, r.2.1, r.1.2.1, r.2.2.1, r.1.2.2.1, r.2.2.2.1, r.1.2.2.2, r.2.2.2.2.1, r.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (D) in

structure Env where

  P : Finset (Pl D.host.E)

  ov : Pl D.host.E → Prop

  Vt : ℕ → HSp D

  Vr : ℕ → HSp D

  Λt : ∀ j, Lat (Vt j)

  Λr : ∀ i, Lat (Vr i)

  βt : ∀ j, GL (Fin (Vt j).rank) (Lev.EAf D)

  βr : ∀ i, GL (Fin (Vr i).rank) (Lev.EAf D)

  ht : ∀ (w : Pl D.host.E) j, j ≤ D.R.m → topRank (bareGrid w) j = (Vt j).rank

  hr : ∀ (w : Pl D.host.E) i, i ≤ D.R.m → (bareGrid w).rank (i, D.R.m) = (Vr i).rank

  dat : ∀ w : P, ColArgs (bareGrid w.1) → RowArgs (bareGrid w.1) → ℂ

  pr : ∀ w : P, ∀ j, 0 < j → j < D.R.m → Subgroup (GL (Fin (topRank (bareGrid w.1) j)) (Kw w.1))

  J : ∀ w : P, (bareGrid w.1).Level

  modulus : Ideal (𝓞 D.host.E)

  emb : GfC (Vr D.R.m) → GfC (Vt D.R.m)

namespace Env

variable (E : Env D)

abbrev Pure : Type := (∀ j : Fin D.R.m, Subtype (Ok E.ov (E.Vt j) (E.Vt (j + 1)) (E.Λt j) (E.Λt (j + 1)))) ×
  ∀ i : Fin D.R.m, Subtype (Ok E.ov (negSp (E.Vr (i + 1))) (E.Vr i) (E.Λr (i + 1)) (E.Λr i))

def colAt (w : Pl D.host.E) (x : ∀ j : Fin D.R.m, WO (E.Vt j) (E.Vt (j + 1))) : ColArgs (bareGrid w) := fun j =>
  if h : j < D.R.m then (((loc w (E.βt (j + 1)))⁻¹).val * Matrix.map (x ⟨j, h⟩) ((cpt w).comp (toEAf D)) *
    (loc w (E.βt j)).val).submatrix (Fin.cast (E.ht w _ h)) (Fin.cast (E.ht w _ h.le)) else 0

def rowAt (w : Pl D.host.E) (y : ∀ i : Fin D.R.m, WO (negSp (E.Vr (i + 1))) (E.Vr i)) : RowArgs (bareGrid w) := fun i =>
  if h : i < D.R.m then (((((loc w (E.βr i))⁻¹).val * Matrix.map (y ⟨i, h⟩) ((cpt w).comp (toEAf D)) *
    (loc w (E.βr (i + 1))).val).submatrix (Fin.cast (E.hr w _ h.le)) (Fin.cast (E.hr w _ h)))ᵀ)ᵀ else 0

def IsCos {m n : ℕ} (k : ℕ) (Λ : AddSubgroup (Mx D m n)) (e : AE D) (f : Mx D m n → ℂ) : Prop :=
  ∃ x₀, IsHalf e x₀ ∧ k • x₀ ∈ Λ ∧ f = (halfCoset e Λ k x₀).indicator 1

def CosExp (k : ℕ) (τ : E.Pure →₀ ℂ) : Prop :=
  0 < k ∧ (∃ e : AE D, IsIdemSum e E.P ∧
    (∀ d ∈ τ.support, (∀ j, (d.1 j).1.1 = E.P ∧ (d.1 j).1.2.1 = e ∧ (d.1 j).1.2.2.2 = 1) ∧
      ∀ i, (d.2 i).1.1 = E.P ∧ (d.2 i).1.2.1 = e ∧ (d.2 i).1.2.2.2 = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (E.Vt j) (E.Vt (j + 1))) (y : ∀ i : Fin D.R.m, WO (negSp (E.Vr (i + 1))) (E.Vr i)),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
      (τ.sum fun d c => c * (∏ j, (d.1 j).1.2.2.1 (x j)) * ∏ i, (d.2 i).1.2.2.1 (y i)) =
        ∏ w, E.dat w (E.colAt w x) (E.rowAt w y)) ∧
    ∀ d ∈ τ.support, (∀ j, IsCos k (homO _ _ (E.Λt _) (E.Λt _)) (d.1 j).1.2.1 (d.1 j).1.2.2.1) ∧
      ∀ i : Fin D.R.m, IsCos k (homO (negSp (E.Vr (i + 1))) (E.Vr i) (E.Λr _) (E.Λr _)) (d.2 i).1.2.1 (d.2 i).1.2.2.1

def levTop : ∀ j, j < D.R.m → Subgroup (GL (Fin (E.Vt j).rank) (Lev.EAf D))
  | 0, _ => congLev D.sp.cm (E.Vt 0).gram (E.Λt 0) E.modulus
  | j + 1, h => prodLev (E.βt (j + 1)) E.P (fun w => E.ht w _ h.le) fun w => E.pr w _ j.succ_pos h

def levRow (i : ℕ) (h : i ≤ D.R.m) : Subgroup (GL (Fin (E.Vr i).rank) (Lev.EAf D)) :=
  prodLev (E.βr i) E.P (fun w => E.hr w _ h) fun w => E.J w (i, D.R.m)

abbrev Classes : Type :=
  (∀ j : Fin D.R.m, FinCl _ (E.levTop j j.2)) × ∀ i : Fin (D.R.m + 1), FinCl _ (E.levRow i (Nat.le_of_lt_succ i.2))

def ptRow (c : E.Classes) (i : ℕ) : GfC (E.Vr i) := if h : i < D.R.m + 1 then (c.2 ⟨i, h⟩).out else 1

def ptTop (c : E.Classes) : ∀ j, GfC (E.Vt j) :=
  Function.update (fun j => if h : j < D.R.m then (c.1 ⟨j, h⟩).out else 1) D.R.m (E.emb (E.ptRow c D.R.m))

abbrev KT : Type := ∀ j, Raw D (E.Vt j) (E.Vt (j + 1)) → GfC (E.Vt j) → GfC (E.Vt (j + 1)) → Prop

abbrev KR : Type := ∀ i, Raw D (negSp (E.Vr (i + 1))) (E.Vr i) → GfC (E.Vr i) → GfC (E.Vr (i + 1)) → Prop

def Jets (a : E.KT) (b : E.KR) : Prop :=
  ∀ τ, E.CosExp (sInf {k | ∃ τ, E.CosExp k τ}) τ → ∀ d ∈ τ.support, ∀ c : E.Classes,
    (∀ j : Fin D.R.m, a j (d.1 j).1 (E.ptTop c j) (E.ptTop c (j + 1))) ∧
      ∀ i : Fin D.R.m, b i (d.2 i).1 (E.ptRow c i) (E.ptRow c (i + 1))

theorem Jets.mono {E : Env D} {a a' : E.KT} {b b' : E.KR} (H : E.Jets a b) (ha : ∀ j, j < D.R.m → ∀ r x y, a j r x y → a' j r x y)
    (hb : ∀ j, j < D.R.m → ∀ r x y, b j r x y → b' j r x y) : E.Jets a' b' := fun τ h d hd c =>
  ⟨fun j => ha _ j.2 _ _ _ ((H τ h d hd c).1 j), fun j => hb _ j.2 _ _ _ ((H τ h d hd c).2 j)⟩

end Env

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
  (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)

def envOf : Env D where
  P := locPl G t
  ov := overPl G.pl.S0 (L.Q t)
  Vt j := G.V (.top j)
  Vr i := G.V (.grid i D.R.m)
  Λt j := G.Λ (.top j)
  Λr i := G.Λ (.grid i D.R.m)
  βt := S.βp
  βr i := S.B.β i D.R.m
  ht w _ h := topRank_eq G t w h
  hr w i h := rank_vertex G t w (X := (i, D.R.m)) ⟨h, le_rfl⟩
  dat w := (S.term t Φ β w).datum
  pr w := (S.term t Φ β w).pr
  J w := givenLevel G t w
  modulus := G.modul
  emb := finEmb G.sp.topDec

def pureEquiv : PureDat G t ≃ (envOf S t Φ β).Pure :=
  (Equiv.piCongrRight fun j : Fin D.R.m => datEquiv G t (.top t j)).prodCongr
    (Equiv.piCongrRight fun i : Fin D.R.m => datEquiv G t (.chi i D.R.m))

theorem cosExp_iff (k : ℕ) (τ : PureDat G t →₀ ℂ) :
    (envOf S t Φ β).CosExp k (τ.equivMapDomain (pureEquiv S t Φ β)) ↔ IsCosetExpansion S t Φ β k τ := by
  have h1 : ∀ p : (envOf S t Φ β).Pure → Prop, (∀ d ∈ (τ.equivMapDomain (pureEquiv S t Φ β)).support, p d) ↔
      ∀ d ∈ τ.support, p (pureEquiv S t Φ β d) := fun p => by
    rw [← (pureEquiv S t Φ β).forall_congr_right]
    simp
  unfold Env.CosExp
  simp only [h1, Finsupp.sum_equivMapDomain]
  exact Iff.rfl

theorem jets_iff {a : (envOf S t Φ β).KT} {b : (envOf S t Φ β).KR} : (envOf S t Φ β).Jets a b ↔
    ∀ τ, IsCosetExpansion S t Φ β (expDepth S t Φ β) τ → ∀ d ∈ τ.support, ∀ c : S.Classes t Φ β,
      (∀ j : Fin D.R.m, a j (raw (d.1 j)) (S.ptTop c j) (S.ptTop c (j + 1))) ∧
        ∀ i : Fin D.R.m, b i (raw (d.2 i)) (S.ptRow c i) (S.ptRow c (i + 1)) := by
  have e : sInf {k | ∃ τ, (envOf S t Φ β).CosExp k τ} = expDepth S t Φ β := by
    unfold expDepth
    congr 2
    funext k
    rw [← (Finsupp.equivCongrLeft (pureEquiv S t Φ β)).exists_congr_right]
    simp only [Finsupp.equivCongrLeft_apply, cosExp_iff]
  unfold Env.Jets
  rw [e, ← (Finsupp.equivCongrLeft (pureEquiv S t Φ β)).forall_congr_right]
  refine forall_congr' fun τ => ?_
  rw [Finsupp.equivCongrLeft_apply, cosExp_iff, ← (pureEquiv S t Φ β).forall_congr_right]
  refine imp_congr_right fun _ => forall_congr' fun d => imp_congr (by simp) ?_
  exact Iff.rfl

end One

section Ker

variable {D : D7}

def IsTh (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (r : Raw D S T)
    (f : WO S T → ℂ) : Prop :=
  AllSome (fun M : (WO S T → ℂ) →ₗ[ℂ] WO S T → ℂ =>
    (∀ Φ, IsSBHalf r.2.1 (homO S T LS LT) Φ → ∀ x, IsHalf r.2.1 x → (M fun t => Φ (t + x)) = heisO ψ S T x (M Φ)) ∧
    (∀ Φ, IsSBHalf r.2.1 (homO S T LS LT) Φ → ∀ y, IsHalf (cA D r.2.1) y →
      (M fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y (M Φ)) ∧
    M ((1 : ℂ) • halfInd r.2.1 (homO S T LS LT)) = f₀) fun M => f = M r.2.2.1

def KerIn {K : Type} [Field K] (σ : K →+* ℂ) (S T : HSp D) {a b : ℕ} (lam : D.what₂.Tau → DomWeight a)
    (lam' : D.what₂.Tau → DomWeight b) (fv : DVar D.what₂.Tau a b → FVar D T.rank S.rank) (op : ℂ →+* ℂ)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (fS : GL (Fin S.rank) D.host.E) (fT : GL (Fin T.rank) D.host.E) (vac : WO S T → ℂ) (c0 : ℂˣ) (δ : ℂ) (r : Raw D S T)
    (g : GA D S) (h : GA D T) : Prop :=
  ∀ x y, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ lam')
    ((((c0⁻¹ : ℂˣ) : ℂ) * ∏ τ, op ((1 : D.what₂.Tau → ℂ) τ / period δ τ) ^ ∑ i, (lam' τ).natW i) •
      jetOp lam lam' (fun k => thetaKO om g h (pureTensorO ψ θ S T sS sT (fun τ => fS.1.map (tauE D τ))
        (fun τ => fT.1.map (tauE D τ)) (om (r.2.2.2, 1) (Classical.epsilon (IsTh ψ S T (colLat fS) (colLat fT) vac r)))
        (monomial (k.mapDomain fv) 1))) fun τ => if h : a - 1 < b then (lam' τ).natW ⟨_, h⟩ else 0) x y ∈ Set.range σ

def KerTop {K : Type} [Field K] (σ : K →+* ℂ) (c : ℝ) (j : ℕ) (A B : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sA : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ)
    (sB : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ) (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
    (fA : GL (Fin A.rank) D.host.E) (fB : GL (Fin B.rank) D.host.E) (uA : GA D A) (uB : GA D B)
    (vac : WO A B → ℂ) (c0 : ℂˣ) (δ : ℂ) (r : Raw D A B) (x : GfC A) (y : GfC B) : Prop :=
  KerIn σ A B (fun τ => wtOf A.rank (entries (Node.par D c (.top j) τ)))
    (fun τ => wtOf B.rank (entries (Node.par D c (.top (j + 1)) τ))) id (RingHom.id ℂ) ψ θ sA sB om fA fB vac c0 δ r
    (x.1 * uA) (y.1 * uB)

def KerRow {K : Type} [Field K] (σ : K →+* ℂ) (c : ℝ) (i : ℕ) (A B : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sA : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ)
    (sB : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (om : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ))
    (fA : GL (Fin A.rank) D.host.E) (fB : GL (Fin B.rank) D.host.E) (uA : GA D A) (uB : GA D B)
    (vac : WO (negSp B) A → ℂ) (c0 : ℂˣ) (δ : ℂ) (r : Raw D (negSp B) A) (x : GfC A) (y : GfC B) : Prop :=
  KerIn σ (negSp B) A (fun τ => (wtOf A.rank (entries (Node.par D c (.grid i D.R.m) τ))).dual)
    (fun τ => (wtOf B.rank (entries (Node.par D c (.grid (i + 1) D.R.m) τ))).dual) (fun k => (k.1, k.2.2, k.2.1))
    (starRingEnd ℂ) ψ θ (fun τ => -sB τ) sA om fB fA vac c0 δ r (negGA B (y.1 * uB)) (x.1 * uA)

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
  {K : Type} [Field K] (σ : K →+* ℂ) (S : GridChoice W U) (t : T)

theorem isTheta_eq {p : Pair T} (d : FinDatum G t p) (LS LT f₀) : d.IsTheta W LS LT f₀ = IsTh W.ψ _ _ LS LT f₀ (raw d) := by
  funext f
  unfold FinDatum.IsTheta IsThetaAt IsTh
  congr 1
  funext M
  exact propext ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

def topOf (j : ℕ) : Raw D (G.V (.top j)) (G.V (.top (j + 1))) → GfC (G.V (.top j)) → GfC (G.V (.top (j + 1))) → Prop :=
  KerTop σ sc.cGap j _ _ W.ψ W.θ (W.cart (.top j)) (W.cart (.top (j + 1))) (W.om (.top t j)) (S.N.fr (.top j))
    (S.N.fr (.top (j + 1))) (S.N.u (.top j)).1 (S.N.u (.top (j + 1))).1 (S.Z.vac (.top t j)) (S.Z.c0 (.top t j)) S.Z.δ

def rowOf (i : ℕ) : Raw D (negSp (G.V (.grid (i + 1) D.R.m))) (G.V (.grid i D.R.m)) → GfC (G.V (.grid i D.R.m)) →
    GfC (G.V (.grid (i + 1) D.R.m)) → Prop :=
  KerRow σ sc.cGap i _ _ W.ψ W.θ (W.cart (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.om (.chi i D.R.m))
    (S.N.fr (.grid i D.R.m)) (S.N.fr (.grid (i + 1) D.R.m)) (S.N.u (.grid i D.R.m)).1 (S.N.u (.grid (i + 1) D.R.m)).1
    (S.Z.vac (.chi i D.R.m)) (S.Z.c0 (.chi i D.R.m)) S.Z.δ

theorem topOf_iff {j : ℕ} (d : FinDatum G t (.top t j)) (x y) :
    topOf σ S t j (raw d) x y ↔ ∀ a b, S.Z.kk d x y a b ∈ Set.range σ := by
  unfold Normal.kk Normal.kkIn Normal.kkMap Normal.vec FinDatum.vec
  rw [isTheta_eq]
  exact Iff.rfl

theorem rowOf_iff {i : ℕ} (d : FinDatum G t (.chi i D.R.m)) (x y) :
    rowOf σ S i (raw d) x y ↔ ∀ a b, S.Z.kk d x y a b ∈ Set.range σ := by
  unfold Normal.kk Normal.kkIn Normal.kkMap Normal.vec FinDatum.vec
  rw [isTheta_eq]
  exact Iff.rfl

theorem jetsIn_iff (Φ β) : JetsIn σ S t Φ β ↔ (envOf S t Φ β).Jets (topOf σ S t) (rowOf σ S) := by
  refine Iff.trans ?_ (jets_iff S t Φ β).symm
  refine forall_congr' fun τ => imp_congr_right fun _ => forall_congr' fun d => imp_congr_right fun _ => forall_congr' fun c => ?_
  exact and_congr (forall_congr' fun j => (topOf_iff σ S t _ _ _).symm) (forall_congr' fun j => (rowOf_iff σ S t _ _ _).symm)

end Ker

section Two

variable {X X' : Stages}

theorem kerTop_congr (hp : X'.B.toPre = X.B.toPre) {K : Type} [Field K] (σ : K →+* ℂ) (c : ℝ) (j : ℕ) {A B : HSp X.toD7}
    {A' B' : HSp X'.toD7} {ψ ψ' θ θ' sA sA' sB sB' om om' fA fA' fB fB' uA uA' uB uB' vac vac' c0 c0' δ δ' r r' x x' y y'}
    (h1 : HEq A' A) (h2 : HEq B' B) (h3 : HEq ψ' ψ) (h4 : HEq θ' θ) (h5 : HEq sA' sA) (h6 : HEq sB' sB) (h7 : HEq om' om)
    (h8 : HEq fA' fA) (h9 : HEq fB' fB) (h10 : HEq uA' uA) (h11 : HEq uB' uB) (h12 : HEq vac' vac) (h13 : c0' = c0)
    (h14 : δ' = δ) (h15 : HEq r' r) (h16 : HEq x' x) (h17 : HEq y' y)
    (H : KerTop σ c j A B ψ θ sA sB om fA fB uA uB vac c0 δ r x y) :
    KerTop σ c j A' B' ψ' θ' sA' sB' om' fA' fB' uA' uB' vac' c0' δ' r' x' y' := by
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9; cases h10; cases h11; cases h12
  cases h13; cases h14; cases h15; cases h16; cases h17
  exact (by with_unfolding_all exact (H :))

theorem kerRow_congr (hp : X'.B.toPre = X.B.toPre) {K : Type} [Field K] (σ : K →+* ℂ) (c : ℝ) (j : ℕ) {A B : HSp X.toD7}
    {A' B' : HSp X'.toD7} {ψ ψ' θ θ' sA sA' sB sB' om om' fA fA' fB fB' uA uA' uB uB' vac vac' c0 c0' δ δ' r r' x x' y y'}
    (h1 : HEq A' A) (h2 : HEq B' B) (h3 : HEq ψ' ψ) (h4 : HEq θ' θ) (h5 : HEq sA' sA) (h6 : HEq sB' sB) (h7 : HEq om' om)
    (h8 : HEq fA' fA) (h9 : HEq fB' fB) (h10 : HEq uA' uA) (h11 : HEq uB' uB) (h12 : HEq vac' vac) (h13 : c0' = c0)
    (h14 : δ' = δ) (h15 : HEq r' r) (h16 : HEq x' x) (h17 : HEq y' y)
    (H : KerRow σ c j A B ψ θ sA sB om fA fB uA uB vac c0 δ r x y) :
    KerRow σ c j A' B' ψ' θ' sA' sB' om' fA' fB' uA' uB' vac' c0' δ' r' x' y' := by
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9; cases h10; cases h11; cases h12
  cases h13; cases h14; cases h15; cases h16; cases h17
  exact (by with_unfolding_all exact (H :))

theorem jets_congr (hp : X'.B.toPre = X.B.toPre) {E : Env X.toD7} {E' : Env X'.toD7} {a : E.KT} {a' : E'.KT} {b : E.KR} {b' : E'.KR}
    (h1 : HEq E'.P E.P) (h2 : HEq E'.ov E.ov) (h3 : HEq E'.Vt E.Vt) (h4 : HEq E'.Vr E.Vr) (h5 : HEq E'.Λt E.Λt)
    (h6 : HEq E'.Λr E.Λr) (h7 : HEq E'.βt E.βt) (h8 : HEq E'.βr E.βr) (h9 : HEq E'.dat E.dat) (h10 : HEq E'.pr E.pr)
    (h11 : HEq E'.J E.J) (h12 : HEq E'.modulus E.modulus) (h13 : HEq E'.emb E.emb)
    (ha : ∀ j, j < X'.toD7.R.m → ∀ r r' x x' y y', HEq r' r → HEq x' x → HEq y' y → a j r x y → a' j r' x' y')
    (hb : ∀ j, j < X'.toD7.R.m → ∀ r r' x x' y y', HEq r' r → HEq x' x → HEq y' y → b j r x y → b' j r' x' y')
    (H : E.Jets a b) : E'.Jets a' b' := by
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  cases E
  cases E'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9; cases h10; cases h11; cases h12
  cases h13
  refine Env.Jets.mono (a := (by with_unfolding_all exact (a :))) (b := (by with_unfolding_all exact (b :))) (by kexactB H) (fun j hj r x y => ?_) fun j hj r x y => ?_
  · exact (by with_unfolding_all exact (ha j hj r r x x y y HEq.rfl HEq.rfl HEq.rfl :))
  · exact (by with_unfolding_all exact (hb j hj r r x x y y HEq.rfl HEq.rfl HEq.rfl :))

variable {T T' : Type} {L : LevCh X.toD7 T} {L' : LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}
  {G' : GridData L' sc} {W : G.Weil} {W' : G'.Weil}

theorem places_congr (hp : X'.B.toPre = X.B.toPre) (hg : GAgree G G') {t t'} (hQ : HEq (L'.Q t') (L.Q t)) :
    HEq (locPl G' t') (locPl G t) ∧ HEq (overPl G'.pl.S0 (L'.Q t')) (overPl G.pl.S0 (L.Q t)) ∧ HEq G'.modul G.modul ∧
      ∀ w w', HEq w' w → cosExp G' w' = cosExp G w ∧ keepAt G' w' = keepAt G w := by
  have h1 := hg.v0
  have h2 := hg.w
  clear hg
  unfold locPl
  generalize L.Q t = Q at hQ
  generalize L'.Q t' = Q' at hQ
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  obtain ⟨⟨v, _, u, _⟩, _⟩ := G
  obtain ⟨⟨v', _, u', _⟩, _⟩ := G'
  dsimp only at h1 h2
  cases h1; cases h2; cases hQ
  refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, fun w w' h => ?_⟩
  cases h
  exact ⟨rfl, rfl⟩

theorem psiAt_congr (hp : X'.B.toPre = X.B.toPre) (h : HEq W'.ψ W.ψ) {w w'} (hw : HEq w' w) : HEq (psiAt W' w') (psiAt W w) := by
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  cases W
  cases W'
  dsimp only at h
  cases h; cases hw
  exact HEq.rfl

theorem finEmb_congr (hp : X'.B.toPre = X.B.toPre) {A B : HSp X.toD7} {A' B' : HSp X'.toD7} {c ε ε'} {d : HermitianOrthogonalExtensionData A B c ε}
    {d' : HermitianOrthogonalExtensionData A' B' c ε'} (h1 : HEq A' A) (h2 : HEq B' B) (h : HEq d'.ι d.ι) : HEq (finEmb d') (finEmb d) := by
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  cases h1; cases h2
  cases d
  cases d'
  dsimp only at h
  cases h
  exact HEq.rfl

set_option maxHeartbeats 1000000 in

theorem term_congr (hp : X'.B.toPre = X.B.toPre) {w : Pl X.toD7.host.E} {w' : Pl X'.toD7.host.E} (hw : HEq w' w)
    {Γ : Grid (Kw w)} {Γ' : Grid (Kw w')} (hs : 1 ≤ Γ.s) (hs' : 1 ≤ Γ'.s) {J J' ψ ψ' k k' e e' f f'} (h1 : HEq Γ' Γ) (h2 : HEq J' J)
    (h3 : HEq ψ' ψ) (h4 : k' = k) (h5 : e' = e) (h6 : HEq f' f) : Cosets hs' J' = Cosets hs J ∧ ∀ b b', HEq b' b →
      let u := unfTerm ψ (unitVol w) k (Reps.through hs J (stair Γ (unifAt w) e)) f b
      let u' := unfTerm ψ' (unitVol w') k' (Reps.through hs' J' (stair Γ' (unifAt w') e')) f' b'
      HEq u'.datum u.datum ∧ HEq u'.pr u.pr ∧ (u'.datum ≠ 0 → u.datum ≠ 0) := by
  obtain ⟨⟨P, _⟩, _⟩ := X
  obtain ⟨⟨P', _⟩, _⟩ := X'
  cases hp
  cases hw; cases h1; cases h2; cases h3; cases h4; cases h5; cases h6
  refine ⟨(by with_unfolding_all exact (Eq.refl (Cosets hs J) :)), fun b b' h => ?_⟩
  cases h
  exact (by with_unfolding_all exact ((⟨HEq.rfl, HEq.rfl, id⟩ : let u := unfTerm ψ (unitVol w) k (Reps.through hs J (stair Γ (unifAt w) e)) f b
    HEq u.datum u.datum ∧ HEq u.pr u.pr ∧ (u.datum ≠ 0 → u.datum ≠ 0)) :))

theorem sub_congr (hp : X'.B.toPre = X.B.toPre) {P : Finset (Pl X.toD7.host.E)} {P' : Finset (Pl X'.toD7.host.E)} (h : HEq P' P) :
    (P' : Type) = P ∧ (∀ (w : P) (w' : P'), HEq w' w → HEq w'.1 w.1) := by
  obtain ⟨⟨_, _⟩, _⟩ := X
  obtain ⟨⟨_, _⟩, _⟩ := X'
  cases hp
  cases h
  refine ⟨rfl, fun w w' h => ?_⟩
  cases h
  exact HEq.rfl

theorem corner_congr {μ₀ μ₀' ι} (h : LAgree L L' μ₀ μ₀' ι) :
    HEq (columnBlock L' X'.toD7.R.m).sp (columnBlock L X.toD7.R.m).sp ∧ HEq (columnBlock L' X'.toD7.R.m).lat (columnBlock L X.toD7.R.m).lat ∧
      HEq (colFrame L' X'.toD7.R.m) (colFrame L X.toD7.R.m) := by
  have key : ∀ {D : D7} {U : Type} (M : LevCh D U) (μ), M.Is μ → (M.ΛX : Set _) = L0c D D.sp.X' := fun M μ hM => by
    obtain ⟨c, -, -, -, h1, h2⟩ := hM.βX
    exact Set.ext fun x => ⟨fun hx => by simpa using h2 x hx, fun hx => by simpa using h1 x hx⟩
  have a1 := key L _ h.is
  have a2 := key L' _ h.is'
  have b1 := colFrame_m L
  have b2 := colFrame_m L'
  rw [h.β.1] at b1
  rw [h.β.2] at b2
  have hp := h.pre
  have c : HEq X'.toD7.sp.X' X.toD7.sp.X' ∧ HEq L'.ΛX L.ΛX ∧ HEq (1 : GL (Fin X'.toD7.sp.X'.rank) (Lev.EAf X'.toD7))
      (1 : GL (Fin X.toD7.sp.X'.rank) (Lev.EAf X.toD7)) := by
    generalize L.ΛX = A at a1
    generalize L'.ΛX = A' at a2
    clear b1 b2 h key
    obtain ⟨⟨_, _⟩, _⟩ := X
    obtain ⟨⟨_, _⟩, _⟩ := X'
    cases hp
    exact ⟨HEq.rfl, heq_of_eq (SetLike.coe_injective (a2.trans a1.symm)), HEq.rfl⟩
  refine ⟨?_, ?_, b2.trans (c.2.2.trans b1.symm)⟩
  · rw [colY_m, colY_m]; exact c.1
  · rw [colY_m, colY_m]; exact c.2.1

theorem fam_congr {S : GridChoice W Set.univ} {S' : GridChoice W' Set.univ} {μ₀ μ₀' ι} (hA : Agree S S' μ₀ μ₀' ι) {Φ Φ'}
    (hF : FlipAgree S S' ι Φ Φ') (t : T') (β' : CosFam G' t) : ∃ β : CosFam G (ι t), ∀ (w : locPl G (ι t)) (w' : locPl G' t), HEq w' w →
      HEq (S'.term t Φ' β' w').datum (S.term (ι t) Φ β w).datum ∧ HEq (S'.term t Φ' β' w').pr (S.term (ι t) Φ β w).pr ∧
        ((S'.term t Φ' β' w').datum ≠ 0 → (S.term (ι t) Φ β w).datum ≠ 0) := by
  have hp := hA.l.pre
  obtain ⟨h1, -, -, h4⟩ := places_congr hp hA.g (hA.l.Q t)
  obtain ⟨e, he⟩ := sub_congr hp h1
  have key := fun (w : locPl G (ι t)) (w' : locPl G' t) (h : HEq w' w) =>
    term_congr hp (he w w' h) one_le_sLen one_le_sLen (hF t _ _ (he w w' h) w'.2).1 (hF t _ _ (he w w' h) w'.2).2.1
      (psiAt_congr hp hA.w.ψ (he w w' h)) (h4 _ _ (he w w' h)).2 (h4 _ _ (he w w' h)).1 (hF t _ _ (he w w' h) w'.2).2.2
  refine ⟨fun w => cast (key w (cast e.symm w) (cast_heq _ _)).1 (β' (cast e.symm w)), fun w w' h => ?_⟩
  obtain rfl : w' = cast e.symm w := eq_of_heq (h.trans (cast_heq _ _).symm)
  exact (key w _ h).2 _ _ (cast_heq _ _).symm

theorem trJet_of_trFlip : TrFlip → TrJet := by
  intro hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hJ t Φ' β' hβ'
  obtain ⟨Φ, hΦ⟩ := hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA Φ'
  have hp := hA.l.pre
  have hm : X'.toD7.R.m = X.toD7.R.m := congrArg (·.R.m) hp
  obtain ⟨β, hβ⟩ := fam_congr hA hΦ t β'
  obtain ⟨h1, h2, h3, -⟩ := places_congr hp hA.g (hA.l.Q t)
  obtain ⟨e, he⟩ := sub_congr hp h1
  have hs : β ∈ S.supp (ι t) Φ := fun w => (hβ w (cast e.symm w) (cast_heq _ _)).2.2 (hβ' _)
  have row : ∀ i, HEq (G'.V (.grid i X'.toD7.R.m)) (G.V (.grid i X.toD7.R.m)) ∧
      HEq (G'.Λ (.grid i X'.toD7.R.m)) (G.Λ (.grid i X.toD7.R.m)) ∧ HEq (S'.B.β i X'.toD7.R.m) (S.B.β i X.toD7.R.m) := by
    rintro (_ | i)
    · exact corner_congr hA.l
    · rw [← hm]
      exact ⟨(hA.g.grid i _).1, (hA.g.grid i _).2, hA.s.β i _⟩
  have top : HEq (G'.V (.top X'.toD7.R.m)) (G.V (.top X.toD7.R.m)) := by
    rw [← hm]; exact (hA.g.top _).1
  have fam : ∀ {A B : ℕ → Sort _} {a : ∀ i, A i} {b : ∀ i, B i}, (∀ i, HEq (a i) (b i)) → HEq a b := fun h =>
    Function.hfunext rfl fun i j hij => by cases hij; exact h i
  refine (jetsIn_iff σ S' t Φ' β').2 (jets_congr hp (E := envOf S (ι t) Φ β) h1 h2 (Function.hfunext rfl fun i j hij => ?_)
    (Function.hfunext rfl fun i j hij => ?_) (fam fun j => (hA.g.top j).2) (fam fun i => (row i).2.1) (fam hA.s.βp)
    (fam fun i => (row i).2.2) (Function.hfunext e fun w' w h => (hβ w w' h).1) (Function.hfunext e fun w' w h => (hβ w w' h).2.1)
    (Function.hfunext e fun w' w h => (hΦ t _ _ (he w w' h) w'.2).2.1) h3 (finEmb_congr hp (row _ |>.1.trans ?_) top hA.g.topDec.1)
    (fun j hj r r' x x' y y' a b c => ?_) (fun i hi r r' x x' y y' a b c => ?_) ((jetsIn_iff σ S (ι t) Φ β).1 (hJ _ Φ β hs)))
  · cases hij; exact (hA.g.top i).1
  · cases hij; exact (row i).1
  · rw [hm]; exact HEq.rfl
  · have n1 : DefNode X'.toD7.R.m (.top j) := hj.le
    have n2 : DefNode X'.toD7.R.m (.top (j + 1)) := hj
    have n3 : DefPair X'.toD7.R.m (.top t j) := hj
    exact kerTop_congr hp σ _ j (hA.g.top _).1 (hA.g.top _).1 hA.w.ψ hA.w.θ (hA.w.cart _ n1) (hA.w.cart _ n2) (hA.w.om _ n3)
      (hA.s.fr _ n1).1 (hA.s.fr _ n2).1 (hA.s.fr _ n1).2 (hA.s.fr _ n2).2 (hA.s.vac _ n3).1 (hA.s.vac _ n3).2 hA.s.δ a b c
  · have n : ∀ k, k ≤ X'.toD7.R.m → HEq (W'.cart (.grid k X'.toD7.R.m)) (W.cart (.grid k X.toD7.R.m)) ∧
        HEq (S'.N.fr (.grid k X'.toD7.R.m)) (S.N.fr (.grid k X.toD7.R.m)) ∧
        HEq (S'.N.u (.grid k X'.toD7.R.m)).1 (S.N.u (.grid k X.toD7.R.m)).1 := fun k hk => by
      rw [← hm]
      exact ⟨hA.w.cart _ ⟨hk, rfl⟩, hA.s.fr _ ⟨hk, rfl⟩⟩
    have n3 : HEq (W'.om (.chi i X'.toD7.R.m)) (W.om (.chi i X.toD7.R.m)) ∧
        HEq (S'.Z.vac (.chi i X'.toD7.R.m)) (S.Z.vac (.chi i X.toD7.R.m)) ∧
        S'.Z.c0 (.chi i X'.toD7.R.m) = S.Z.c0 (.chi i X.toD7.R.m) := by
      rw [← hm]
      exact ⟨hA.w.om (.chi i _) ⟨hi, rfl⟩, hA.s.vac (.chi i _) ⟨hi, rfl⟩⟩
    exact kerRow_congr hp σ _ i (row _).1 (row _).1 hA.w.ψ hA.w.θ (n _ hi.le).1 (n _ hi).1 n3.1
      (n _ hi.le).2.1 (n _ hi).2.1 (n _ hi.le).2.2 (n _ hi).2.2 n3.2.1 n3.2.2 hA.s.δ a b c

end Two

end GlobalTheory.RowEx.Jet

end
