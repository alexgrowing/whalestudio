import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def flipOrder (m : ℕ) : List (ℕ × ℕ) := (List.range m).flatMap fun i => (List.range m).map fun j => (i, j)

def midEdge (m i j p : ℕ) : Edge :=
  if p < i then .ex p m else if p + j < i + m then .theta i (m + i - 1 - p) else if p + j = i + m then .ex i j
  else if p ≤ i + m then .theta (i + 1) (m + i - p) else .ex (p - m) 0

theorem infix_map_range {α : Type*} (f : ℕ → α) {p n : ℕ} (h : p + 2 ≤ n) : [f p, f (p + 1)] <:+: (List.range n).map f := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(List.range p).map f, ((List.range c).map fun x => p + 2 + x).map f, by
    simp [List.range_add, List.range_succ]⟩

theorem canFlip_append {γ : List Edge} {l l' : List (ℕ × ℕ)} (h : CanFlip γ l)
    (h' : CanFlip (l.foldl (fun γ x => flipPath x.1 x.2 γ) γ) l') : CanFlip γ (l ++ l') := by
  induction h with
  | nil => exact h'
  | cons hp _ ih => exact .cons hp (ih h')

theorem canFlip_col {m i : ℕ} (hi : i < m) : ∀ j, j ≤ m →
    CanFlip ((List.range (m + m)).map (midEdge m i 0)) ((List.range j).map fun j => (i, j)) ∧
    ((List.range j).map fun j => (i, j)).foldl (fun γ x => flipPath x.1 x.2 γ) ((List.range (m + m)).map (midEdge m i 0)) =
      (List.range (m + m)).map (midEdge m i j)
  | 0, _ => ⟨.nil _, rfl⟩
  | j + 1, hj => by
    obtain ⟨h1, h2⟩ := canFlip_col hi j (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append, h2]
    refine ⟨canFlip_append h1 (h2 ▸ .cons ?_ (.nil _)), ?_⟩
    · have := infix_map_range (midEdge m i j) (p := i + m - j - 1) (n := m + m) (by omega)
      have e1 : midEdge m i j (i + m - j - 1) = .theta i j := by
        rw [midEdge, if_neg (by omega), if_pos (by omega)]; congr 1; omega
      have e2 : midEdge m i j (i + m - j - 1 + 1) = .ex i j := by
        rw [midEdge, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rwa [e1, e2] at this
    · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, flipPath, List.map_map]
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp, midEdge]
      split_ifs <;> simp_all <;> omega

theorem canFlip_cols {m : ℕ} : ∀ i, i ≤ m →
    CanFlip ((List.range (m + m)).map (midEdge m 0 0)) ((List.range i).flatMap fun i => (List.range m).map fun j => (i, j)) ∧
    ((List.range i).flatMap fun i => (List.range m).map fun j => (i, j)).foldl (fun γ x => flipPath x.1 x.2 γ)
      ((List.range (m + m)).map (midEdge m 0 0)) = (List.range (m + m)).map (midEdge m i 0)
  | 0, _ => ⟨.nil _, rfl⟩
  | i + 1, hi => by
    obtain ⟨h1, h2⟩ := canFlip_cols i (by omega : i ≤ m)
    obtain ⟨h3, h4⟩ := canFlip_col (by omega : i < m) m le_rfl
    rw [List.range_succ, List.flatMap_append, List.foldl_append, h2, List.flatMap_singleton, h4]
    refine ⟨canFlip_append h1 (h2 ▸ h3), List.map_congr_left fun p _ => ?_⟩
    simp only [midEdge]
    split_ifs <;> first | omega | rfl | (congr 1; omega)

theorem canFlip_flipOrder (m : ℕ) : CanFlip (givenPath m) (flipOrder m) ∧ (flipOrder m).length = m ^ 2 ∧
    (flipOrder m).foldl (fun γ x => flipPath x.1 x.2 γ) (givenPath m) = oppositePath m := by
  have rev : (List.range m).reverse = (List.range m).map fun p => m - 1 - p := by
    simp [List.range_eq_range', List.reverse_range']
  have e1 : givenPath m = (List.range (m + m)).map (midEdge m 0 0) := by
    rw [givenPath, rev, List.range_add, List.map_append, List.map_map, List.map_map]
    congr 1 <;> refine List.map_congr_left fun p hp => ?_ <;> have := List.mem_range.1 hp <;>
      simp only [Function.comp, midEdge] <;> split_ifs <;> first | omega | rfl | (congr 1; omega)
  have e2 : oppositePath m = (List.range (m + m)).map (midEdge m m 0) := by
    rw [oppositePath, rev, List.range_add, List.map_append, List.map_map, List.map_map]
    congr 1 <;> refine List.map_congr_left fun p hp => ?_ <;> have := List.mem_range.1 hp <;>
      simp only [Function.comp, midEdge] <;> split_ifs <;> first | omega | rfl | (congr 1; omega)
  rw [e1, e2]
  exact ⟨(canFlip_cols m le_rfl).1, by simp [flipOrder, List.length_flatMap, sq], (canFlip_cols m le_rfl).2⟩

example : flipOrder 2 = [(0, 0), (0, 1), (1, 0), (1, 1)] := rfl

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

abbrev Kw (w : Pl D.host.E) : Type := w.adicCompletion D.host.E

@[reducible] def borelKw (w : Pl D.host.E) : MeasurableSpace (Kw w) := borel _

attribute [local instance] borelKw

theorem borelSpaceKw (w : Pl D.host.E) : BorelSpace (Kw w) := ⟨rfl⟩

attribute [local instance] borelSpaceKw

def unifAt (w : Pl D.host.E) : (Kw w)ˣ := atFin w (unif w)

theorem isUnif_unifAt (w : Pl D.host.E) : IsUnif (unifAt w) := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  refine le_antisymm (le_uniformizer_iff.2 (e.lt_one_iff_lt_one.2 (by rw [h, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))) ?_
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer (Kw w))
  have h1 : Valued.v y < 1 := e.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
  rw [← hy, e y, h]
  rw [← WithZero.exp_zero] at h1
  exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)

open Classical in

def locPl (G : GridData L sc) (t : T) : Finset (Pl D.host.E) := G.pl.W0 ∪ L.Q t

open Classical in

def cosExp (G : GridData L sc) (w : Pl D.host.E) : ℕ := if w ∈ G.pl.W0 then G.pl.depth sc (w.under (𝓞 D.host.F)) else 0

def depthAt (G : GridData L sc) (w : Pl D.host.E) : ℕ := max (cosExp G w) 1

theorem depthAt_w (G : GridData L sc) {v : Pl D.host.F} (hv : v ∈ G.pl.S0) :
    cosExp G (G.pl.w v) = G.pl.depth sc v ∧ depthAt G (G.pl.w v) = G.pl.depth sc v := by
  classical
  have h : cosExp G (G.pl.w v) = G.pl.depth sc v := by
    rw [cosExp, if_pos (by unfold Places.W0; convert Finset.mem_image_of_mem _ hv), G.pl.under_w hv]
  exact ⟨h, by rw [depthAt, h, max_eq_left (G.pl.depth_pos sc v)]⟩

theorem depthAt_of_notMem (G : GridData L sc) {w : Pl D.host.E} (hw : w ∉ G.pl.W0) : cosExp G w = 0 ∧ depthAt G w = 1 := by
  simp [depthAt, cosExp, hw]

variable (L) in

def muBase : ℕ → HChar D.host.E
  | 0 => 1
  | j + 1 => if h : j < D.R.m then L.C.mu0 ⟨j, h⟩ else 1

def locGrid (G : GridData L sc) (t : T) (w : Pl D.host.E) : Grid (Kw w) where
  m := D.R.m
  r := D.R.r
  t := D.R.t
  s := sLen D
  mu j := (muBase L j * L.xiH t).loc w
  chi i := (G.ch.chiH i).loc w
  eta := L.C.eta.loc w

theorem rank_vertex (G : GridData L sc) (t : T) (w : Pl D.host.E) {X : ℕ × ℕ} (h : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) :
    (locGrid G t w).rank X = (G.V (.grid X.1 X.2)).rank := by
  obtain ⟨_ | i, k⟩ := X
  · change D.R.r + k * D.R.t + 0 * sLen D = (columnBlock L k).sp.rank
    rw [zero_mul, add_zero]
    rcases (show k ≤ D.R.m from h.2).eq_or_lt with rfl | hk
    · rw [colY_m]; exact D.sp.X'_rank.symm
    · rw [colY_lt L hk]
      exact ((D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)).symm
  · exact (G.sp.V_is (i + 1) k (by omega) h.1 h.2).rank.symm

theorem isTame_loc {χ : HChar D.host.E} {w : Pl D.host.E} (h : χ.TameAt w) : IsTame (χ.loc w) := by
  intro x hx
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have h1 : Valued.v ((x : Kw w) - 1) < 1 :=
    (ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.1 hx
  refine h x ?_ ?_
  · have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  · rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)

theorem isTame_muBase (w : Pl D.host.E) (j : ℕ) : IsTame ((muBase L j).loc w)⁻¹ := fun x hx => by
  have : (muBase L j).TameAt w := by
    rcases j with _ | j
    · exact fun _ _ _ => rfl
    · rw [muBase]
      split_ifs with h
      · exact (L.C.isMu0 ⟨j, h⟩).tame w
      · exact fun _ _ _ => rfl
  rw [MonoidHom.inv_apply, isTame_loc this x hx, inv_one]

open Classical in

def atPl (w : Pl D.host.E) (x : Kw w) : AE D := ((comp_toAd D).surj (RestrictedProduct.single _ w x)).choose

open Classical in

theorem atPl_spec (w : Pl D.host.E) (x : Kw w) :
    infPart D (atPl w x) = 0 ∧ ∀ Q, cpt (D := D) Q (toEAf D (atPl w x)) = (Pi.single w x : ∀ Q, Kw Q) Q :=
  have h := ((comp_toAd D).surj (RestrictedProduct.single _ w x)).choose_spec
  ⟨h.1, fun Q => congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) h.2⟩

theorem ae_ext {z z' : AE D} (h : infPart D z = infPart D z') (h' : ∀ Q, cpt (D := D) Q (toEAf D z) = cpt (D := D) Q (toEAf D z')) : z = z' :=
  sub_eq_zero.1 ((comp_toAd D).ext _ (by rw [RingHom.map_sub, h, sub_self])
    (by rw [RingHom.comp_apply, RingHom.map_sub, cpt_ext h', sub_self, RingHom.map_zero]))

theorem atPl_add (w : Pl D.host.E) (x y : Kw w) : atPl w (x + y) = atPl w x + atPl w y := by
  classical
  refine ae_ext (by rw [RingHom.map_add, (atPl_spec w _).1, (atPl_spec w _).1, (atPl_spec w _).1, add_zero]) fun Q => ?_
  rw [RingHom.map_add, RingHom.map_add, (atPl_spec w _).2, (atPl_spec w _).2, (atPl_spec w _).2, Pi.single_add, Pi.add_apply]

def psiAt {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E) : AddChar (Kw w) Circle where
  toFun x := ⟨W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w x)),
    mem_sphere_zero_iff_norm.2 (W.ψ_std.1.2.1 _)⟩
  map_zero_eq_one' := Circle.ext (by
    have : atPl w 0 = 0 := by simpa using atPl_add w 0 0
    simp [this])
  map_add_eq_mul' x y := Circle.ext (by
    change W.ψ _ = W.ψ _ * W.ψ _
    rw [atPl_add, mul_add, map_add, AddChar.map_add_eq_mul])

def colFrame (L : LevCh D T) : ∀ j, GL (Fin (columnBlock L j).sp.rank) (Formalism.IndefR.Lev.EAf D)
  | 0 => L.βY 0
  | j + 1 => if h : j + 1 < D.R.m then cast (by rw [colY_lt L h]) (L.βY (j + 1))
      else cast (by rw [show columnBlock L (j + 1) = ⟨D.sp.X', L.ΛX⟩ from if_neg h]) L.βX

theorem colFrame_lt (L : LevCh D T) {j : ℕ} (h : j < D.R.m) : HEq (colFrame L j) (L.βY j) := by
  cases j with
  | zero => rfl
  | succ j => rw [colFrame, dif_pos h]; exact cast_heq _ _

theorem colFrame_m (L : LevCh D T) : HEq (colFrame L D.R.m) L.βX := by
  obtain ⟨j, hj⟩ : ∃ j, D.R.m = j + 1 := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩
  have : HEq (colFrame L (j + 1)) L.βX := by rw [colFrame, dif_neg (by omega)]; exact cast_heq _ _
  rwa [← hj] at this

structure Frames (G : GridData L sc) where

  βs : ∀ i j, GL (Fin (G.sp.Vs i j).sp.rank) (Formalism.IndefR.Lev.EAf D)

  isFrame : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → IsFrame (βs i j) (G.sp.Vs i j).lat

instance (G : GridData L sc) : Nonempty (Frames G) := by
  have h : ∀ i j, ∃ β : GL (Fin (G.sp.Vs i j).sp.rank) (Formalism.IndefR.Lev.EAf D),
      1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → IsFrame β (G.sp.Vs i j).lat := fun i j => by
    by_cases h : 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
    · have hl := (G.sp.V_is i j h.1 h.2.1 h.2.2).sd.1
      obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ hl.fg hl.span_eq_top
      exact ⟨β, fun _ _ _ => hβ⟩
    · exact ⟨1, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose β hβ using h
  exact ⟨⟨β, hβ⟩⟩

namespace Frames

variable {G : GridData L sc} (B : Frames G)

def β : ∀ i j, GL (Fin (G.V (.grid i j)).rank) (Formalism.IndefR.Lev.EAf D)
  | 0, j => colFrame L j
  | i + 1, j => B.βs (i + 1) j

theorem isFrame_β {μ₀ : T} (hL : L.Is μ₀) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) :
    IsFrame (B.β i j) (G.Λ (.grid i j)) := by
  rcases i with _ | i
  · have key : ∀ (X Y : LSp D) (a : GL (Fin X.sp.rank) (Formalism.IndefR.Lev.EAf D)) (b : GL (Fin Y.sp.rank) (Formalism.IndefR.Lev.EAf D)),
        X = Y → HEq a b → IsFrame b Y.lat → IsFrame a X.lat := by
      rintro X _ a b rfl h h'
      rwa [eq_of_heq h]
    rcases hj.eq_or_lt with rfl | hj
    · exact key _ _ _ _ (colY_m L) (colFrame_m L) hL.βX.choose_spec.1
    · exact key _ _ _ _ (colY_lt L hj) (colFrame_lt L hj) (hL.βY j hj).choose_spec.1
  · exact B.isFrame (i + 1) j (by omega) hi hj

def coord (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (y : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w) :=
  ((((loc w (B.β X.1 X.2))⁻¹).val * y * (loc w (B.β Y.1 Y.2)).val).submatrix
    (Fin.cast (rank_vertex G t w hX)) (Fin.cast (rank_vertex G t w hY)))ᵀ

end Frames

variable (G : GridData L sc) (t : T) (w : Pl D.host.E)

def ixFin (j : ℕ) : Ix (Fin D.R.r) (Fin D.R.t) j ≃ Fin ((locGrid G t w).rank (0, j)) :=
  (((Equiv.refl _).sumCongr finProdFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by change _ = D.R.r + j * D.R.t + 0 * sLen D; rw [zero_mul, add_zero]))

theorem ixFin_val (j : ℕ) : (∀ a, (ixFin G t w j (.inl a)).val = a.val) ∧
    ∀ c b, (ixFin G t w j (.inr (c, b))).val = D.R.r + (b.val + D.R.t * c.val) := ⟨fun _ => rfl, fun _ _ => rfl⟩

variable (L) in
open Classical in

def stepGroup (j : ℕ) : Subgroup (GL (Ix (Fin D.R.r) (Fin D.R.t) j) (Kw w)) :=
  if w ∈ L.Pg then
    ((TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j).J
  else if w ∈ L.Q t then (parahoric (k := Kw w) (Fin D.R.r) (Fin j × Fin D.R.t) 1 fun _ _ => rfl).J else KO (Kw w) _

variable (L) in
open Classical in

def stepFn (j : ℕ) : Matrix (Ix (Fin D.R.r) (Fin D.R.t) (j + 1)) (Ix (Fin D.R.r) (Fin D.R.t) j) (Kw w) → ℂ :=
  if w ∈ L.Pg then
    (TypeDatum.principal (Kw w) (Fin D.R.r)).iterPhi (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j
  else if w ∈ L.Q t then parPhi ((L.xiH t).loc w)⁻¹ else Set.indicator {x | IntM x} 1

variable {G} (B : Frames G)

def cosetSet {i : ℕ} (hi : i < D.R.m) (κ : G.CosAt i) :
    Set (Matrix (Fin ((locGrid G t w).rank (i + 1, 0))) (Fin ((locGrid G t w).rank (i, 0))) (Kw w)) :=
  {x | ∃ y : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)), Cos.mk G.modul y = κ ∧
    x - B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩
      (y.1.map (algebraMap D.host.E (Kw w))) ∈ matLat _ (unifAt w ^ cosExp G w • stdLat (Kw w) _)}

def givenDatum (Φ : G.Datum) : ∀ b : Edge,
    Matrix (Fin ((locGrid G t w).rank b.tgt)) (Fin ((locGrid G t w).rank b.src)) (Kw w) → ℂ
  | .theta 0 j => fun x => stepFn L t w j (xᵀ.submatrix (ixFin G t w (j + 1)) (ixFin G t w j))
  | .ex i 0 => if hi : i < D.R.m then (cosetSet t w B hi (Φ ⟨i, hi⟩)).indicator 1 else 0
  | _ => 0

variable (G) in

def givenLevel : (locGrid G t w).Level
  | (_, 0) => glLatCong (unifAt w ^ cosExp G w) (stdLat (Kw w) _)
  | (0, j + 1) => (stepGroup L t w (j + 1)).map (reGL (ixFin G t w (j + 1))).toMonoidHom
  | (_ + 1, _ + 1) => KO (Kw w) _

def givenStage (Φ : G.Datum) : (locGrid G t w).PiLocalization₂ :=
  ⟨givenPath D.R.m, givenLevel G t w, (locGrid G t w).lines₂ (givenPath D.R.m) (givenDatum t w B Φ)⟩

def flipStage (W : G.Weil) (Φ : G.Datum) : (locGrid G t w).PiLocalization₂ :=
  (givenStage t w B Φ).flips .one (psiAt W w) (unifAt w) (depthAt G w) (flipOrder D.R.m)

def Tflip (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E) : (locGrid G t w).Args → ℂ :=
  (flipStage t w B W Φ).tensor

theorem flips_path {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ)
    (l : List (ℕ × ℕ)) (S : Γ.PiLocalization₂) : (S.flips s ψ ϖ e l).path = l.foldl (fun γ x => flipPath x.1 x.2 γ) S.path := by
  induction l generalizing S with
  | nil => rfl
  | cons x l ih => exact ih (S.flip s ψ ϖ e x)

theorem flips_level {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ)
    (l : List (ℕ × ℕ)) (S : Γ.PiLocalization₂) (h : ∀ i j, S.level (i + 1, j + 1) = KO k _) : (S.flips s ψ ϖ e l).level = S.level := by
  induction l generalizing S with
  | nil => rfl
  | cons x l ih =>
    have e1 : (S.flip s ψ ϖ e x).level = S.level := Function.update_eq_self_iff.2 (h _ _).symm
    exact (ih (S.flip s ψ ϖ e x) (e1 ▸ h)).trans e1

theorem flipStage_path_level (W : G.Weil) (Φ : G.Datum) :
    (flipStage t w B W Φ).path = oppositePath D.R.m ∧ (flipStage t w B W Φ).level = givenLevel G t w :=
  ⟨(flips_path _ _ _ _ _ _).trans (canFlip_flipOrder _).2.2, flips_level _ _ _ _ _ _ fun _ _ => rfl⟩

variable (L) in

theorem exists_stepFn_eq_one (j : ℕ) : ∃ x, stepFn L t w j x = 1 := by
  unfold stepFn
  split_ifs
  · refine ⟨(fromRows 1 0).submatrix (ixSucc _ _ j).symm id, ?_⟩
    rw [TypeDatum.iterPhi, submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, submatrix_id_id,
      TypeDatum.Phi_of_mem _ _ 1 (by simp) (by simpa using maxM_zero)]
    simp
  · exact ⟨fromBlocks 1 0 0 0, by rw [parPhi_fromBlocks _ (one_mem _) Units.val_one maxM_zero intM_zero intM_zero]; simp⟩
  · exact ⟨0, Set.indicator_of_mem intM_zero _⟩

theorem exists_givenStage_eq_one (Φ : G.Datum) : ∃ x, (givenStage t w B Φ).tensor x = 1 := by
  have h : ∀ b : Edge, ∃ x, b ∈ givenPath D.R.m → givenDatum t w B Φ b x = 1 := fun b => by
    by_cases hb : b ∈ givenPath D.R.m
    · simp only [givenPath, List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at hb
      rcases hb with ⟨j, -, rfl⟩ | ⟨i, hi, rfl⟩
      · obtain ⟨x, hx⟩ := exists_stepFn_eq_one L t w j
        refine ⟨(x.submatrix (ixFin G t w (j + 1)).symm (ixFin G t w j).symm)ᵀ, fun _ => ?_⟩
        simpa [givenDatum] using hx
      · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Φ ⟨i, hi⟩)
        refine ⟨B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩
          (y.1.map (algebraMap D.host.E (Kw w))), fun _ => ?_⟩
        rw [givenDatum, dif_pos hi]
        refine Set.indicator_of_mem (s := cosetSet t w B hi _) ?_ _
        exact ⟨y, hy, by rw [sub_self]; exact zero_mem _⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose x hx using h
  exact ⟨x, List.prod_eq_one fun c hc => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    exact hx b hb⟩

end GlobalTheory.FunObj

end
