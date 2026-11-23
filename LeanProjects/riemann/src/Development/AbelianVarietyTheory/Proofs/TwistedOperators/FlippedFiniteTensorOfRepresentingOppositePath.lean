import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.OppConv

open GlobalTheory.FlipRun GlobalTheory.RowClaim

variable {D : D7} {T : Type}

section Fam

variable {S : Arrow T → Type} {X Y : Node}

theorem append_inj (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z) (d d' : p.Fam S) (e e' : q.Fam S),
    Path.Fam.append (q := q) d e = Path.Fam.append (q := q) d' e' → d = d' ∧ e = e'
  | _, .nil, _, _, _, _, h => ⟨h, rfl⟩
  | _, .snoc _ q, d, d', e, e', h => by
      have h' : (Path.Fam.append (q := q) d e.1, e.2) = (Path.Fam.append (q := q) d' e'.1, e'.2) := h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h'
      obtain ⟨r1, r2⟩ := append_inj p q d d' e.1 e'.1 h1
      exact ⟨r1, Prod.ext r2 h2⟩

theorem append_surj (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z) (f : (p.comp q).Fam S),
    ∃ d e, Path.Fam.append (q := q) d e = f
  | _, .nil, f => ⟨f, (), rfl⟩
  | _, .snoc a q, f => by
      obtain ⟨d, e, h⟩ := append_surj p q f.1
      refine ⟨d, ((e, f.2) : (Path.snoc a q).Fam S), ?_⟩
      show (Path.Fam.append (q := q) d e, f.2) = f
      rw [h]
      rfl

theorem rowFam_inj (j : ℕ) : ∀ n (f g : ∀ i : Fin n, S (.right i j)), rowFam j n f = rowFam j n g → f = g
  | 0, _, _, _ => funext fun i => i.elim0
  | n + 1, f, g, h => by
      have h' : (rowFam j n (fun i => f i.castSucc), f (Fin.last n)) = (rowFam j n (fun i => g i.castSucc), g (Fin.last n)) := h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h'
      have h3 := rowFam_inj j n _ _ h1
      funext i
      induction i using Fin.lastCases with
      | last => exact h2
      | cast i => exact congrFun h3 i

theorem rowFam_surj (j : ℕ) : ∀ n (d : (rowPath T j n).Fam S), ∃ f, rowFam j n f = d
  | 0, _ => ⟨fun i => i.elim0, rfl⟩
  | n + 1, d => by
      obtain ⟨f, hf⟩ := rowFam_surj j n d.1
      refine ⟨Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f, ?_⟩
      show (rowFam j n (fun i => Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f i.castSucc),
        Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f (Fin.last n)) = d
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl

theorem downFam_inj (t : T) (i : ℕ) : ∀ n (f g : ∀ j : Fin n, S (.down t i j)), downFam t i n f = downFam t i n g → f = g
  | 0, _, _, _ => funext fun j => j.elim0
  | n + 1, f, g, h => by
      obtain ⟨h1, h2⟩ := append_inj (Path.one (.down t i n)) (downPath t i n) _ _ _ _ h
      have h3 := downFam_inj t i n _ _ h2
      have h4 : f (Fin.last n) = g (Fin.last n) := congrArg Prod.snd h1
      funext j
      induction j using Fin.lastCases with
      | last => exact h4
      | cast j => exact congrFun h3 j

theorem downFam_surj (t : T) (i : ℕ) : ∀ n (d : (downPath t i n).Fam S), ∃ f, downFam t i n f = d
  | 0, _ => ⟨fun j => j.elim0, rfl⟩
  | n + 1, d => by
      obtain ⟨d0, e, he⟩ := append_surj (Path.one (.down t i n)) (downPath t i n) d
      obtain ⟨f, hf⟩ := downFam_surj t i n e
      refine ⟨Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f, ?_⟩
      rw [← he]
      show Path.Fam.append (p := Path.one (.down t i n)) ((), Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f (Fin.last n))
        (downFam t i n fun j => Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f j.castSucc) = _
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl

end Fam

section Grid

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {X Y : Node}

theorem edges_snoc (a : Arrow T) (p : Path T X a.src) : edges (Path.snoc a p) = edges p ++ [edgeOf a] := by
  simp only [edges, Path.arrows, List.map_append, List.map_cons, List.map_nil]

theorem edges_comp (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z), edges (p.comp q) = edges p ++ edges q
  | _, .nil => by simp only [edges, Path.arrows, List.map_nil, List.append_nil]; rfl
  | _, .snoc a q => by
      rw [show p.comp (.snoc a q) = .snoc a (p.comp q) from rfl, edges_snoc, edges_snoc, edges_comp p q, List.append_assoc]

theorem mem_edges_row (j : ℕ) : ∀ (n : ℕ) (e : GlobalTheory.SplitFlip.Edge), e ∈ edges (rowPath T j n) ↔ ∃ i < n, e = .ex i j
  | 0, e => by simp [edges, Path.arrows, rowPath]
  | n + 1, e => by
      rw [show rowPath T j (n + 1) = .snoc (.right n j) (rowPath T j n) from rfl, edges_snoc, List.mem_append,
        mem_edges_row j n e, List.mem_singleton]
      constructor
      · rintro (⟨i, hi, rfl⟩ | rfl)
        · exact ⟨i, by omega, rfl⟩
        · exact ⟨n, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · exact Or.inl ⟨i, h, rfl⟩
        · exact Or.inr rfl

theorem mem_edges_down (t : T) (i : ℕ) : ∀ (n : ℕ) (e : GlobalTheory.SplitFlip.Edge), e ∈ edges (downPath t i n) ↔ ∃ j < n, e = .theta i j
  | 0, e => by simp [edges, Path.arrows, downPath]
  | n + 1, e => by
      rw [show downPath t i (n + 1) = (Path.one (.down t i n)).comp (downPath t i n) from rfl, edges_comp, List.mem_append,
        mem_edges_down t i n e, edges_snoc]
      simp only [edges, Path.arrows, List.map_nil, List.nil_append, List.mem_singleton]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨n, by omega, rfl⟩
        · exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
        · exact Or.inr ⟨j, h, rfl⟩
        · exact Or.inl rfl

section Args

variable (B : Frames G) (t : T) (w : Pl D.host.E)

theorem pathArgs_zero : ∀ {Y : Node} (p : Path T X Y) (x : ArgT G p) (e : GlobalTheory.SplitFlip.Edge), e ∉ edges p →
    pathArgs B t w p x e = 0
  | _, .nil, _, _, _ => rfl
  | _, .snoc a p, x, e, he => by
      rw [edges_snoc, List.mem_append, List.mem_singleton, not_or] at he
      show argAt B t w a x.2 e (pathArgs B t w p x.1 e) = 0
      rw [argAt, dif_neg (Ne.symm he.2)]
      exact pathArgs_zero p x.1 e he.1

theorem pathArgs_comp (p : Path T X Y) (x : ArgT G p) (e : GlobalTheory.SplitFlip.Edge) : ∀ {Z : Node} (q : Path T Y Z) (y : ArgT G q),
    (e ∈ edges q → pathArgs B t w (p.comp q) (Path.Fam.append (q := q) x y) e = pathArgs B t w q y e) ∧
    (e ∉ edges q → pathArgs B t w (p.comp q) (Path.Fam.append (q := q) x y) e = pathArgs B t w p x e)
  | _, .nil, _ => ⟨fun h => absurd h (by simp [edges, Path.arrows]), fun _ => rfl⟩
  | _, .snoc a q, y => by
      have ih := pathArgs_comp p x e q y.1
      have hl : pathArgs B t w (p.comp (.snoc a q)) (Path.Fam.append (q := .snoc a q) x y) e =
          argAt B t w a y.2 e (pathArgs B t w (p.comp q) (Path.Fam.append (q := q) x y.1) e) := rfl
      have hr : pathArgs B t w (.snoc a q) y e = argAt B t w a y.2 e (pathArgs B t w q y.1 e) := rfl
      rw [hl, hr, edges_snoc]
      by_cases h : edgeOf a = e
      · refine ⟨fun _ => ?_, fun h' => absurd (List.mem_append_right _ (List.mem_singleton.2 h.symm)) h'⟩
        simp only [argAt, dif_pos h]
      · simp only [argAt, dif_neg h]
        refine ⟨fun h' => ih.1 ?_, fun h' => ih.2 ?_⟩
        · rcases List.mem_append.1 h' with h'' | h''
          · exact h''
          · exact absurd (List.mem_singleton.1 h'').symm h
        · exact fun h'' => h' (List.mem_append_left _ h'')

theorem pathArgs_row (j : ℕ) : ∀ (n : ℕ) (x : ∀ i : Fin n, WO (G.pS (Arrow.right (T := T) i j).pair) (G.pT (Arrow.right (T := T) i j).pair))
    (i : ℕ) (h : i < n), pathArgs B t w (rowPath T j n) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) j n x) (.ex i j) =
      locArg B t w (.right i j) (x ⟨i, h⟩)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, i, h => by
      show argAt B t w (.right n j) (x (Fin.last n)) (.ex i j)
        (pathArgs B t w (rowPath T j n) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) j n fun i => x i.castSucc) (.ex i j)) = _
      by_cases hi : i = n
      · subst hi
        rw [argAt]
        exact dif_pos rfl
      · rw [argAt, dif_neg (by simp only [edgeOf, ne_eq, GlobalTheory.SplitFlip.Edge.ex.injEq, not_and]; intro h'; exact absurd h'.symm hi)]
        exact pathArgs_row j n (fun i => x i.castSucc) i (by omega)

theorem pathArgs_down (i : ℕ) : ∀ (n : ℕ) (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair))
    (j : ℕ) (h : j < n), pathArgs B t w (downPath t i n) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) (.theta i j) =
      locArg B t w (.down t i j) (y ⟨j, h⟩)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, y, j, h => by
      have hc := pathArgs_comp B t w (Path.one (.down t i n)) ((), y (Fin.last n)) (.theta i j) (downPath t i n)
        (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)
      by_cases hj : j < n
      · exact (hc.1 ((mem_edges_down t i n _).2 ⟨j, hj, rfl⟩)).trans (pathArgs_down i n _ j hj)
      · have hj' : j = n := by omega
        subst hj'
        refine (hc.2 fun h' => ?_).trans ?_
        · obtain ⟨k, hk, hk'⟩ := (mem_edges_down t i j _).1 h'
          simp only [GlobalTheory.SplitFlip.Edge.theta.injEq] at hk'
          omega
        · exact dif_pos rfl

end Args

section Prods

theorem famProd_append (p : Path T X Y) (d : PureT G p) (x : ArgT G p) : ∀ {Z : Node} (q : Path T Y Z) (d' : PureT G q)
    (x' : ArgT G q), famProd (p.comp q) (Path.Fam.append (q := q) d d') (Path.Fam.append (q := q) x x') = famProd p d x * famProd q d' x'
  | _, .nil, _, _ => (mul_one _).symm
  | _, .snoc _ q, d', x' => by
      show famProd (p.comp q) (Path.Fam.append (q := q) d d'.1) (Path.Fam.append (q := q) x x'.1) * d'.2 x'.2 =
        famProd p d x * (famProd q d'.1 x'.1 * d'.2 x'.2)
      rw [famProd_append p d x q, mul_assoc]

theorem halfAll_append (e : AE D) (p : Path T X Y) (x : ArgT G p) : ∀ {Z : Node} (q : Path T Y Z) (x' : ArgT G q),
    HalfAll (G := G) e (p.comp q) (Path.Fam.append (q := q) x x') ↔ HalfAll (G := G) e p x ∧ HalfAll (G := G) e q x'
  | _, .nil, _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | _, .snoc _ q, x' => by
      show HalfAll (G := G) e (p.comp q) (Path.Fam.append (q := q) x x'.1) ∧ IsHalf e x'.2 ↔
        HalfAll (G := G) e p x ∧ (HalfAll (G := G) e q x'.1 ∧ IsHalf e x'.2)
      rw [halfAll_append e p x q, and_assoc]

theorem vecAll_append {W : G.Weil} (ρ : RealMatch W) (e : AE D) (p : Path T X Y) (φ d : PureT G p) : ∀ {Z : Node} (q : Path T Y Z)
    (φ' d' : PureT G q), VecAll ρ e (p.comp q) (Path.Fam.append (q := q) φ φ') (Path.Fam.append (q := q) d d') ↔
      VecAll ρ e p φ d ∧ VecAll ρ e q φ' d'
  | _, .nil, _, _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | _, .snoc a q, φ', d' => by
      show VecAll ρ e (p.comp q) (Path.Fam.append (q := q) φ φ'.1) (Path.Fam.append (q := q) d d'.1) ∧
          IsLocVec W a.pair e (vacOf ρ a) φ'.2 d'.2 ↔
        VecAll ρ e p φ d ∧ (VecAll ρ e q φ'.1 d'.1 ∧ IsLocVec W a.pair e (vacOf ρ a) φ'.2 d'.2)
      rw [vecAll_append ρ e p φ d q, and_assoc]

theorem restrictPol_append (P : PolE G) (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = Path.Fam.append (q := q) (restrictPol P p) (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
      show (restrictPol P (p.comp q), polOf P a) = (Path.Fam.append (q := q) (restrictPol P p) (restrictPol P q), polOf P a)
      rw [restrictPol_append P p q]

theorem zip_append {S S' S'' : Arrow T → Type} (f : ∀ a, S a → S' a → S'' a) (p : Path T X Y) (d : p.Fam S) (d' : p.Fam S') :
    ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S) (e' : q.Fam S'),
      Path.Fam.zip f (Path.Fam.append (q := q) d e) (Path.Fam.append (q := q) d' e') =
        Path.Fam.append (q := q) (Path.Fam.zip f d d') (Path.Fam.zip f e e')
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, e' => by
      show (Path.Fam.zip f (Path.Fam.append (q := q) d e.1) (Path.Fam.append (q := q) d' e'.1), f a e.2 e'.2) =
        (Path.Fam.append (q := q) (Path.Fam.zip f d d') (Path.Fam.zip f e.1 e'.1), f a e.2 e'.2)
      rw [zip_append f p d d' q]

theorem zip_row {S S' S'' : Arrow T → Type} (f : ∀ a, S a → S' a → S'' a) (j : ℕ) : ∀ (n : ℕ) (d : ∀ i : Fin n, S (.right i j))
    (d' : ∀ i : Fin n, S' (.right i j)), Path.Fam.zip f (rowFam j n d) (rowFam j n d') = rowFam j n fun i => f _ (d i) (d' i)
  | 0, _, _ => rfl
  | n + 1, d, d' => by
      show (Path.Fam.zip f (rowFam j n fun i => d i.castSucc) (rowFam j n fun i => d' i.castSucc), f _ (d (Fin.last n)) (d' (Fin.last n))) = _
      rw [zip_row f j n]
      rfl

theorem zip_down {S S' S'' : Arrow T → Type} (f : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) : ∀ (n : ℕ) (d : ∀ j : Fin n, S (.down t i j))
    (d' : ∀ j : Fin n, S' (.down t i j)), Path.Fam.zip f (downFam t i n d) (downFam t i n d') = downFam t i n fun j => f _ (d j) (d' j)
  | 0, _, _ => rfl
  | n + 1, d, d' => by
      show Path.Fam.zip f (Path.Fam.append (p := Path.one (.down t i n)) ((), d (Fin.last n)) (downFam t i n fun j => d j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), d' (Fin.last n)) (downFam t i n fun j => d' j.castSucc)) = _
      refine (zip_append f _ _ _ _ _ _).trans ?_
      rw [zip_down f t i n]
      rfl

theorem restrictPol_row (P : PolE G) (j : ℕ) : ∀ n, restrictPol P (rowPath T j n) =
    rowFam (S := fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank) j n fun i => polOf P (.right i j)
  | 0 => rfl
  | n + 1 => by
      show (restrictPol P (rowPath T j n), polOf P (.right n j)) = _
      rw [restrictPol_row P j n]
      rfl

theorem restrictPol_down (P : PolE G) (t : T) (i : ℕ) : ∀ n, restrictPol P (downPath t i n) =
    downFam (S := fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank) t i n fun j => polOf P (.down t i j)
  | 0 => rfl
  | n + 1 => by
      show restrictPol P ((Path.one (.down t i n)).comp (downPath t i n)) = _
      rw [restrictPol_append, restrictPol_down P t i n]
      rfl

theorem famProd_row (j : ℕ) : ∀ (n : ℕ) (f : ∀ i : Fin n, Sch G (.right i j))
    (x : ∀ i : Fin n, WO (G.pS (Arrow.right (T := T) i j).pair) (G.pT (Arrow.right (T := T) i j).pair)),
    famProd (rowPath T j n) (rowFam j n f) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) j n x) = ∏ i, f i (x i)
  | 0, _, _ => Fin.prod_univ_zero _ |>.symm
  | n + 1, f, x => by
      show famProd (rowPath T j n) (rowFam j n fun i => f i.castSucc)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) j n fun i => x i.castSucc) * f (Fin.last n) (x (Fin.last n)) = _
      rw [famProd_row j n, Fin.prod_univ_castSucc]

theorem famProd_down (t : T) (i : ℕ) : ∀ (n : ℕ) (f : ∀ j : Fin n, Sch G (.down t i j))
    (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair)),
    famProd (downPath t i n) (downFam t i n f) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) = ∏ j, f j (y j)
  | 0, _, _ => Fin.prod_univ_zero _ |>.symm
  | n + 1, f, y => by
      show famProd ((Path.one (.down t i n)).comp (downPath t i n))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), y (Fin.last n))
          (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)) = _
      refine (famProd_append _ _ _ _ _ _).trans ?_
      rw [famProd_down t i n, Fin.prod_univ_castSucc]
      show 1 * f (Fin.last n) (y (Fin.last n)) * _ = _
      rw [one_mul, mul_comm]

theorem halfAll_row (e : AE D) (j : ℕ) : ∀ (n : ℕ)
    (x : ∀ i : Fin n, WO (G.pS (Arrow.right (T := T) i j).pair) (G.pT (Arrow.right (T := T) i j).pair)),
    HalfAll (G := G) e (rowPath T j n) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) j n x) ↔ ∀ i, IsHalf e (x i)
  | 0, _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | n + 1, x => by
      show HalfAll (G := G) e (rowPath T j n) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) j n fun i => x i.castSucc) ∧
        IsHalf e (x (Fin.last n)) ↔ _
      rw [halfAll_row e j n, Fin.forall_fin_succ']

theorem halfAll_down (e : AE D) (t : T) (i : ℕ) : ∀ (n : ℕ)
    (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair)),
    HalfAll (G := G) e (downPath t i n) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) ↔ ∀ j, IsHalf e (y j)
  | 0, _ => ⟨fun _ j => j.elim0, fun _ => trivial⟩
  | n + 1, y => by
      show HalfAll (G := G) e ((Path.one (.down t i n)).comp (downPath t i n))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), y (Fin.last n))
          (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)) ↔ _
      refine (halfAll_append _ _ _ _ _).trans ?_
      rw [halfAll_down e t i n, Fin.forall_fin_succ']
      show (True ∧ IsHalf e (y (Fin.last n))) ∧ _ ↔ _
      rw [true_and, and_comm]

theorem vecAll_row {W : G.Weil} (ρ : RealMatch W) (e : AE D) (j : ℕ) : ∀ (n : ℕ) (φ f : ∀ i : Fin n, Sch G (.right i j)),
    VecAll ρ e (rowPath T j n) (rowFam j n φ) (rowFam j n f) ↔ ∀ i : Fin n, IsLocVec W (.chi i j) e (ρ.vX i j) (φ i) (f i)
  | 0, _, _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | n + 1, φ, f => by
      show VecAll ρ e (rowPath T j n) (rowFam j n fun i => φ i.castSucc) (rowFam j n fun i => f i.castSucc) ∧
        IsLocVec W (.chi n j) e (ρ.vX n j) (φ (Fin.last n)) (f (Fin.last n)) ↔ _
      rw [vecAll_row ρ e j n, Fin.forall_fin_succ']
      rfl

theorem vecAll_down {W : G.Weil} (ρ : RealMatch W) (e : AE D) (t : T) (i : ℕ) : ∀ (n : ℕ) (φ f : ∀ j : Fin n, Sch G (.down t i j)),
    VecAll ρ e (downPath t i n) (downFam t i n φ) (downFam t i n f) ↔ ∀ j : Fin n, IsLocVec W (.mu t i j) e (ρ.vT i j) (φ j) (f j)
  | 0, _, _ => ⟨fun _ j => j.elim0, fun _ => trivial⟩
  | n + 1, φ, f => by
      show VecAll ρ e ((Path.one (.down t i n)).comp (downPath t i n))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), φ (Fin.last n)) (downFam t i n fun j => φ j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc)) ↔ _
      refine (vecAll_append _ _ _ _ _ _ _ _).trans ?_
      rw [vecAll_down ρ e t i n, Fin.forall_fin_succ']
      show (True ∧ IsLocVec W (.mu t i n) e (ρ.vT i n) (φ (Fin.last n)) (f (Fin.last n))) ∧ _ ↔ _
      rw [true_and, and_comm]
      rfl

end Prods

section Opp

variable (t : T)

def oppFam (d : SchRow G × SchDown G t) : PureT G (oppPath t D.R.m) :=
  Path.Fam.append (q := downPath t D.R.m D.R.m) (rowFam D.R.m D.R.m d.1) (downFam t D.R.m D.R.m d.2)

def oppArg (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) : ArgT G (oppPath t D.R.m) :=
  Path.Fam.append (q := downPath t D.R.m D.R.m) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) D.R.m D.R.m x)
    (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t D.R.m D.R.m y)

theorem oppFam_bijective : Function.Bijective (oppFam (G := G) t) := by
  constructor
  · rintro ⟨r, s⟩ ⟨r', s'⟩ h
    obtain ⟨h1, h2⟩ := append_inj _ _ _ _ _ _ h
    exact Prod.ext (rowFam_inj _ _ _ _ h1) (downFam_inj _ _ _ _ _ h2)
  · intro f
    obtain ⟨d, e, h⟩ := append_surj (rowPath T D.R.m D.R.m) (downPath t D.R.m D.R.m) f
    obtain ⟨r, hr⟩ := rowFam_surj _ _ d
    obtain ⟨s, hs⟩ := downFam_surj _ _ _ e
    exact ⟨(r, s), by rw [← h, ← hr, ← hs]; rfl⟩

def oppEquiv : SchRow G × SchDown G t ≃ PureT G (oppPath t D.R.m) := Equiv.ofBijective _ (oppFam_bijective t)

theorem famProd_opp (d : SchRow G × SchDown G t) (x y) :
    famProd (oppPath t D.R.m) (oppFam t d) (oppArg t x y) = (∏ i, d.1 i (x i)) * ∏ j, d.2 j (y j) := by
  refine (famProd_append _ _ _ _ _ _).trans ?_
  rw [famProd_row, famProd_down]

theorem halfAll_opp (e : AE D) (x y) :
    HalfAll (G := G) e (oppPath t D.R.m) (oppArg t x y) ↔ (∀ i, IsHalf e (x i)) ∧ ∀ j, IsHalf e (y j) := by
  refine (halfAll_append _ _ _ _ _).trans ?_
  rw [halfAll_row, halfAll_down]

theorem vecAll_opp {W : G.Weil} (ρ : RealMatch W) (e : AE D) (φ d : SchRow G × SchDown G t) :
    VecAll ρ e (oppPath t D.R.m) (oppFam t φ) (oppFam t d) ↔
      (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i)) ∧
        ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j) := by
  refine (vecAll_append _ _ _ _ _ _ _ _).trans ?_
  rw [vecAll_row, vecAll_down]

theorem pathArgs_opp (B : Frames G) (w : Pl D.host.E) (x y) :
    pathArgs B t w (oppPath t D.R.m) (oppArg t x y) = oppArgs t B w x y := by
  funext e
  have hc := pathArgs_comp B t w (rowPath T D.R.m D.R.m) (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) D.R.m D.R.m x) e
    (downPath t D.R.m D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t D.R.m D.R.m y)
  cases e with
  | theta i j =>
    by_cases h : j < D.R.m ∧ i = D.R.m
    · obtain ⟨hj, rfl⟩ := h
      refine (hc.1 ((mem_edges_down t _ _ _).2 ⟨j, hj, rfl⟩)).trans ?_
      rw [pathArgs_down B t w _ _ y j hj]
      simp only [oppArgs, locArg, hj, le_refl, and_self, and_true, true_and, ↓reduceDIte]
      exact Matrix.ext fun a b => rfl
    · have h1 : GlobalTheory.SplitFlip.Edge.theta i j ∉ edges (downPath t D.R.m D.R.m) := by
        rw [mem_edges_down]
        rintro ⟨k, hk, hk'⟩
        simp only [GlobalTheory.SplitFlip.Edge.theta.injEq] at hk'
        exact h ⟨hk'.2 ▸ hk, hk'.1⟩
      have h2 : GlobalTheory.SplitFlip.Edge.theta i j ∉ edges (rowPath T D.R.m D.R.m) := by
        rw [mem_edges_row]
        rintro ⟨k, _, hk'⟩
        cases hk'
      refine (hc.2 h1).trans ?_
      rw [pathArgs_zero B t w _ _ _ h2]
      simp only [oppArgs, dif_neg h]
  | ex i j =>
    have h1 : GlobalTheory.SplitFlip.Edge.ex i j ∉ edges (downPath t D.R.m D.R.m) := by
      rw [mem_edges_down]
      rintro ⟨k, _, hk'⟩
      cases hk'
    refine (hc.2 h1).trans ?_
    by_cases h : i < D.R.m ∧ j = D.R.m
    · obtain ⟨hi, rfl⟩ := h
      rw [pathArgs_row B t w _ _ x i hi]
      simp only [oppArgs, locArg, hi, le_refl, and_self, and_true, true_and, ↓reduceDIte]
      exact Matrix.ext fun a b => rfl
    · have h2 : GlobalTheory.SplitFlip.Edge.ex i j ∉ edges (rowPath T D.R.m D.R.m) := by
        rw [mem_edges_row]
        rintro ⟨k, hk, hk'⟩
        simp only [GlobalTheory.SplitFlip.Edge.ex.injEq] at hk'
        exact h ⟨hk'.1 ▸ hk, hk'.2⟩
      rw [pathArgs_zero B t w _ _ _ h2]
      simp only [oppArgs, dif_neg h]

theorem zip_opp (W : G.Weil) (P : PolE G) (d : SchRow G × SchDown G t) :
    Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (oppFam t d) (restrictPol P (oppPath t D.R.m)) =
      oppPure W t (toOpp P) d := by
  unfold oppPath oppFam oppPure
  rw [restrictPol_append, zip_append, restrictPol_row, restrictPol_down, zip_row, zip_down]
  rfl

end Opp

end Grid

theorem flipFin_of_repFin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (Φ : G.Datum) (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G (oppPath t D.R.m))
    (h : GlobalTheory.FlipRun.RepFin B ρ t (oppPath t D.R.m) τ (Tflip W B t Φ)) :
    ∃ τ', GlobalTheory.RowClaim.IsFlipFin t B ρ Φ τ' ∧
      GlobalTheory.FlipRun.tensE W (oppPath t D.R.m) Q τ = GlobalTheory.RowClaim.oppTens W t (Q.mapDomain GlobalTheory.FlipRun.toOpp) τ' := by
  obtain ⟨e, he, φ, hφ, hs⟩ := h
  let E := oppEquiv (G := G) t
  have hE : ∀ d, E d = oppFam t d := fun _ => rfl
  refine ⟨Finsupp.equivMapDomain E.symm τ, ⟨e, he, fun d => E.symm (φ (E d)), ?_, ?_⟩, ?_⟩
  · intro d hd
    rw [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply, Equiv.symm_symm] at hd
    have h1 := hφ (E d) (Finsupp.mem_support_iff.2 hd)
    rw [← E.apply_symm_apply (φ (E d)), hE, hE] at h1
    exact (vecAll_opp t ρ e _ _).1 h1
  · intro x y hx hy
    have h1 := hs (oppArg t x y) ((halfAll_opp t e x y).2 ⟨hx, hy⟩)
    simp only [pathArgs_opp] at h1
    rw [← h1, Finsupp.sum_equivMapDomain]
    refine Finsupp.sum_congr fun d _ => ?_
    beta_reduce
    rw [E.apply_symm_apply, mul_assoc]
    conv_rhs => rw [← E.apply_symm_apply (φ d), hE, famProd_opp]
  · unfold tensE tensT oppTens
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul, Finsupp.single_add, Finsupp.sum_add]),
      Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul, Finsupp.single_add, Finsupp.sum_add])]
    refine Finsupp.sum_congr fun P _ => ?_
    rw [Finsupp.sum_equivMapDomain]
    refine Finsupp.sum_congr fun d _ => ?_
    congr 1
    conv_lhs => rw [← E.apply_symm_apply d]
    exact zip_opp t W P (E.symm d)

end GlobalTheory.OppConv
