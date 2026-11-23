import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Lin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem kerA_col_add (t : T) (j : ℕ) (f f' : Sch G (.col t j)) :
    ∀ g h, W.kerA (.col t j) (f + f') g h = W.kerA (.col t j) f g h + W.kerA (.col t j) f' g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]

theorem kerA_col_smul (t : T) (j : ℕ) (c : ℂ) (f : Sch G (.col t j)) :
    ∀ g h, W.kerA (.col t j) (c • f) g h = c * W.kerA (.col t j) f g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem kerA_right_add (i j : ℕ) (f f' : Sch G (.right i j)) :
    ∀ g h, W.kerA (.right i j) (f + f') g h = W.kerA (.right i j) f g h + W.kerA (.right i j) f' g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]

theorem kerA_right_smul (i j : ℕ) (c : ℂ) (f : Sch G (.right i j)) :
    ∀ g h, W.kerA (.right i j) (c • f) g h = c * W.kerA (.right i j) f g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

end Lin

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Lin2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem liftA_datum_add {a : Arrow T} {f f' f'' : Sch G a} {F : Fn G a.src}
    (hk : ∀ g h, W.kerA a f'' g h = W.kerA a f g h + W.kerA a f' g h)
    (h1 : LiftConv W M a f F) (h2 : LiftConv W M a f' F) :
    liftA W M a f'' F = liftA W M a f F + liftA W M a f' F := by
  funext x
  simp only [liftA_apply, Pi.add_apply, hk, add_mul]
  exact integral_add (h1 x) (h2 x)

theorem liftA_datum_smul {a : Arrow T} {f f'' : Sch G a} {F : Fn G a.src} (c : ℂ)
    (hk : ∀ g h, W.kerA a f'' g h = c * W.kerA a f g h) :
    liftA W M a f'' F = c • liftA W M a f F := by
  funext x
  simp only [liftA_apply, Pi.smul_apply, smul_eq_mul, hk, mul_assoc, integral_const_mul]

theorem pathLift_column_add (t : T) : ∀ (n : ℕ) (f f' f'' : ∀ j : Fin n, Sch G (.col t j)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j ∧ f' j = f'' j) → f'' j0 = f j0 + f' j0 → ∀ F : Fn G (.top 0),
    PathConv W M (colPath t n) (colFam t n f) F → PathConv W M (colPath t n) (colFam t n f') F →
    liftP W M (colPath t n) (colFam t n f'') F =
      liftP W M (colPath t n) (colFam t n f) F + liftP W M (colPath t n) (colFam t n f') F
  | 0, _, _, _, j0, _, _, _, _, _ => j0.elim0
  | n + 1, f, f', f'', j0, hne, h0, F, h1, h2 => by
    have h1a : PathConv W M (colPath t n) (colFam t n fun j => f j.castSucc) F := h1.1
    have h2a : PathConv W M (colPath t n) (colFam t n fun j => f' j.castSucc) F := h2.1
    have h1b : LiftConv W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F) := h1.2
    have h2b : LiftConv W M (.col t n) (f' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) F) := h2.2
    change liftA W M (.col t n) (f'' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f'' j.castSucc) F) =
      liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F) +
      liftA W M (.col t n) (f' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).1
      have e2 : (fun j : Fin n => f' j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).2
      rw [e1] at h1b ⊢
      rw [e2] at h2b ⊢
      exact liftA_datum_add W M (fun g h => by rw [h0]; exact kerA_col_add W t n _ _ g h) h1b h2b
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).1
      have el' : f' (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).2
      have ih := pathLift_column_add t n (fun j => f j.castSucc) (fun j => f' j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F h1a h2a
      rw [el] at h1b ⊢
      rw [el'] at h2b ⊢
      rw [ih]
      exact liftA_add W M h1b h2b

theorem pathLift_column_smul (t : T) (c : ℂ) : ∀ (n : ℕ) (f f'' : ∀ j : Fin n, Sch G (.col t j)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j) → f'' j0 = c • f j0 → ∀ F : Fn G (.top 0),
    liftP W M (colPath t n) (colFam t n f'') F = c • liftP W M (colPath t n) (colFam t n f) F
  | 0, _, _, j0, _, _, _ => j0.elim0
  | n + 1, f, f'', j0, hne, h0, F => by
    change liftA W M (.col t n) (f'' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f'' j.castSucc) F) =
      c • liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => hne _ (Fin.castSucc_lt_last j).ne
      rw [e1]
      exact liftA_datum_smul W M c (fun g h => by rw [h0]; exact kerA_col_smul W t n c _ g h)
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := hne _ (Ne.symm hj)
      have ih := pathLift_column_smul t c n (fun j => f j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F
      rw [el, ih]
      exact liftA_smul W M _ _ c _

theorem pathLift_row_add (k : ℕ) : ∀ (n : ℕ) (f f' f'' : ∀ i : Fin n, Sch G (.right i k)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j ∧ f' j = f'' j) → f'' j0 = f j0 + f' j0 → ∀ F : Fn G (.grid 0 k),
    PathConv W M (rowPath T k n) (rowFam k n f) F → PathConv W M (rowPath T k n) (rowFam k n f') F →
    liftP W M (rowPath T k n) (rowFam k n f'') F =
      liftP W M (rowPath T k n) (rowFam k n f) F + liftP W M (rowPath T k n) (rowFam k n f') F
  | 0, _, _, _, j0, _, _, _, _, _ => j0.elim0
  | n + 1, f, f', f'', j0, hne, h0, F, h1, h2 => by
    have h1a : PathConv W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F := h1.1
    have h2a : PathConv W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F := h2.1
    have h1b : LiftConv W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F) := h1.2
    have h2b : LiftConv W M (.right n k) (f' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F) := h2.2
    change liftA W M (.right n k) (f'' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f'' j.castSucc) F) =
      liftA W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F) +
      liftA W M (.right n k) (f' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).1
      have e2 : (fun j : Fin n => f' j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).2
      rw [e1] at h1b ⊢
      rw [e2] at h2b ⊢
      exact liftA_datum_add W M (fun g h => by rw [h0]; exact kerA_right_add W n k _ _ g h) h1b h2b
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).1
      have el' : f' (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).2
      have ih := pathLift_row_add k n (fun j => f j.castSucc) (fun j => f' j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F h1a h2a
      rw [el] at h1b ⊢
      rw [el'] at h2b ⊢
      rw [ih]
      exact liftA_add W M h1b h2b

theorem pathLift_row_smul (k : ℕ) (c : ℂ) : ∀ (n : ℕ) (f f'' : ∀ i : Fin n, Sch G (.right i k)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j) → f'' j0 = c • f j0 → ∀ F : Fn G (.grid 0 k),
    liftP W M (rowPath T k n) (rowFam k n f'') F = c • liftP W M (rowPath T k n) (rowFam k n f) F
  | 0, _, _, j0, _, _, _ => j0.elim0
  | n + 1, f, f'', j0, hne, h0, F => by
    change liftA W M (.right n k) (f'' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f'' j.castSucc) F) =
      c • liftA W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => hne _ (Fin.castSucc_lt_last j).ne
      rw [e1]
      exact liftA_datum_smul W M c (fun g h => by rw [h0]; exact kerA_right_smul W n k c _ g h)
    · obtain ⟨j1, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      have el : f (Fin.last n) = f'' (Fin.last n) := hne _ (Ne.symm hj)
      have ih := pathLift_row_smul k c n (fun j => f j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F
      rw [el, ih]
      exact liftA_smul W M _ _ c _

end Lin2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Outer

variable {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}

end Outer

section Multi

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
  (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)

def colLift (Q1 : PolCol ch.G) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) : Fn ch.G (.top D.R.m) :=
  liftP ch.W M (colPath t D.R.m)
    (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
    (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a))

def rowLift (Q2 : PolRow ch.G) (η : Module.Dual ℂ R.cX.W) : Fn ch.G (.grid D.R.m D.R.m) :=
  liftP ch.W M (rowPath T D.R.m D.R.m)
    (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i))
    (formGen ch t y η)

theorem genPer_eq (Q : PolCol ch.G × PolRow ch.G) ξ η :
    genPer ch t a M d y Q ξ η = ∫ h in M.fd (.grid D.R.m D.R.m),
      colLift ch t a M d Q.1 ξ (stabilizerEmbedding ch.G.sp.topDec h) * rowLift ch t M d y Q.2 η h ∂M.ν (.grid D.R.m D.R.m) := rfl

theorem genConv_int {Q : PolCol ch.G × PolRow ch.G} {ξ η} (h : GenConv ch t a M d y Q ξ η) :
    IntegrableOn (fun h => colLift ch t a M d Q.1 ξ (stabilizerEmbedding ch.G.sp.topDec h) * rowLift ch t M d y Q.2 η h)
      (M.fd (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) := h.2.2

theorem colLift_add [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ
    (h1 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)))
    (h2 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x' j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a))) :
    colLift ch t a M d (Function.update Q1 i (x + x')) ξ =
      colLift ch t a M d (Function.update Q1 i x) ξ + colLift ch t a M d (Function.update Q1 i x') ξ :=
  pathLift_column_add ch.W M t D.R.m
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x' j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i (x + x') j)) i
    (fun j hj => by simp only [Function.update_of_ne hj, and_self])
    (by simp only [Function.update_self, map_add]) _ h1 h2

theorem colLift_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ :
    colLift ch t a M d (Function.update Q1 i (c • x)) ξ = c • colLift ch t a M d (Function.update Q1 i x) ξ :=
  pathLift_column_smul ch.W M t c D.R.m
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i (c • x) j)) i
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self, map_smul]) _

theorem rowLift_add [DecidableEq (Fin D.R.m)] (Q2 : PolRow ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) η
    (h1 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
      (formGen ch t y η))
    (h2 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x' j))
      (formGen ch t y η)) :
    rowLift ch t M d y (Function.update Q2 i (x + x')) η =
      rowLift ch t M d y (Function.update Q2 i x) η + rowLift ch t M d y (Function.update Q2 i x') η :=
  pathLift_row_add ch.W M D.R.m D.R.m
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x' j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i (x + x') j)) i
    (fun j hj => by simp only [Function.update_of_ne hj, and_self])
    (by simp only [Function.update_self, map_add]) _ h1 h2

theorem rowLift_smul [DecidableEq (Fin D.R.m)] (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) η :
    rowLift ch t M d y (Function.update Q2 i (c • x)) η = c • rowLift ch t M d y (Function.update Q2 i x) η :=
  pathLift_row_smul ch.W M D.R.m c D.R.m
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i (c • x) j)) i
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self, map_smul]) _

theorem colLift_xi_add (Q1 : PolCol ch.G) ξ ξ'
    (h1 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)))
    (h2 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ' (ch.col a))) :
    colLift ch t a M d Q1 (ξ + ξ') = colLift ch t a M d Q1 ξ + colLift ch t a M d Q1 ξ' := by
  have hp : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ + ξ') (ch.col a) =
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) + pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ' (ch.col a) := by
    funext h
    simp only [pairVec_apply, LinearMap.add_apply, Pi.add_apply]
  unfold colLift
  rw [hp]
  exact pathLift_add ch.W M _ _ h1 h2

theorem colLift_xi_smul (Q1 : PolCol ch.G) (c : ℂ) ξ :
    colLift ch t a M d Q1 (c • ξ) = c • colLift ch t a M d Q1 ξ := by
  have hp : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (c • ξ) (ch.col a) =
      c • pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) := by
    funext h
    simp only [pairVec_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  unfold colLift
  rw [hp]
  exact pathLift_smul ch.W M _ _ _ _

theorem formGen_add (η η' : Module.Dual ℂ R.cX.W) : formGen ch t y (η + η') = formGen ch t y η + formGen ch t y η' := by
  funext g
  simp only [formGen, LinearMap.add_apply, Pi.add_apply]

theorem formGen_smul (c : ℂ) (η : Module.Dual ℂ R.cX.W) : formGen ch t y (c • η) = c • formGen ch t y η := by
  funext g
  simp only [formGen, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

theorem rowLift_eta_add (Q2 : PolRow ch.G) η η'
    (h1 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i)) (formGen ch t y η))
    (h2 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i)) (formGen ch t y η')) :
    rowLift ch t M d y Q2 (η + η') = rowLift ch t M d y Q2 η + rowLift ch t M d y Q2 η' := by
  unfold rowLift
  rw [formGen_add]
  exact pathLift_add ch.W M _ _ h1 h2

theorem rowLift_eta_smul (Q2 : PolRow ch.G) (c : ℂ) η :
    rowLift ch t M d y Q2 (c • η) = c • rowLift ch t M d y Q2 η := by
  unfold rowLift
  rw [formGen_smul]
  exact pathLift_smul ch.W M _ _ _ _

end Multi

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Multi2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
  (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)

theorem genPer_col_add [DecidableEq (Fin D.R.m)] (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q1 : PolCol ch.G)
    (Q2 : PolRow ch.G) (i : Fin D.R.m) (x x' : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ η :
    genPer ch t a M d y (Function.update Q1 i (x + x'), Q2) ξ η =
      genPer ch t a M d y (Function.update Q1 i x, Q2) ξ η + genPer ch t a M d y (Function.update Q1 i x', Q2) ξ η := by
  have i1 := genConv_int ch t a M d y (hc (Function.update Q1 i x, Q2) ξ η)
  have i2 := genConv_int ch t a M d y (hc (Function.update Q1 i x', Q2) ξ η)
  have e := colLift_add ch t a M d Q1 i x x' ξ (hc (Function.update Q1 i x, Q2) ξ η).1
    (hc (Function.update Q1 i x', Q2) ξ η).1
  dsimp only at i1 i2
  rw [genPer_eq, genPer_eq, genPer_eq]
  dsimp only
  rw [e]
  simp only [Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem genPer_col_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ η :
    genPer ch t a M d y (Function.update Q1 i (c • x), Q2) ξ η = c * genPer ch t a M d y (Function.update Q1 i x, Q2) ξ η := by
  rw [genPer_eq, genPer_eq]
  dsimp only
  rw [colLift_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem genPer_row_add [DecidableEq (Fin D.R.m)] (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q1 : PolCol ch.G)
    (Q2 : PolRow ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) ξ η :
    genPer ch t a M d y (Q1, Function.update Q2 i (x + x')) ξ η =
      genPer ch t a M d y (Q1, Function.update Q2 i x) ξ η + genPer ch t a M d y (Q1, Function.update Q2 i x') ξ η := by
  have i1 := genConv_int ch t a M d y (hc (Q1, Function.update Q2 i x) ξ η)
  have i2 := genConv_int ch t a M d y (hc (Q1, Function.update Q2 i x') ξ η)
  have e := rowLift_add ch t M d y Q2 i x x' η (hc (Q1, Function.update Q2 i x) ξ η).2.1
    (hc (Q1, Function.update Q2 i x') ξ η).2.1
  dsimp only at i1 i2
  rw [genPer_eq, genPer_eq, genPer_eq]
  dsimp only
  rw [e]
  simp only [Pi.add_apply, mul_add]
  exact integral_add i1 i2

theorem genPer_row_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) ξ η :
    genPer ch t a M d y (Q1, Function.update Q2 i (c • x)) ξ η = c * genPer ch t a M d y (Q1, Function.update Q2 i x) ξ η := by
  rw [genPer_eq, genPer_eq]
  dsimp only
  rw [rowLift_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem genPer_xi_add (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q : PolCol ch.G × PolRow ch.G) ξ ξ' η :
    genPer ch t a M d y Q (ξ + ξ') η = genPer ch t a M d y Q ξ η + genPer ch t a M d y Q ξ' η := by
  have i1 := genConv_int ch t a M d y (hc Q ξ η)
  have i2 := genConv_int ch t a M d y (hc Q ξ' η)
  rw [genPer_eq, genPer_eq, genPer_eq, colLift_xi_add ch t a M d Q.1 ξ ξ' (hc Q ξ η).1 (hc Q ξ' η).1]
  simp only [Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem genPer_xi_smul (Q : PolCol ch.G × PolRow ch.G) (c : ℂ) ξ η :
    genPer ch t a M d y Q (c • ξ) η = c * genPer ch t a M d y Q ξ η := by
  rw [genPer_eq, genPer_eq, colLift_xi_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem genPer_eta_add (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q : PolCol ch.G × PolRow ch.G) ξ η η' :
    genPer ch t a M d y Q ξ (η + η') = genPer ch t a M d y Q ξ η + genPer ch t a M d y Q ξ η' := by
  have i1 := genConv_int ch t a M d y (hc Q ξ η)
  have i2 := genConv_int ch t a M d y (hc Q ξ η')
  rw [genPer_eq, genPer_eq, genPer_eq, rowLift_eta_add ch t M d y Q.2 η η' (hc Q ξ η).2.1 (hc Q ξ η').2.1]
  simp only [Pi.add_apply, mul_add]
  exact integral_add i1 i2

theorem genPer_eta_smul (Q : PolCol ch.G × PolRow ch.G) (c : ℂ) ξ η :
    genPer ch t a M d y Q ξ (c • η) = c * genPer ch t a M d y Q ξ η := by
  rw [genPer_eq, genPer_eq, rowLift_eta_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem genPer_multilinear (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) :
    ∃ Φ : MultilinearMap ℂ (fun j : Fin D.R.m => PolF D (ch.G.V (.top ((j : ℕ) + 1))).rank (ch.G.V (.top j)).rank)
      (MultilinearMap ℂ (fun i : Fin D.R.m => PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank)
        (Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W →ₗ[ℂ] Module.Dual ℂ R.cX.W →ₗ[ℂ] ℂ)),
      ∀ Q ξ η, Φ Q.1 Q.2 ξ η = genPer ch t a M d y Q ξ η := by
  refine ⟨
    { toFun := fun Q1 =>
        { toFun := fun Q2 => LinearMap.mk₂ ℂ (fun ξ η => genPer ch t a M d y (Q1, Q2) ξ η)
            (fun ξ ξ' η => genPer_xi_add ch t a M d y hc _ ξ ξ' η)
            (fun c ξ η => genPer_xi_smul ch t a M d y _ c ξ η)
            (fun ξ η η' => genPer_eta_add ch t a M d y hc _ ξ η η')
            (fun c ξ η => genPer_eta_smul ch t a M d y _ c ξ η)
          map_update_add' := fun Q2 i x x' => LinearMap.ext fun ξ => LinearMap.ext fun η =>
            genPer_row_add ch t a M d y hc Q1 Q2 i x x' ξ η
          map_update_smul' := fun Q2 i c x => LinearMap.ext fun ξ => LinearMap.ext fun η =>
            genPer_row_smul ch t a M d y Q1 Q2 i c x ξ η }
      map_update_add' := fun Q1 i x x' => MultilinearMap.ext fun Q2 => LinearMap.ext fun ξ => LinearMap.ext fun η =>
        genPer_col_add ch t a M d y hc Q1 Q2 i x x' ξ η
      map_update_smul' := fun Q1 i c x => MultilinearMap.ext fun Q2 => LinearMap.ext fun ξ => LinearMap.ext fun η =>
        genPer_col_smul ch t a M d y Q1 Q2 i c x ξ η }, fun Q ξ η => rfl⟩

end Multi2

end GlobalTheory.RowReal
