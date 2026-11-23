import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem mulSingle_ne {m : ℕ} (κ : GL (Fin (Γ.rank (0, m))) k) {X : ℕ × ℕ} (h : X ≠ (0, m)) :
    (Pi.mulSingle (0, m) κ : Γ.VertexGroup) X = 1 := Pi.mulSingle_eq_of_ne h _

theorem moveArgs_fill (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (x : ColArgs Γ) (y : RowArgs Γ)
    (e : Vars Γ) :
    Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (fill hs x y e) = fill hs x (Function.update y 0 ((κ⁻¹).val * y 0)) e := by
  funext b
  cases b with
  | theta i j =>
    by_cases h : i = Γ.m
    · subst h
      rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt, hm]), mulSingle_ne κ (by simp [Edge.src, hm])]
      simp [fill]
    · simp [moveArgs, fill, h]
  | ex i j =>
    by_cases hj : j = Γ.m
    · subst hj
      by_cases hi : i = 0
      · subst hi
        rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), fill_ex, fill_ex]
        simp only [Edge.src, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [Matrix.transpose_mul, Assignment.read, invT_val]
      · rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), mulSingle_ne κ (by simp [Edge.src, hi])]
        simp [fill, Function.update_of_ne hi]
    · simp [moveArgs, fill, hj]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem moveArgs_mul (s : Assignment) (g g' : Γ.VertexGroup) (z : Γ.Args) :
    Γ.moveArgs s (g * g') z = Γ.moveArgs s g' (Γ.moveArgs s g z) := by
  funext b
  simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem mulSingle_comm (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) :
    Pi.mulSingle (0, Γ.m) κ * g = g * Pi.mulSingle (0, Γ.m) κ := by
  funext X
  by_cases h : X = (0, Γ.m)
  · subst h; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne h]

theorem elt_zero_m (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) : ρ.elt β (0, Γ.m) = 1 := by
  simp [Reps.elt, onColumn, Ne.symm hm]

theorem prod_edgeFactor (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod =
      Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) := by
  have h1 : ∀ b : Edge, b.src ≠ (0, Γ.m) → b.tgt ≠ (0, Γ.m) → Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) b = 1 := by
    intro b hs ht
    simp [edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
  obtain ⟨n, hn⟩ : ∃ n, Γ.m = n + 1 := ⟨Γ.m - 1, by omega⟩
  rw [oppositePath, List.map_append, List.prod_append]
  have h2 : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src, hm]) (by simp [Edge.tgt, hm])
  rw [h2, mul_one]
  have h3 : List.range Γ.m = 0 :: (List.range n).map Nat.succ := by rw [hn, List.range_succ_eq_map]
  rw [h3, List.map_cons, List.map_cons, List.prod_cons]
  have h4 : ((((List.range n).map Nat.succ).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src]) (by simp [Edge.tgt])
  rw [h4, mul_one]

variable [MeasurableSpace k] [BorelSpace k]

theorem moved_law (keep : Bool) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) (κ : GL (Fin (Γ.rank (0, Γ.m))) k)
    (T : Γ.Args → ℂ) (c : ℂ) (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (z : Γ.Args) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
      moved Γ keep g T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) = c * moved Γ keep g T z := by
  have h1 := congrFun hlaw (Γ.moveArgs .one g z)
  simp only [pathAct, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : Γ.moveArgs .one g (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) =
      Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z) := by
    rw [← moveArgs_mul, ← moveArgs_mul, mulSingle_comm κ g hg]
  simp only [moved, pathAct, h2]
  calc _ = (if keep then (1 : ℂ) else (((charFactor Γ g)⁻¹ : ℂˣ) : ℂ)) * ((oppositePath Γ.m).map (Γ.edgeFactor .one g)).prod *
        (((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
          T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z))) := by ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}
  [MeasurableSpace k] [BorelSpace k]

theorem datum_law (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (ψ : AddChar k Circle) (ν : Measure k) {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) (T : Γ.Args → ℂ) (β : Cosets hs J) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (c : ℂ)
    (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (x : ColArgs Γ) (y : RowArgs Γ) :
    Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) *
        (unfTerm ψ ν keep ρ T β).datum x (Function.update y 0 ((κ⁻¹).val * y 0)) =
      c * (unfTerm ψ ν keep ρ T β).datum x y := by
  simp only [unfTerm, flatTensor, flatIntegrand, ← moveArgs_fill hs hm κ x y]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  have h := moved_law keep (ρ.elt β) (elt_zero_m hs hm ρ β) κ T c hlaw (fill hs x y e)
  rw [prod_edgeFactor hm] at h
  simp only
  rw [← mul_assoc, h, mul_assoc]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def kapAt (S : GridChoice W U) (t : T) (w : Pl D.host.E) (k : FinPt G (.grid 0 D.R.m)) :
    GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (S.B.β 0 D.R.m) w (finG (G.V (.grid 0 D.R.m)) k)

theorem edgeFactor_ne_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : GlobalTheory.SplitFlip.Grid k) (g : Γ.VertexGroup) (b : GlobalTheory.SplitFlip.Edge) : Γ.edgeFactor .one g b ≠ 0 := by
  simp only [GlobalTheory.SplitFlip.Grid.edgeFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
    (GlobalTheory.SplitFlip.apow_ne_zero _ _)

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

theorem prod_update_comp {m : ℕ} {X : Fin m → Type} (F : ∀ i, X i → ℂ) (i₀ : Fin m) (f : X i₀ → X i₀) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (fun y => F i₀ (f y)) i (ys i) = ∏ i, F i (Function.update ys i₀ (f (ys i₀)) i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sum_update_comp {κ : Type} {m n : ℕ} {X : Fin n → Type} {Y : Fin m → Type} (τ : κ →₀ ℂ) (A : κ → ∀ j, X j → ℂ)
    (B : κ → ∀ i, Y i → ℂ) (i₀ : Fin m) (f : Y i₀ → Y i₀) (xs : ∀ j, X j) (ys : ∀ i, Y i) :
    (τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, Function.update (B d) i₀ (fun y => B d i₀ (f y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, B d i (Function.update ys i₀ (f (ys i₀)) i) :=
  Finset.sum_congr rfl fun d _ => by beta_reduce; rw [prod_update_comp]

theorem key_cancel (s PE PL P P' : ℂ) (h1 : PE ≠ 0) (h2 : s * PL = PE) (h3 : PE * P' = PL * P) : s * P' = P :=
  mul_left_cancel₀ h1 (by linear_combination s * h3 + P * h2)

end GlobalTheory.FirstRowTermLaw
