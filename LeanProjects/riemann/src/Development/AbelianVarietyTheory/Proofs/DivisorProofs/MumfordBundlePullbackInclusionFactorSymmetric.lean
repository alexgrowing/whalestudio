import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MumSymPull

open GlobalTheory.CoordToExt GlobalTheory.RigidTranslate

variable {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

omit [IsCommMonObj G] in
theorem comp_psum {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    h ≫ psum G x I = psum G (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rw [← Category.assoc, comp_toUnit]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    exact MonObj.comp_mul _ _ _

def chartPullCube (L : LB G.left) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    ChartPull (cubeLB G ![s', t'] L) (cubeLB G ![s, t] L) h.left :=
  chartPullSame L _ _ _ h.left fun I => by
    rw [← Over.comp_left, comp_psum]
    congr 2
    funext k
    fin_cases k
    exacts [hs, ht]

theorem cube_swap (hL : L.IsLB) (s t : T ⟶ G) : LBIso (cubeLB G ![s, t] L) (cubeLB G ![t, s] L) := by
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ isGen_one fun U _ f => ?_
  refine (congrArg₂ (· * ·) (Fintype.prod_empty _) (prod_square ![s, t] fun x => f x.left)).trans
    (Eq.symm ((prod_square ![t, s] fun x => f x.left).trans ?_))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, _root_.mul_comm t s]
  rw [mul_right_comm (f _) (f t.left)⁻¹]

theorem cube_pull (hL : L.IsLB) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    LBIso (cubeLB G ![s', t'] L) ((cubeLB G ![s, t] L).pull h.left) := by
  have r : LBIso (cubeLB G ![s, t] L) (cubeLB G ![s, t] L) := exists_iso hL rfl _
  exact LBIso.chartPull (chartPullCube L s t h s' t' hs ht) (GlobalTheory.chartPullPull _ h.left) r

theorem cube_adj {a b : G ⟶ G}
    (H : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ b] L)) (s t : T ⟶ G) :
    LBIso (cubeLB G ![s ≫ a, t] L) (cubeLB G ![s, t ≫ b] L) :=
  LBIso.chartPull (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp))
    (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp)) H

theorem lbIso_swap : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  intro S G G' _ _ _ _ L hL O _ _ oG hadj e f inc _ he hef P hP hPL
  have cI : ∀ s t : G2 G ⟶ G', (cubeLB G' ![s, t] L).IsLB := fun s t => DVR.linComb_isLB _ hL _ _
  have lI : (abelian₂ G' L).IsLB := DVR.linComb_isLB _ hL _ _
  set x : G2 G ⟶ G' := fst G G ≫ inc with hx
  set y : G2 G ⟶ G' := snd G G ≫ inc with hy
  have xe : x ≫ oG.act e = x := by rw [hx, Category.assoc, he]
  have ye : y ≫ oG.act e = y := by rw [hy, Category.assoc, he]
  have h₁ : LBIso P (cubeLB G' ![x, y ≫ oG.act f] L) :=
    hPL.trans hP (pull_isLB lI _) (cI _ _) (cube_pull hL _ _ _ _ _ (by simp) (by simp [hy])).symm
  have h₂ : LBIso (P.pull (lift (snd G G) (fst G G)).left) (cubeLB G' ![y, x ≫ oG.act f] L) :=
    LBIso.chartPull (GlobalTheory.chartPullPull P _)
      (chartPullCube L _ _ (lift (snd G G) (fst G G)) _ _ (by simp [hx, hy]) (by simp [hx, hy])) h₁
  have h₃ := cube_swap hL y (x ≫ oG.act f)
  have h₄ := cube_adj (hadj f) x y
  have h₅ := cube_adj (hadj e) x (y ≫ oG.act (star f))
  have h₆ := cube_adj (hadj e) x (y ≫ oG.act f)
  rw [xe] at h₅ h₆
  have k : (y ≫ oG.act (star f)) ≫ oG.act (star e) = (y ≫ oG.act f) ≫ oG.act (star e) := by
    have := congrArg (fun a => y ≫ oG.act a) hef
    simp only [oG.map_mul] at this
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, ye] at this
    exact this.symm
  rw [k] at h₅
  have h₇ : LBIso (cubeLB G' ![y, x ≫ oG.act f] L) (cubeLB G' ![x, y ≫ oG.act f] L) :=
    h₃.trans (cI _ _) (cI _ _) (cI _ _) (h₄.trans (cI _ _) (cI _ _) (cI _ _)
      (h₅.trans (cI _ _) (cI _ _) (cI _ _) h₆.symm))
  exact h₁.trans hP (cI _ _) (pull_isLB hP _) (h₇.symm.trans (cI _ _) (cI _ _) (pull_isLB hP _) h₂.symm)

end GlobalTheory.MumSymPull
