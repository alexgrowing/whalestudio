import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_addEquiv_of_coord {L L' R R' : Type} [Field L] [Field L'] [Semiring R] [Semiring R'] {n n' : ℕ}
    [Module R (Fin n → L)] [Module R' (Fin n' → L')] (hn : n = n') (W : Submodule R (Fin n → L))
    (W' : Submodule R' (Fin n' → L')) (ι : L →+* L')
    (h1 : ∀ y : W, ∃ y' : W', ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → y'.1 k' = ι (y.1 k))
    (h2 : ∀ y' : W', ∃ y : W, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → y'.1 k' = ι (y.1 k)) :
    ∃ φ : W ≃+ W', ∀ (y : W) (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k) := by
  subst hn
  choose F hF using h1
  have hF' : ∀ y k, (F y).1 k = ι (y.1 k) := fun y k => hF y k k rfl
  let ψ : W →+ W' :=
    { toFun := F
      map_zero' := Subtype.ext (funext fun k => by rw [hF']; simp)
      map_add' := fun a b => Subtype.ext (funext fun k => by
        simp only [Submodule.coe_add, Pi.add_apply, hF', map_add]) }
  have hb : Function.Bijective ψ := by
    constructor
    · intro a b hab
      refine Subtype.ext (funext fun k => ι.injective ?_)
      rw [← hF', ← hF']
      exact congrArg (fun v : W' => v.1 k) hab
    · intro y'
      obtain ⟨y, hy⟩ := h2 y'
      exact ⟨y, Subtype.ext (funext fun k => (hF' y k).trans (hy k k rfl).symm)⟩
  exact ⟨AddEquiv.ofBijective ψ hb, fun y k k' hk => hF y k k' hk⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem cusp_type_eq_of_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {H H' : Host E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {U : ∀ j (σ : c.F →+* ℂ), Formalism.L2.Pj.Unf (Xo j) c σ r} {U' : ∀ j (σ : c'.F →+* ℂ), Formalism.L2.Pj.Unf (Xo' j) c' σ r}
    (hU : HEq U' U) {a a' : (E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {j j' : ℕ} (hj : j' = j) :
    (Formalism.L2.Pj.cusp (Xo' j') c' (U' j') a' n' : Type) = (Formalism.L2.Pj.cusp (Xo j) c (U j) a n : Type) := by
  subst hH ha hn hj
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hU
  rfl

theorem extendByZero_congr_of_heq {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : Formalism.L2.Pj.ext0 (a' t) = Formalism.L2.Pj.ext0 (a t) := by
  subst hj; cases h; rfl

set_option maxHeartbeats 4000000 in

theorem cusp_type_eq_dat {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hN : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z.R.nW j = z'.R.nW j' ∧
    (z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n : Type) =
      (z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n : Type) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j) := by
    funext x
    unfold Formalism.L2.Pj.wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : Formalism.L2.Pj.ext0 ((z'.geo.κ j').aP t) = Formalism.L2.Pj.ext0 ((z.geo.κ j).aP t) :=
      extendByZero_congr_of_heq (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : Formalism.L2.Pj.ext0 ((z'.geo.κ j').aM t) = Formalism.L2.Pj.ext0 ((z.geo.κ j).aM t) :=
      extendByZero_congr_of_heq (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M := cusp_type_eq_of_heq hH hN.l hN.c hN.Dw hN.Xo hN.U ha hκ.2.2 hj1
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  refine ⟨hn.symm, ?_⟩
  exact (by with_unfolding_all exact (M :))

set_option maxHeartbeats 4000000 in

theorem forms_match_dat {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hN : ExtN z z') (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ t, (w'.st Z').toD7.what₂.embLL (φ t) = (w.st Z).toD7.what₂.embLL t)
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z.R.nW j = z'.R.nW j' ∧
    (∀ y : (z.R.FW j).WK, ∃ y' : (z'.R.FW j').WK, ∀ (k : Fin (z.R.nW j))
      (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y'.1 k' = φ (y.1 k)) ∧
    (∀ y' : (z'.R.FW j').WK, ∃ y : (z.R.FW j).WK, ∀ (k : Fin (z.R.nW j))
      (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y'.1 k' = φ (y.1 k)) := by
  obtain ⟨hn, M⟩ := cusp_type_eq_dat hB z z' hN j j' hj
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  refine ⟨hn, fun y => ?_, fun y' => ?_⟩
  · obtain ⟨u, rfl⟩ : ∃ u, z.geo.fw.e j u = y := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    exact ⟨z'.geo.fw.e j' (cast M.symm u), fun k k' hk =>
      hinj ((hN.forms j j' hj u (cast M.symm u) (cast_heq _ _) k k' hk).trans (hφ _).symm)⟩
  · obtain ⟨u', rfl⟩ : ∃ u', z'.geo.fw.e j' u' = y' := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    exact ⟨z.geo.fw.e j (cast M u'), fun k k' hk =>
      hinj ((hN.forms j j' hj (cast M u') u' (cast_heq _ _).symm k k' hk).trans (hφ _).symm)⟩

theorem forms_corr_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → (sideAt x g hg a).R.nW j = (sideAt x' g' hg' a').R.nW j' ∧ ∃ φ : ↥((sideAt x g hg a).R.FW j).WK ≃+ ↥((sideAt x' g' hg' a').R.FW j').WK, ∀ (y : ↥((sideAt x g hg a).R.FW j).WK) (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj
  obtain ⟨hn, h1, h2⟩ := forms_match_dat l.enl.1 (datAt x g) (datAt x' g') l.extN ι l.cp.embLL j j' hj
  exact ⟨hn, exists_addEquiv_of_coord hn _ _ ι h1 h2⟩

end GlobalTheory.HeightCounting.SerMove

end
