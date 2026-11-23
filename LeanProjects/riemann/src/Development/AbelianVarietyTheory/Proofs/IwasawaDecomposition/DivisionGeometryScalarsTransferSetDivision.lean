import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Wp3ApplyEqSqMulSubSqMul
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.OxMove

set_option linter.style.haveILetI false

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

section General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JW (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Type :=
  ∀ i : Fin D.R.m, (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)

def wpW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (i : Fin D.R.m) (c : A3.fam3.base3.Ix) :
    Submodule D.what₂.LL (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) := (by with_unfolding_all exact (((cxW R F u).WpK false i c) :))

def overW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((j i) '' (wpW R F u i c : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)))

def lamW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F)
    (l : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, overW R F u j σ c) → overW R F u j σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        l ((i : ℕ) + 1) σ e = Real.log (R.lam3 i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → l ((i : ℕ) + 1) σ e = 0)

end General

section Copy

variable {B : Base} {C : Cols B} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks]

abbrev mv (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Late B C := Db.setDivZ a N h

set_option maxHeartbeats 4000000 in

theorem lamAre_copy (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ)
    [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)
    {X0 : BaseLevelRowSide a.D} {Y : R3.Read (A3 := A) R.toRealDat F.lv2 X0} (Z : R3.ReadL R F X0 Y) (X : DivX a.D)
    (X' : DivX (mv a N h).D) (hX : HEq X'.logLam X.logLam) {X0' : BaseLevelRowSide (mv a N h).D} :
    letI := alg (mv a N h) iK
    ∀ {Y' : R3.Read (A3 := famInThreeCoefficientChange (mv a N h) A) (real3 (mv a N h) R).toRealDat (face3 (mv a N h) F).lv2 X0'}
      (Z' : R3.ReadL (real3 (mv a N h) R) (face3 (mv a N h) F) X0' Y'), HEq Z'.jW Z.jW → LamAre Z X → LamAre Z' X' := by
  letI := alg (mv a N h) iK
  intro Y' Z' hj hl
  have h1 : lamW R F (R.EEp3, R.toRealDat.EEat, R.Wp3) ((by with_unfolding_all exact (Z.jW :))) X.logLam := (by with_unfolding_all exact (hl :))
  have ej : ((by with_unfolding_all exact (Z.jW :)) : JW R F) = (by with_unfolding_all exact (Z'.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj.symm :)))
  have el : X.logLam = (by with_unfolding_all exact (X'.logLam :)) := eq_of_heq ((by with_unfolding_all exact (hX.symm :)))
  have h2 := cast (congr (congrArg₂ (lamW R F) (parts_eq (mv a N h) R F) ej) el) h1
  exact (by with_unfolding_all exact (h2 :))

end Copy

set_option maxHeartbeats 4000000 in

theorem oAt_setDiv : ∀ (Γ : GeoP) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O : Obj2 (w.D Z)) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h → ∀ (t : RowsT K w Z Wt O.p0) (t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0), R3.Rw.RowsSame t t' → OAt (geoCl Γ) t O.X → Nonempty (OAt (geoCl Γ) t' O'.X) := by
  intro Γ K B f T w Z Wt N h O O' hO t t' hs hp
  have hOX : O'.X = (by with_unfolding_all exact ((divTr (D := w.D Z) N h O.X) :)) := by subst hO; exact (by with_unfolding_all exact ((Eq.refl (divTr (D := w.D Z) N h O.X)) :))
  clear hO
  generalize O'.X = X' at hOX
  revert t'
  generalize O'.p0 = p0'
  intro t' hs
  subst hOX
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' holds' Y' Zr' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hj := hs.jW
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(Db.setDivZ Z N h).W, (Db.setDivZ Z N h).V, (Db.setDivZ Z N h).S, (Db.setDivZ Z N h).N, (Db.setDivZ Z N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (Db.setDivZ Z N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  refine ⟨⟨?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((GeoCl.step (Γ := Γ) (D := (w.st Z).toD7) N h hp.geo) :))
  · exact (by with_unfolding_all exact ((lamAre_copy (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) N h (iK := t.r.z.alg) t.r.z.R t.r.z.F t.r.Z O.X
      (((divTr (D := w.D Z) N h O.X))) (((HEq.refl O.X.logLam))) (X0' := (p0')) (Y' := (Y')) ((Zr')) ((hj)) hp.lam) : _))

end GlobalTheory.Mem.OxMove

end
