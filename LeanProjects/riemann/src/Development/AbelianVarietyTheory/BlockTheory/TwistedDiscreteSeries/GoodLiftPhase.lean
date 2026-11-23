import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

def RatTest (X : CxData A) : Prop :=
  ∀ (j : Bs.J) (t : Bs.Tup), ∃ (n : ℕ) (l : Fin n → (X.W j →ₗ[ℂ] ℂ)),
    (∀ w : X.W j, (∀ k, l k w = 0) → w = 0) ∧
      ∀ (x : A.FL j t) (k : Fin n), ∃ a : K, l k (X.θ' j t (X.jL j t x)) = Bs.v0.embedding a

def KerRat (X : CxData A) : Prop :=
  ∀ (j : Bs.J) (t : Bs.Tup),
    LinearMap.ker (X.θ' j t) = Submodule.span ℂ {u | ∃ x : A.FL j t, X.jL j t x = u ∧ X.θ' j t u = 0}

def LevelRat (X : CxData A) (b : Bool) (V : ∀ j t, Submodule K (A.FL j t)) : Prop :=
  ∀ (j : Bs.J) (t : Bs.Tup), ∀ x ∈ V j t,
    ∃ y : Fin (X.dW b j) → K, X.θ' j t (X.jL j t x) = X.w0C b j (cpt Bs.v0.embedding y)

def withLift (X : CxData A) (θ : ∀ j t, X.FLC j t →ₗ[ℂ] X.W j) : CxData A := { X with θ' := θ }

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def liftLvl (F : Face D A) (b : Bool) : Lvl D.what₂.LL G := A.fam.lvlA (F.lvl b).P (F.lvl b).ψ

def goodLift (F : Face D A) (b : Bool) (j : Fin D.R.m) (t : T) : Submodule D.what₂.LL (A.fam.amb.FL j t) :=
  LinearMap.range ((A.fam.L j t).S.gaOp (A.fam.L j t).r (goodAt (liftLvl F b).X (liftLvl F b).P (liftLvl F b).ψ))

def cxPhase (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : CxData A.fam.amb :=
  withLift (R.toCx F) fun j t =>
    Tw.map (E := (R.HV j t).H) (F := (R.HW j (sg0 D A)).H) (twAt D.what₂.embLL A.v0) (ph j • R.thG j t)

def LiftKerTest (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop := RatTest (cxPhase R F ph)

def LiftKerSpan (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop := KerRat (cxPhase R F ph)

def LiftBaseRat (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop :=
  LevelRat (cxPhase R F ph) false (goodLift F false)

def LiftsRational (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop :=
  (∀ j, ‖ph j‖ = 1) ∧ LiftKerTest R F ph ∧ LiftBaseRat R F ph

theorem liftWeight_complexPoint_eq_twist (R : RealDat D A Ks) (F : Face D A) (b : Bool) (j : Fin D.R.m)
    (y : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → D.what₂.LL) :
    Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) ((R.toCx F).w0C b j (cpt A.v0.embedding y)) =
      (R.FW j).j (sg0 D A) (∑ k, y k • R.bL F b j k) := by
  have hn : (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) * (((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) = 1 := by
    have h0 : 0 < RealDat.nP F b := by
      unfold RealDat.nP
      exact_mod_cast Nat.card_pos
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h0).ne', Complex.ofReal_one]
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : (R.toCx F).w0C b j (cpt A.v0.embedding y) =
      ∑ k, A.v0.embedding (y k) • (R.toCx F).eW b j ((R.toCx F).bW b j A.v0 k) := by
    simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
    rfl
  rw [h1, map_sum]
  have h2 : ∀ (s : Bool) (f : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → Tw s (R.HW j (sg0 D A)).H),
      Tw.out (∑ k, f k) = ∑ k, Tw.out (f k) := fun _ _ => rfl
  refine (h2 _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [map_smulₛₗ]
  show cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y k)) •
    ((((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) •
      (R.FW j).j (sg0 D A) (R.bL F b j k))) = _
  rw [smul_smul (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)), hn, one_smul, R.emb0, cj_cj]
  congr 1
  exact (DFunLike.congr_fun hs (y k)).symm

theorem twMap_smul {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (s : Bool) (c : ℂ) (f : E →ₗ[ℂ] E') : Tw.map s (c • f) = cj s c • Tw.map s f := by
  ext u
  show c • f (Tw.out u) = cj s (cj s c) • f (Tw.out u)
  rw [cj_cj]

theorem cxPhase_eq (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) :
    cxPhase R F ph = withLift (R.toCx F) fun j t => cj (twAt D.what₂.embLL A.v0) (ph j) • (R.toCx F).θ' j t :=
  congrArg (withLift (R.toCx F)) (funext fun j => funext fun t => twMap_smul _ (ph j) (R.thG j t))

end GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

end
