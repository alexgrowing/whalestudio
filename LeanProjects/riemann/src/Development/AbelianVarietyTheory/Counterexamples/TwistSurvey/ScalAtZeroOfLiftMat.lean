import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWTie

noncomputable section

open NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix

namespace GlobalTheory.ScalarConjugation

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem maj_eq_zero {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K)
    (h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x x = 0) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x y = 0 := by
  have hc : ∀ i, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i = 0 := by
    have hs : ∑ i, ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) : ℝ) : ℂ) = 0 := by
      rw [← h]
      unfold Formalism.HermitianLatticesTheory.majAt
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hr : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) = 0 := by
      exact_mod_cast hs
    intro i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 hr i (Finset.mem_univ i))
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, star_zero, zero_mul]

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def im (j : Bs.J) (v : InfinitePlace K) (x : Fin ((lv (fc X.zs) b).dZ j Bs.μ0) → K) : X.WC b j v :=
  X.wC b j v (cpt v.embedding ((X.liftMat cr b j Bs.μ0).mulVec x))

def ScalAt (j : Bs.J) (p : Bs.Ix) (v : InfinitePlace K) (l : ℝ) : Prop :=
  ∀ x, X.tC cr b j Bs.μ0 (cpt Bs.v0.embedding x) ∈ X.Wp j p → ∀ y,
    ⟪im X cr b j v x, im X cr b j v y⟫_ℂ =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XT j Bs.μ0) v x y

def twist (S : ∀ b j v, X.WC b j v →ₗ[ℂ] X.WC b j v) (lam' : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) : CxData A :=
  { X with bW := fun b j v k => S b j v (X.bW b j v k), lam := lam' }

def shear {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u u' : E) : E →ₗ[ℂ] E :=
  LinearMap.id + (innerₛₗ ℂ u').smulRight u

end Abstract

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def withJ (j' : ∀ i σ, (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H) : RealDat D A Ks :=
  { R with FW := fun i => { R.FW i with j := j' i } }

end Concrete

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1000000 in

def fwTie_withJ {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (h : FWTie T R κ v₀) (j' : ∀ i σ, (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H)
    (hj : ∀ i σ, GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) → j' i σ = (R.FW i).j σ) :
    FWTie T (withJ R j') κ v₀ where
  alg_eq := h.alg_eq
  e := h.e
  ks := h.ks
  kap := h.kap
  pt := h.pt
  nrm_eq := h.nrm_eq
  laws := h.laws
  chiR := h.chiR
  hv₀ := h.hv₀
  x0 := h.x0
  ev0 i σ hσ hV hn := (hj i σ hσ).trans (h.ev0 i σ hσ hV hn)
  ev i σ hσ hV he f := by
    have := h.ev i σ hσ hV he f
    rw [← hj i σ hσ] at this
    exact this

end Comparison₂

end GlobalTheory.ScalarConjugation
