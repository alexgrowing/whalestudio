import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Core (D : D7) : Type 1 where
  Q : Par D
  U : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r
  V : ℕ → (Q.c.F →+* ℂ) → HSp D
  dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r
  mu : ∀ j σ, GA D (V j σ) → ℂ
  Kf : ∀ j σ, Subgroup (GA D (V j σ))
  pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)

variable {D : D7}

def latHat (V : HSp D) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ a : Af D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) ∧
    ∃ x ∈ V.L0, z = fun i => a ⊗ₜ V.frame.repr x i}

def IsLevelK (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

def xiR (D : D7) : ℝ := ‖D.host.φ₀ D.host.xi0‖

namespace Core

variable (T : Core D)

def σ₀ : T.Q.c.F →+* ℂ := T.Q.c.F.val.toRingHom

theorem good_σ₀ : GoodEmb T.Q.c T.σ₀ := rfl

abbrev R (j : ℕ) : Type := Rul (T.Q.Xo j) T.Q.c

abbrev cuspA (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) a n

abbrev X₀ (j : ℕ) : (T.U j T.σ₀).Comp → Data D.host.E D.R.r := (T.U j T.σ₀).X

def frI (_T : Core D) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := 1

abbrev PtM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def nrmM (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) : ℝ := nrmOf la (y.1 f)

theorem nrmM_le_one_iff (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la) (f : T.R j) :
    T.nrmM j la y f ≤ 1 ↔ 0 ≤ y.1 f := by
  unfold nrmM nrmOf
  have hy := y.2
  unfold valSet at hy
  obtain ⟨x, hx⟩ := hy
  unfold vAtV at hx
  obtain ⟨T1, io, e, -, y', -, eta, -, hxe⟩ := x.2
  rw [hxe] at hx
  unfold profI at hx
  have key : y.1 f = nval T1.V e (evI y' f) := by rw [← hx]
  unfold nval at key
  have hN : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    have h1 : Ideal.absNorm la.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact la.isPrime.ne_top
    exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)
  rw [key]
  by_cases hz : evI y' f = 0
  · simp [hz]
  · simp only [hz, if_false, EReal.coe_ne_top, EReal.toReal_coe, EReal.coe_nonneg]
    constructor
    · intro h
      by_contra hneg
      exact absurd h (not_le.mpr (Real.one_lt_rpow hN (neg_pos.mpr (not_le.mp hneg))))
    · intro h
      exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr h)

def phiAd (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) • adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f)

end Core

structure LawsM (T : Core D) : Prop where

  pins : T.Q.Pins

  half : (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) ∧
    T.Q.l.Mb = ∏ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

  evalWD : ∀ j, InR D j → EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)

  unf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ)

  unTest : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k x,
    FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) ((T.U j σ).un k x)
  chiTriv : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
    ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1

  dictU : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr

  spaceW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j
  levelK : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsLevelK (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ)

  xiAbs : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((T.U j σ).X k).ξ0‖ = xiR D
  muUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)
  muCont : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → Continuous (T.mu j σ)
  finVol : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → FinVol (T.V j σ)

  cuspFD : ∀ j, InR D j → CuspFD (T.Q.Xo j) T.Q.c (T.U j)

  supDef : ∀ j, InR D j → SupDef (T.Q.Xo j) T.Q.c (T.U j)

  cuspidalL2Subspace : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)
  l2Def : ∀ j (hj : InR D j) σ (hσ : GoodEmb T.Q.c σ),
    L2DefiniteCuspForms (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (cuspidalL2Subspace j hj σ hσ)

  unitIndep : ∀ j, InR D j → UnitIndep (T.Q.Xo j) T.Q.c
  ptNe : ∀ j, InR D j → IntFrNe (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)

structure LawsCore (T : Core D) : Prop extends LawsM T where

  cuspMul : ∀ j, InR D j → CuspMul (T.Q.Xo j) T.Q.c (T.U j)

  latZ : ∀ j, InR D j → FJ.LatZ (T.X₀ j) (WeightFamilies.rho D j)
  cuNe : ∀ j, InR D j → FJ.CuNeF (T.X₀ j) (WeightFamilies.rho D j)
  expo : ∀ j, InR D j → FJ.ExpoMatch (T.X₀ j) T.frI (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Formalism.L2.Pj
