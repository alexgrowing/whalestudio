import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

def CplxEq {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ) {m m' : ℕ}
    (c : Fin m → ℂ) (v : Fin m → V) (c' : Fin m' → ℂ) (v' : Fin m' → V) : Prop :=
  letI := σ.toAlgebra
  (∑ i, c i ⊗ₜ[K] v i : ℂ ⊗[K] V) = ∑ k, c' k ⊗ₜ[K] v' k

def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial

section OneField

variable {K : Type} [Field K] [NumberField K]

section Geo

variable (G : Geo K) (s : Fin G.D → Fin G.N → K) (σ : K →+* ℂ)

def rad (i : Fin G.D) : ℝ := G.normAt σ (s i)

def radSq : ℝ := ∑ i, rad G s σ i ^ 2

def radPow {a : ℕ} (α : MonoDeg (Fin G.D) a) : ℝ := ∏ i, rad G s σ i ^ α.1 i

def degS : ℕ :=
  letI := algebraΓOfHom ((G.ideal s).subschemeι ≫ G.str)
  Module.finrank K Γ((G.ideal s).subscheme, ⊤)

def mulPow {a j l : ℕ} (h : j + a = l) (α : MonoDeg (Fin G.D) a) : G.Sec j →ₗ[K] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) α ((Nat.cast_add j a).symm.trans (congrArg _ h))

variable {G s} (hs : G.IsGood s)

def symOnGr {a j l : ℕ} (h : j + a = l) (V : Submodule K (G.Sec l)) :
    gr (G.ideal s) a V →ₗ[K] SymTarget G.str G.L₂ G.isLB (G.sec s) a j :=
  Submodule.liftQ _ (hs.sym h V) (ker_sym _ _ _ _ _ _ _ _ _ _ V).ge

def ExtensionBound (j : ℕ) : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → G.SecOn s j),
    ∃ (m' : ℕ) (c' : Fin m' → ℂ) (f : Fin m' → H0 G.str (G.adj₂ j) ⊤),
      CplxEq σ c' (fun k => hs.res j (G.mulE j (f k))) c g ∧
        G.sqInt j σ (∑ k, c' k • cval σ (f k)) ≤
          ENNReal.ofReal (34 * cD G.D * radSq G s σ ^ G.D * csq (hs.normOn j) σ c g)

end Geo

section Data

variable (X : Data K) (s : Fin X.D → Fin X.N → K) (σ : K →+* ℂ)

theorem add_sub_D : X.D + (X.T - X.D) = X.T := Nat.add_sub_cancel' ((Nat.le_succ _).trans X.le_T)

theorem sub_add {a : ℕ} (ha : a ≤ X.a₀) : X.T - a + a = X.T :=
  Nat.sub_add_cancel (by have := X.a₀_add; omega)

def spaceP : Submodule K (X.Sec X.T) :=
  ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)

def spaceV : Submodule K (X.Sec X.T) := X.global X.T ⊔ spaceP X s

instance finiteDimensional_spaceP : FiniteDimensional K (spaceP X s) := by
  unfold spaceP
  infer_instance

instance finiteDimensional_spaceV : FiniteDimensional K (spaceV X s) := by
  unfold spaceV
  infer_instance

def liftConstSq (β κ : ℝ) (a : ℕ) : ℝ :=
  κ * β ^ (X.T + X.D + 1) * (34 * cD X.D) * X.Ra a * radSq X.toGeo s σ ^ X.D

def toTop (a : ℕ) : Fil (X.ideal s) a (X.global X.T) →ₗ[K] X.V X.T :=
  Submodule.inclusion (Fil_le.trans (X.global_le X.T le_rfl))

variable {X s} (hs : X.IsGood s)

def LiftBound (β κ : ℝ) {a : ℕ} (ha : a ≤ X.a₀) : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → SymTarget X.str X.L₂ X.isLB (X.sec s) a (X.T - a : ℕ)),
    ∃ (m' : ℕ) (c' : Fin m' → ℂ) (f : Fin m' → Fil (X.ideal s) a (X.global X.T)),
      CplxEq σ c' (fun k => hs.sym (sub_add X ha) (X.global X.T) (f k)) c g ∧
        cnrm (X.nm X.T) σ c' (fun k => toTop X s a (f k)) ≤
          Real.sqrt (liftConstSq X s σ β κ a) *
            Real.sqrt (∑ α, radPow X.toGeo s σ α ^ 2 * csq (hs.normOn (X.T - a)) σ c fun i => g i α)

end Data

end OneField

variable {F : Type} [Field F] [NumberField F] (X : Data F)

structure LocalHyp (β κ : (F →+* ℂ) → ℝ) : Prop where

  totallyComplex : IsTotallyComplex F

  beta_pos : ∀ σ, 0 < β σ

  kappa_pos : ∀ σ, 0 < κ σ

  pos : X.Positivity

  mulStable : X.MulStable

  mulBound : X.MulBound β

  integralBound : X.IntegralBound β κ

variable {X} in

theorem LocalHyp.of_meanHyp {β κ : (F →+* ℂ) → ℝ} (h : X.MeanHyp β κ) : LocalHyp X β κ :=
  ⟨h.totallyComplex, h.beta_pos, h.kappa_pos, h.pos, h.mulStable, h.mulBound, h.integralBound⟩

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

structure IsChosen (s : Fin X.D → Fin X.N → E) : Prop where

  mem : ∀ i, s i ∈ X.latticeOver E

  good : (X.baseChange E).IsGood s

  degree : (degS (X.baseChange E).toGeo s : ℤ) = X.del

variable {E}

structure Ranks {s : Fin X.D → Fin X.N → E} (hs : (X.baseChange E).IsGood s) : Prop where

  bijective : ∀ (a : ℕ) (ha : a ≤ (X.baseChange E).a₀),
    Function.Bijective (symOnGr hs (sub_add (X.baseChange E) ha) (spaceV (X.baseChange E) s))

  finrank_eq : (Module.finrank E (spaceV (X.baseChange E) s) : ℤ) =
    X.R * X.del + Module.finrank E (spaceP (X.baseChange E) s)

  le_d : X.R * X.del ≤ (X.d : ℤ)

  d_pos : 0 < X.d

  z_nonneg : 0 ≤ X.z

  z_le_one : X.z ≤ 1

  one_sub_mul : (1 - X.z) * X.d = X.R * X.del

def Complexify : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (β : (F →+* ℂ) → ℝ), IsTotallyComplex F → (∀ σ, 0 < β σ) →
    X.MulStable → X.MulBound β →
      (∀ σ, X.MulBoundAt σ (β σ)) ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], (X.baseChange E).MulStable

def Lifts : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (β κ : (F →+* ℂ) → ℝ), LocalHyp X β κ →
    ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E) (hs : IsChosen X E s),
      (∀ (τ : E →+* ℂ) (a : ℕ) (ha : a ≤ (X.baseChange E).a₀),
        ExtensionBound τ hs.good (X.T - a) ∧
          LiftBound (X := X.baseChange E) τ hs.good (β (τ.comp (algebraMap F E))) (κ (τ.comp (algebraMap F E))) ha) ∧
      Ranks X hs.good

def Statement : Prop := Complexify ∧ Lifts

theorem Lifts.of_hyp (h : Lifts) (hX : X.Hyp) {s : Fin X.D → Fin X.N → E} (hs : IsChosen X E s) :
    (∀ (τ : E →+* ℂ) (a : ℕ) (ha : a ≤ (X.baseChange E).a₀),
      ExtensionBound τ hs.good (X.T - a) ∧ LiftBound (X := X.baseChange E) τ hs.good X.beta 1 ha) ∧ Ranks X hs.good :=
  h F X _ _ (.of_meanHyp hX.meanHyp) E s hs

example : cD 1 = 4 * Real.pi ∧ cD 2 = 8 * Real.pi ^ 2 := by
  constructor <;> norm_num [cD]

example {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ) (a : K) (v : V) :
    CplxEq σ ![σ a] ![v] ![1] ![a • v] := by
  letI := σ.toAlgebra
  simp only [CplxEq, Fin.sum_univ_one, Matrix.cons_val_zero, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact congrArg (· ⊗ₜ[K] v) ((Algebra.smul_def a (1 : ℂ)).trans (mul_one _)).symm

end GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
