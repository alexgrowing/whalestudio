import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev WA (V W : HSp D) : Type := Matrix (Fin V.rank) (Fin W.rank) (AE D)

scoped instance measWA (V W : HSp D) : MeasurableSpace (WA V W) := borel _

abbrev cA (D : D7) : AE D →+* AE D := sigR (AF D.host.F) D.sp.cm.sig

def cM {m n : ℕ} (x : Matrix (Fin m) (Fin n) (AE D)) : Matrix (Fin m) (Fin n) (AE D) := x.map (cA D)

def mt (V : HSp D) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := (matHom V g).1

def hHom (V W : HSp D) (x y : WA V W) : AE D :=
  if V.rank ≤ W.rank then
    ∑ i, ∑ j, ∑ k, ∑ l, cA D (x i j) * incA D (V.gram k i) * incA D (W.gram j l) * y k l
  else
    ∑ i, ∑ j, ∑ k, ∑ l, cA D (x i j) * incA D (V.gram i k) * incA D (W.gram l j) * y k l

def sympl (V W : HSp D) (x y : WA V W) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hHom V W y x)

def symplH (V W : HSp D) (x y : WA V W) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * sympl V W x y

def actHom (V W : HSp D) (g : GA D V) (h : GA D W) (x : WA V W) : WA V W :=
  if V.rank ≤ W.rank then HMul.hMul (HMul.hMul (cM (mt V g)) x) (mt W h).transpose
  else HMul.hMul (HMul.hMul (mt V g) x) (cM (mt W h)).transpose

def ratW (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : WA V W := γ.map (incA D)

def ratL (V W : HSp D) : AddSubgroup (WA V W) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin V.rank) (n := Fin W.rank)).range

def Heisenberg₂ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w₀ : WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  fun w => ψ (symplH V W w w₀) * f (w + w₀)

structure IsThetaFun (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WA V W → ℂ) : Prop where

  quasi : ∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w

  level : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f
  cont : Continuous f

  smooth : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
    ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

def IsStdChar (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (s : ℤ) : Prop :=
  IsCharAF D.host.F ψ ∧ AllSome (IsInfFam (D := D)) fun θ =>
    ∀ x : Ainf D.host.F, psiInf D.host.F ψ x =
      Complex.exp (2 * Real.pi * Complex.I * s * ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)))

def IsDetRoot (V : HSp D) (g : GA D V) (x : (AE D)ˣ) : Prop :=
  (x : AE D) = ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det *
    sigR (AF D.host.F) D.sp.cm.sig (x : AE D)

def IsPlaceIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  ∃ α : Af D.host.F, ε = pairA D.host.F 0 α ∧ evalV D.host.F v α = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' α = 0

def IsSplitIdem (D : D7) (e : AE D) : Prop :=
  e * e = e ∧ e * cA D e = 0 ∧ ∃ v ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def SuppAt (e : AE D) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, (e + cA D e) * (mt V g - 1) i j = (mt V g - 1) i j

def IsDetAt (e : AE D) (V : HSp D) (g : GA D V) (x : (AE D)ˣ) : Prop :=
  (x : AE D) = e * (mt V g).det + (1 - e)

def splitFac (V W : HSp D) (c c' : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) : Circle :=
  if V.rank ≤ W.rank then (c' x)⁻¹ * c y else c' x * (c y)⁻¹

structure TwRule {X : ThetaX D} (T : ThetaTied D X)
    (om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Prop where
  twW_up : ∀ (V W : HSp D) χ χ' ν, V.rank < W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  twV_up : ∀ (V W : HSp D) χ χ' ν, V.rank < W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = ((T.eChr ν x : Circle) : ℂ) • om V W χ χ' (g, h)
  twW_dn : ∀ (V W : HSp D) χ χ' ν, W.rank < V.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = ((T.eChr ν x : Circle) : ℂ) • om V W χ χ' (g, h)
  twV_dn : ∀ (V W : HSp D) χ χ' ν, W.rank < V.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)

structure WeilTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) where

  ψ : AddChar (AF D.host.F) ℂ
  ψ_std : IsStdChar D ψ (-1)

  evS : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ)
  evS_inj : ∀ V W, Function.Injective (evS V W)
  evS_range : ∀ V W : HSp D, V.rank ≠ W.rank → Set.range (evS V W) = {f | IsThetaFun ψ V W f}

  om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))

  om_heis : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ g h w₀ Φ Φ', evS V W Φ' = Heisenberg₂ ψ V W w₀ (evS V W Φ) →
      evS V W (om V W χ χ' (g, h) Φ') = Heisenberg₂ ψ V W (actHom V W g h w₀) (evS V W (om V W χ χ' (g, h) Φ))

  om_aut : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ, evS V W (om V W χ χ' (γ, γ') Φ) 0 = evS V W Φ 0

  om_cont : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ Φ w, Continuous fun p : GA D V × GA D W => evS V W (om V W χ χ' p Φ) w

  om_unit : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p Φ, ∫ w in 𝓕, ‖evS V W (om V W χ χ' p Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖evS V W Φ w‖ ^ 2 ∂μ

  om_split : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : X.Sch V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', evS V W Φ' = Heisenberg₂ ψ V W u (evS V W Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (om V W χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V W (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ

  om_tw : TwRule T om

  om_swap : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ g h (Φ : X.Sch V W) (Φ' : X.Sch W V), (∀ x : WA V W, evS W V Φ' x.transpose = evS V W Φ x) →
      ∀ x : WA V W, evS W V (om W V χ' χ (h, g) Φ') x.transpose = evS V W (om V W χ χ' (g, h) Φ) x

  th : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → V.SigOK →
    ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (Φ : X.Sch V W) (F : X.cusp V) (h : GA D W),
      T.ev W (X.th V W χ χ' Φ F) h =
        (T.petC V : ℂ) * ∫ g in 𝓕, evS V W (om V W χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

def PhiYupTied {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop :=
  ∀ μ j, j < D.R.m → ∀ x : WA (D.sp.Y (j + 1)) (D.sp.Y j),
    Wl.evS _ _ (X.PhiYup μ j) x.transpose = Wl.evS _ _ (X.PhiY μ j) x

end Formalism.L2.Theta

end
